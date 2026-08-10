import FormalConjectures.Util.ProblemImports

open BigOperators Int Real

def a_fast_loop : ℕ → ℕ → ℕ → ℤ → ℤ
  | 0, _, _, acc => acc
  | m + 1, p3, p2, acc =>
    let p3' := p3 * 3
    let p2' := p2 * 2
    let term : ℤ := if (p3' / p2') % 2 = 0 then -1 else 1
    a_fast_loop m p3' p2' (acc + term)

def a_fast (n : ℕ) : ℤ :=
  a_fast_loop n 1 1 0

lemma a_fast_loop_add (m n : ℕ) (p3 p2 : ℕ) (acc : ℤ) :
  a_fast_loop (m + n) p3 p2 acc = a_fast_loop n (p3 * 3^m) (p2 * 2^m) (a_fast_loop m p3 p2 acc) := by
  induction m generalizing p3 p2 acc with
  | zero =>
    simp [a_fast_loop]
  | succ m ih =>
    have h_add : m + 1 + n = m + n + 1 := by omega
    rw [h_add]
    dsimp [a_fast_loop]
    rw [ih (p3 * 3) (p2 * 2)]
    congr 1
    · have : 3 * 3^m = 3^(m+1) := by ring
      rw [mul_assoc, this]
    · have : 2 * 2^m = 2^(m+1) := by ring
      rw [mul_assoc, this]

lemma a_fast_add (m n : ℕ) :
  a_fast (m + n) = a_fast_loop n (3^m) (2^m) (a_fast m) := by
  dsimp [a_fast]
  rw [a_fast_loop_add]
  simp

set_option maxRecDepth 1000000
set_option exponentiation.threshold 1000000

lemma a_fast_1000 : a_fast 1000 = 102 := by rfl

lemma a_fast_2000 : a_fast 2000 = 96 := by
  have h : a_fast (1000 + 1000) = a_fast_loop 1000 (3^1000) (2^1000) (a_fast 1000) := by
    apply a_fast_add
  rw [h]
  rw [a_fast_1000]
  rfl

lemma a_fast_3000 : a_fast 3000 = 44 := by
  have h : a_fast (2000 + 1000) = a_fast_loop 1000 (3^2000) (2^2000) (a_fast 2000) := by
    apply a_fast_add
  rw [h]
  rw [a_fast_2000]
  rfl

lemma a_fast_4000 : a_fast 4000 = 84 := by
  have h : a_fast (3000 + 1000) = a_fast_loop 1000 (3^3000) (2^3000) (a_fast 3000) := by
    apply a_fast_add
  rw [h]
  rw [a_fast_3000]
  rfl

lemma a_fast_5000 : a_fast 5000 = 72 := by
  have h : a_fast (4000 + 1000) = a_fast_loop 1000 (3^4000) (2^4000) (a_fast 4000) := by
    apply a_fast_add
  rw [h]
  rw [a_fast_4000]
  rfl

lemma a_fast_6000 : a_fast 6000 = 86 := by
  have h : a_fast (5000 + 1000) = a_fast_loop 1000 (3^5000) (2^5000) (a_fast 5000) := by
    apply a_fast_add
  rw [h]
  rw [a_fast_5000]
  rfl

lemma a_fast_7000 : a_fast 7000 = 104 := by
  have h : a_fast (6000 + 1000) = a_fast_loop 1000 (3^6000) (2^6000) (a_fast 6000) := by
    apply a_fast_add
  rw [h]
  rw [a_fast_6000]
  rfl

lemma a_fast_8000 : a_fast 8000 = 118 := by
  have h : a_fast (7000 + 1000) = a_fast_loop 1000 (3^7000) (2^7000) (a_fast 7000) := by
    apply a_fast_add
  rw [h]
  rw [a_fast_7000]
  rfl

lemma a_fast_9000 : a_fast 9000 = 158 := by
  have h : a_fast (8000 + 1000) = a_fast_loop 1000 (3^8000) (2^8000) (a_fast 8000) := by
    apply a_fast_add
  rw [h]
  rw [a_fast_8000]
  rfl

lemma a_fast_10000 : a_fast 10000 = 140 := by
  have h : a_fast (9000 + 1000) = a_fast_loop 1000 (3^9000) (2^9000) (a_fast 9000) := by
    apply a_fast_add
  rw [h]
  rw [a_fast_9000]
  rfl

lemma a_fast_11000 : a_fast 11000 = 148 := by
  have h : a_fast (10000 + 1000) = a_fast_loop 1000 (3^10000) (2^10000) (a_fast 10000) := by
    apply a_fast_add
  rw [h]
  rw [a_fast_10000]
  rfl

lemma a_fast_12000 : a_fast 12000 = 222 := by
  have h : a_fast (11000 + 1000) = a_fast_loop 1000 (3^11000) (2^11000) (a_fast 11000) := by
    apply a_fast_add
  rw [h]
  rw [a_fast_11000]
  rfl

lemma a_fast_13000 : a_fast 13000 = 188 := by
  have h : a_fast (12000 + 1000) = a_fast_loop 1000 (3^12000) (2^12000) (a_fast 12000) := by
    apply a_fast_add
  rw [h]
  rw [a_fast_12000]
  rfl

lemma a_fast_14000 : a_fast 14000 = 192 := by
  have h : a_fast (13000 + 1000) = a_fast_loop 1000 (3^13000) (2^13000) (a_fast 13000) := by
    apply a_fast_add
  rw [h]
  rw [a_fast_13000]
  rfl

lemma a_fast_15000 : a_fast 15000 = 190 := by
  have h : a_fast (14000 + 1000) = a_fast_loop 1000 (3^14000) (2^14000) (a_fast 14000) := by
    apply a_fast_add
  rw [h]
  rw [a_fast_14000]
  rfl

lemma a_fast_16000 : a_fast 16000 = 212 := by
  have h : a_fast (15000 + 1000) = a_fast_loop 1000 (3^15000) (2^15000) (a_fast 15000) := by
    apply a_fast_add
  rw [h]
  rw [a_fast_15000]
  rfl

lemma a_fast_17000 : a_fast 17000 = 214 := by
  have h : a_fast (16000 + 1000) = a_fast_loop 1000 (3^16000) (2^16000) (a_fast 16000) := by
    apply a_fast_add
  rw [h]
  rw [a_fast_16000]
  rfl

lemma a_fast_18000 : a_fast 18000 = 140 := by
  have h : a_fast (17000 + 1000) = a_fast_loop 1000 (3^17000) (2^17000) (a_fast 17000) := by
    apply a_fast_add
  rw [h]
  rw [a_fast_17000]
  rfl

lemma a_fast_19000 : a_fast 19000 = 172 := by
  have h : a_fast (18000 + 1000) = a_fast_loop 1000 (3^18000) (2^18000) (a_fast 18000) := by
    apply a_fast_add
  rw [h]
  rw [a_fast_18000]
  rfl

lemma a_fast_20000 : a_fast 20000 = 222 := by
  have h : a_fast (19000 + 1000) = a_fast_loop 1000 (3^19000) (2^19000) (a_fast 19000) := by
    apply a_fast_add
  rw [h]
  rw [a_fast_19000]
  rfl

lemma a_fast_21000 : a_fast 21000 = 180 := by
  have h : a_fast (20000 + 1000) = a_fast_loop 1000 (3^20000) (2^20000) (a_fast 20000) := by
    apply a_fast_add
  rw [h]
  rw [a_fast_20000]
  rfl

lemma a_fast_22000 : a_fast 22000 = 136 := by
  have h : a_fast (21000 + 1000) = a_fast_loop 1000 (3^21000) (2^21000) (a_fast 21000) := by
    apply a_fast_add
  rw [h]
  rw [a_fast_21000]
  rfl

lemma a_fast_23000 : a_fast 23000 = 178 := by
  have h : a_fast (22000 + 1000) = a_fast_loop 1000 (3^22000) (2^22000) (a_fast 22000) := by
    apply a_fast_add
  rw [h]
  rw [a_fast_22000]
  rfl

lemma a_fast_24000 : a_fast 24000 = 198 := by
  have h : a_fast (23000 + 1000) = a_fast_loop 1000 (3^23000) (2^23000) (a_fast 23000) := by
    apply a_fast_add
  rw [h]
  rw [a_fast_23000]
  rfl

lemma a_fast_25000 : a_fast 25000 = 252 := by
  have h : a_fast (24000 + 1000) = a_fast_loop 1000 (3^24000) (2^24000) (a_fast 24000) := by
    apply a_fast_add
  rw [h]
  rw [a_fast_24000]
  rfl

lemma a_fast_26000 : a_fast 26000 = 280 := by
  have h : a_fast (25000 + 1000) = a_fast_loop 1000 (3^25000) (2^25000) (a_fast 25000) := by
    apply a_fast_add
  rw [h]
  rw [a_fast_25000]
  rfl

lemma a_fast_27000 : a_fast 27000 = 296 := by
  have h : a_fast (26000 + 1000) = a_fast_loop 1000 (3^26000) (2^26000) (a_fast 26000) := by
    apply a_fast_add
  rw [h]
  rw [a_fast_26000]
  rfl

lemma a_fast_28000 : a_fast 28000 = 252 := by
  have h : a_fast (27000 + 1000) = a_fast_loop 1000 (3^27000) (2^27000) (a_fast 27000) := by
    apply a_fast_add
  rw [h]
  rw [a_fast_27000]
  rfl

lemma a_fast_29000 : a_fast 29000 = 228 := by
  have h : a_fast (28000 + 1000) = a_fast_loop 1000 (3^28000) (2^28000) (a_fast 28000) := by
    apply a_fast_add
  rw [h]
  rw [a_fast_28000]
  rfl

lemma a_fast_30000 : a_fast 30000 = 252 := by
  have h : a_fast (29000 + 1000) = a_fast_loop 1000 (3^29000) (2^29000) (a_fast 29000) := by
    apply a_fast_add
  rw [h]
  rw [a_fast_29000]
  rfl

lemma a_fast_31000 : a_fast 31000 = 244 := by
  have h : a_fast (30000 + 1000) = a_fast_loop 1000 (3^30000) (2^30000) (a_fast 30000) := by
    apply a_fast_add
  rw [h]
  rw [a_fast_30000]
  rfl

lemma a_fast_32000 : a_fast 32000 = 250 := by
  have h : a_fast (31000 + 1000) = a_fast_loop 1000 (3^31000) (2^31000) (a_fast 31000) := by
    apply a_fast_add
  rw [h]
  rw [a_fast_31000]
  rfl

lemma a_fast_33000 : a_fast 33000 = 272 := by
  have h : a_fast (32000 + 1000) = a_fast_loop 1000 (3^32000) (2^32000) (a_fast 32000) := by
    apply a_fast_add
  rw [h]
  rw [a_fast_32000]
  rfl

lemma a_fast_34000 : a_fast 34000 = 276 := by
  have h : a_fast (33000 + 1000) = a_fast_loop 1000 (3^33000) (2^33000) (a_fast 33000) := by
    apply a_fast_add
  rw [h]
  rw [a_fast_33000]
  rfl

lemma a_fast_35000 : a_fast 35000 = 264 := by
  have h : a_fast (34000 + 1000) = a_fast_loop 1000 (3^34000) (2^34000) (a_fast 34000) := by
    apply a_fast_add
  rw [h]
  rw [a_fast_34000]
  rfl

lemma a_fast_36000 : a_fast 36000 = 278 := by
  have h : a_fast (35000 + 1000) = a_fast_loop 1000 (3^35000) (2^35000) (a_fast 35000) := by
    apply a_fast_add
  rw [h]
  rw [a_fast_35000]
  rfl

lemma a_fast_37000 : a_fast 37000 = 230 := by
  have h : a_fast (36000 + 1000) = a_fast_loop 1000 (3^36000) (2^36000) (a_fast 36000) := by
    apply a_fast_add
  rw [h]
  rw [a_fast_36000]
  rfl

lemma a_fast_38000 : a_fast 38000 = 228 := by
  have h : a_fast (37000 + 1000) = a_fast_loop 1000 (3^37000) (2^37000) (a_fast 37000) := by
    apply a_fast_add
  rw [h]
  rw [a_fast_37000]
  rfl

lemma a_fast_39000 : a_fast 39000 = 254 := by
  have h : a_fast (38000 + 1000) = a_fast_loop 1000 (3^38000) (2^38000) (a_fast 38000) := by
    apply a_fast_add
  rw [h]
  rw [a_fast_38000]
  rfl

lemma a_fast_40000 : a_fast 40000 = 300 := by
  have h : a_fast (39000 + 1000) = a_fast_loop 1000 (3^39000) (2^39000) (a_fast 39000) := by
    apply a_fast_add
  rw [h]
  rw [a_fast_39000]
  rfl

lemma a_fast_41000 : a_fast 41000 = 326 := by
  have h : a_fast (40000 + 1000) = a_fast_loop 1000 (3^40000) (2^40000) (a_fast 40000) := by
    apply a_fast_add
  rw [h]
  rw [a_fast_40000]
  rfl

lemma a_fast_42000 : a_fast 42000 = 338 := by
  have h : a_fast (41000 + 1000) = a_fast_loop 1000 (3^41000) (2^41000) (a_fast 41000) := by
    apply a_fast_add
  rw [h]
  rw [a_fast_41000]
  rfl

lemma a_fast_43000 : a_fast 43000 = 312 := by
  have h : a_fast (42000 + 1000) = a_fast_loop 1000 (3^42000) (2^42000) (a_fast 42000) := by
    apply a_fast_add
  rw [h]
  rw [a_fast_42000]
  rfl

lemma a_fast_44000 : a_fast 44000 = 260 := by
  have h : a_fast (43000 + 1000) = a_fast_loop 1000 (3^43000) (2^43000) (a_fast 43000) := by
    apply a_fast_add
  rw [h]
  rw [a_fast_43000]
  rfl

lemma a_fast_45000 : a_fast 45000 = 304 := by
  have h : a_fast (44000 + 1000) = a_fast_loop 1000 (3^44000) (2^44000) (a_fast 44000) := by
    apply a_fast_add
  rw [h]
  rw [a_fast_44000]
  rfl

lemma a_fast_46000 : a_fast 46000 = 266 := by
  have h : a_fast (45000 + 1000) = a_fast_loop 1000 (3^45000) (2^45000) (a_fast 45000) := by
    apply a_fast_add
  rw [h]
  rw [a_fast_45000]
  rfl

lemma a_fast_47000 : a_fast 47000 = 266 := by
  have h : a_fast (46000 + 1000) = a_fast_loop 1000 (3^46000) (2^46000) (a_fast 46000) := by
    apply a_fast_add
  rw [h]
  rw [a_fast_46000]
  rfl

lemma a_fast_48000 : a_fast 48000 = 240 := by
  have h : a_fast (47000 + 1000) = a_fast_loop 1000 (3^47000) (2^47000) (a_fast 47000) := by
    apply a_fast_add
  rw [h]
  rw [a_fast_47000]
  rfl

lemma a_fast_49000 : a_fast 49000 = 216 := by
  have h : a_fast (48000 + 1000) = a_fast_loop 1000 (3^48000) (2^48000) (a_fast 48000) := by
    apply a_fast_add
  rw [h]
  rw [a_fast_48000]
  rfl

lemma a_fast_50000 : a_fast 50000 = 176 := by
  have h : a_fast (49000 + 1000) = a_fast_loop 1000 (3^49000) (2^49000) (a_fast 49000) := by
    apply a_fast_add
  rw [h]
  rw [a_fast_49000]
  rfl

lemma a_fast_51000 : a_fast 51000 = 168 := by
  have h : a_fast (50000 + 1000) = a_fast_loop 1000 (3^50000) (2^50000) (a_fast 50000) := by
    apply a_fast_add
  rw [h]
  rw [a_fast_50000]
  rfl

lemma a_fast_52000 : a_fast 52000 = 182 := by
  have h : a_fast (51000 + 1000) = a_fast_loop 1000 (3^51000) (2^51000) (a_fast 51000) := by
    apply a_fast_add
  rw [h]
  rw [a_fast_51000]
  rfl

lemma a_fast_53000 : a_fast 53000 = 164 := by
  have h : a_fast (52000 + 1000) = a_fast_loop 1000 (3^52000) (2^52000) (a_fast 52000) := by
    apply a_fast_add
  rw [h]
  rw [a_fast_52000]
  rfl

lemma a_fast_54000 : a_fast 54000 = 190 := by
  have h : a_fast (53000 + 1000) = a_fast_loop 1000 (3^53000) (2^53000) (a_fast 53000) := by
    apply a_fast_add
  rw [h]
  rw [a_fast_53000]
  rfl

lemma a_fast_55000 : a_fast 55000 = 214 := by
  have h : a_fast (54000 + 1000) = a_fast_loop 1000 (3^54000) (2^54000) (a_fast 54000) := by
    apply a_fast_add
  rw [h]
  rw [a_fast_54000]
  rfl

lemma a_fast_56000 : a_fast 56000 = 230 := by
  have h : a_fast (55000 + 1000) = a_fast_loop 1000 (3^55000) (2^55000) (a_fast 55000) := by
    apply a_fast_add
  rw [h]
  rw [a_fast_55000]
  rfl

lemma a_fast_57000 : a_fast 57000 = 230 := by
  have h : a_fast (56000 + 1000) = a_fast_loop 1000 (3^56000) (2^56000) (a_fast 56000) := by
    apply a_fast_add
  rw [h]
  rw [a_fast_56000]
  rfl

lemma a_fast_58000 : a_fast 58000 = 244 := by
  have h : a_fast (57000 + 1000) = a_fast_loop 1000 (3^57000) (2^57000) (a_fast 57000) := by
    apply a_fast_add
  rw [h]
  rw [a_fast_57000]
  rfl

lemma a_fast_59000 : a_fast 59000 = 228 := by
  have h : a_fast (58000 + 1000) = a_fast_loop 1000 (3^58000) (2^58000) (a_fast 58000) := by
    apply a_fast_add
  rw [h]
  rw [a_fast_58000]
  rfl

lemma a_fast_60000 : a_fast 60000 = 238 := by
  have h : a_fast (59000 + 1000) = a_fast_loop 1000 (3^59000) (2^59000) (a_fast 59000) := by
    apply a_fast_add
  rw [h]
  rw [a_fast_59000]
  rfl

lemma a_fast_61000 : a_fast 61000 = 240 := by
  have h : a_fast (60000 + 1000) = a_fast_loop 1000 (3^60000) (2^60000) (a_fast 60000) := by
    apply a_fast_add
  rw [h]
  rw [a_fast_60000]
  rfl

lemma a_fast_62000 : a_fast 62000 = 288 := by
  have h : a_fast (61000 + 1000) = a_fast_loop 1000 (3^61000) (2^61000) (a_fast 61000) := by
    apply a_fast_add
  rw [h]
  rw [a_fast_61000]
  rfl

lemma a_fast_63000 : a_fast 63000 = 250 := by
  have h : a_fast (62000 + 1000) = a_fast_loop 1000 (3^62000) (2^62000) (a_fast 62000) := by
    apply a_fast_add
  rw [h]
  rw [a_fast_62000]
  rfl

lemma a_fast_64000 : a_fast 64000 = 242 := by
  have h : a_fast (63000 + 1000) = a_fast_loop 1000 (3^63000) (2^63000) (a_fast 63000) := by
    apply a_fast_add
  rw [h]
  rw [a_fast_63000]
  rfl

lemma a_fast_65000 : a_fast 65000 = 258 := by
  have h : a_fast (64000 + 1000) = a_fast_loop 1000 (3^64000) (2^64000) (a_fast 64000) := by
    apply a_fast_add
  rw [h]
  rw [a_fast_64000]
  rfl

lemma a_fast_66000 : a_fast 66000 = 326 := by
  have h : a_fast (65000 + 1000) = a_fast_loop 1000 (3^65000) (2^65000) (a_fast 65000) := by
    apply a_fast_add
  rw [h]
  rw [a_fast_65000]
  rfl

lemma a_fast_67000 : a_fast 67000 = 354 := by
  have h : a_fast (66000 + 1000) = a_fast_loop 1000 (3^66000) (2^66000) (a_fast 66000) := by
    apply a_fast_add
  rw [h]
  rw [a_fast_66000]
  rfl

lemma a_fast_68000 : a_fast 68000 = 330 := by
  have h : a_fast (67000 + 1000) = a_fast_loop 1000 (3^67000) (2^67000) (a_fast 67000) := by
    apply a_fast_add
  rw [h]
  rw [a_fast_67000]
  rfl

lemma a_fast_69000 : a_fast 69000 = 324 := by
  have h : a_fast (68000 + 1000) = a_fast_loop 1000 (3^68000) (2^68000) (a_fast 68000) := by
    apply a_fast_add
  rw [h]
  rw [a_fast_68000]
  rfl

lemma a_fast_70000 : a_fast 70000 = 256 := by
  have h : a_fast (69000 + 1000) = a_fast_loop 1000 (3^69000) (2^69000) (a_fast 69000) := by
    apply a_fast_add
  rw [h]
  rw [a_fast_69000]
  rfl

lemma a_fast_71000 : a_fast 71000 = 278 := by
  have h : a_fast (70000 + 1000) = a_fast_loop 1000 (3^70000) (2^70000) (a_fast 70000) := by
    apply a_fast_add
  rw [h]
  rw [a_fast_70000]
  rfl

lemma a_fast_72000 : a_fast 72000 = 302 := by
  have h : a_fast (71000 + 1000) = a_fast_loop 1000 (3^71000) (2^71000) (a_fast 71000) := by
    apply a_fast_add
  rw [h]
  rw [a_fast_71000]
  rfl

lemma a_fast_73000 : a_fast 73000 = 308 := by
  have h : a_fast (72000 + 1000) = a_fast_loop 1000 (3^72000) (2^72000) (a_fast 72000) := by
    apply a_fast_add
  rw [h]
  rw [a_fast_72000]
  rfl

lemma a_fast_74000 : a_fast 74000 = 348 := by
  have h : a_fast (73000 + 1000) = a_fast_loop 1000 (3^73000) (2^73000) (a_fast 73000) := by
    apply a_fast_add
  rw [h]
  rw [a_fast_73000]
  rfl

lemma a_fast_75000 : a_fast 75000 = 430 := by
  have h : a_fast (74000 + 1000) = a_fast_loop 1000 (3^74000) (2^74000) (a_fast 74000) := by
    apply a_fast_add
  rw [h]
  rw [a_fast_74000]
  rfl

lemma a_fast_76000 : a_fast 76000 = 464 := by
  have h : a_fast (75000 + 1000) = a_fast_loop 1000 (3^75000) (2^75000) (a_fast 75000) := by
    apply a_fast_add
  rw [h]
  rw [a_fast_75000]
  rfl

lemma a_fast_77000 : a_fast 77000 = 442 := by
  have h : a_fast (76000 + 1000) = a_fast_loop 1000 (3^76000) (2^76000) (a_fast 76000) := by
    apply a_fast_add
  rw [h]
  rw [a_fast_76000]
  rfl

lemma a_fast_78000 : a_fast 78000 = 480 := by
  have h : a_fast (77000 + 1000) = a_fast_loop 1000 (3^77000) (2^77000) (a_fast 77000) := by
    apply a_fast_add
  rw [h]
  rw [a_fast_77000]
  rfl

lemma a_fast_79000 : a_fast 79000 = 492 := by
  have h : a_fast (78000 + 1000) = a_fast_loop 1000 (3^78000) (2^78000) (a_fast 78000) := by
    apply a_fast_add
  rw [h]
  rw [a_fast_78000]
  rfl

lemma a_fast_80000 : a_fast 80000 = 472 := by
  have h : a_fast (79000 + 1000) = a_fast_loop 1000 (3^79000) (2^79000) (a_fast 79000) := by
    apply a_fast_add
  rw [h]
  rw [a_fast_79000]
  rfl

lemma a_fast_81000 : a_fast 81000 = 480 := by
  have h : a_fast (80000 + 1000) = a_fast_loop 1000 (3^80000) (2^80000) (a_fast 80000) := by
    apply a_fast_add
  rw [h]
  rw [a_fast_80000]
  rfl

lemma a_fast_82000 : a_fast 82000 = 446 := by
  have h : a_fast (81000 + 1000) = a_fast_loop 1000 (3^81000) (2^81000) (a_fast 81000) := by
    apply a_fast_add
  rw [h]
  rw [a_fast_81000]
  rfl

lemma a_fast_83000 : a_fast 83000 = 466 := by
  have h : a_fast (82000 + 1000) = a_fast_loop 1000 (3^82000) (2^82000) (a_fast 82000) := by
    apply a_fast_add
  rw [h]
  rw [a_fast_82000]
  rfl

lemma a_fast_84000 : a_fast 84000 = 482 := by
  have h : a_fast (83000 + 1000) = a_fast_loop 1000 (3^83000) (2^83000) (a_fast 83000) := by
    apply a_fast_add
  rw [h]
  rw [a_fast_83000]
  rfl

lemma a_fast_85000 : a_fast 85000 = 488 := by
  have h : a_fast (84000 + 1000) = a_fast_loop 1000 (3^84000) (2^84000) (a_fast 84000) := by
    apply a_fast_add
  rw [h]
  rw [a_fast_84000]
  rfl

lemma a_fast_86000 : a_fast 86000 = 470 := by
  have h : a_fast (85000 + 1000) = a_fast_loop 1000 (3^85000) (2^85000) (a_fast 85000) := by
    apply a_fast_add
  rw [h]
  rw [a_fast_85000]
  rfl

lemma a_fast_87000 : a_fast 87000 = 546 := by
  have h : a_fast (86000 + 1000) = a_fast_loop 1000 (3^86000) (2^86000) (a_fast 86000) := by
    apply a_fast_add
  rw [h]
  rw [a_fast_86000]
  rfl

lemma a_fast_88000 : a_fast 88000 = 540 := by
  have h : a_fast (87000 + 1000) = a_fast_loop 1000 (3^87000) (2^87000) (a_fast 87000) := by
    apply a_fast_add
  rw [h]
  rw [a_fast_87000]
  rfl

lemma a_fast_89000 : a_fast 89000 = 532 := by
  have h : a_fast (88000 + 1000) = a_fast_loop 1000 (3^88000) (2^88000) (a_fast 88000) := by
    apply a_fast_add
  rw [h]
  rw [a_fast_88000]
  rfl

lemma a_fast_90000 : a_fast 90000 = 550 := by
  have h : a_fast (89000 + 1000) = a_fast_loop 1000 (3^89000) (2^89000) (a_fast 89000) := by
    apply a_fast_add
  rw [h]
  rw [a_fast_89000]
  rfl

lemma a_fast_91000 : a_fast 91000 = 622 := by
  have h : a_fast (90000 + 1000) = a_fast_loop 1000 (3^90000) (2^90000) (a_fast 90000) := by
    apply a_fast_add
  rw [h]
  rw [a_fast_90000]
  rfl

lemma a_fast_92000 : a_fast 92000 = 624 := by
  have h : a_fast (91000 + 1000) = a_fast_loop 1000 (3^91000) (2^91000) (a_fast 91000) := by
    apply a_fast_add
  rw [h]
  rw [a_fast_91000]
  rfl

lemma a_fast_93000 : a_fast 93000 = 642 := by
  have h : a_fast (92000 + 1000) = a_fast_loop 1000 (3^92000) (2^92000) (a_fast 92000) := by
    apply a_fast_add
  rw [h]
  rw [a_fast_92000]
  rfl

lemma a_fast_94000 : a_fast 94000 = 614 := by
  have h : a_fast (93000 + 1000) = a_fast_loop 1000 (3^93000) (2^93000) (a_fast 93000) := by
    apply a_fast_add
  rw [h]
  rw [a_fast_93000]
  rfl

lemma a_fast_95000 : a_fast 95000 = 624 := by
  have h : a_fast (94000 + 1000) = a_fast_loop 1000 (3^94000) (2^94000) (a_fast 94000) := by
    apply a_fast_add
  rw [h]
  rw [a_fast_94000]
  rfl

lemma a_fast_96000 : a_fast 96000 = 562 := by
  have h : a_fast (95000 + 1000) = a_fast_loop 1000 (3^95000) (2^95000) (a_fast 95000) := by
    apply a_fast_add
  rw [h]
  rw [a_fast_95000]
  rfl

lemma a_fast_97000 : a_fast 97000 = 560 := by
  have h : a_fast (96000 + 1000) = a_fast_loop 1000 (3^96000) (2^96000) (a_fast 96000) := by
    apply a_fast_add
  rw [h]
  rw [a_fast_96000]
  rfl

lemma a_fast_98000 : a_fast 98000 = 572 := by
  have h : a_fast (97000 + 1000) = a_fast_loop 1000 (3^97000) (2^97000) (a_fast 97000) := by
    apply a_fast_add
  rw [h]
  rw [a_fast_97000]
  rfl

lemma a_fast_99000 : a_fast 99000 = 578 := by
  have h : a_fast (98000 + 1000) = a_fast_loop 1000 (3^98000) (2^98000) (a_fast 98000) := by
    apply a_fast_add
  rw [h]
  rw [a_fast_98000]
  rfl

lemma a_fast_100000 : a_fast 100000 = 526 := by
  have h : a_fast (99000 + 1000) = a_fast_loop 1000 (3^99000) (2^99000) (a_fast 99000) := by
    apply a_fast_add
  rw [h]
  rw [a_fast_99000]
  rfl

lemma a_fast_101000 : a_fast 101000 = 534 := by
  have h : a_fast (100000 + 1000) = a_fast_loop 1000 (3^100000) (2^100000) (a_fast 100000) := by
    apply a_fast_add
  rw [h]
  rw [a_fast_100000]
  rfl

lemma a_fast_102000 : a_fast 102000 = 540 := by
  have h : a_fast (101000 + 1000) = a_fast_loop 1000 (3^101000) (2^101000) (a_fast 101000) := by
    apply a_fast_add
  rw [h]
  rw [a_fast_101000]
  rfl

lemma a_fast_103000 : a_fast 103000 = 594 := by
  have h : a_fast (102000 + 1000) = a_fast_loop 1000 (3^102000) (2^102000) (a_fast 102000) := by
    apply a_fast_add
  rw [h]
  rw [a_fast_102000]
  rfl

lemma a_fast_104000 : a_fast 104000 = 578 := by
  have h : a_fast (103000 + 1000) = a_fast_loop 1000 (3^103000) (2^103000) (a_fast 103000) := by
    apply a_fast_add
  rw [h]
  rw [a_fast_103000]
  rfl

lemma a_fast_105000 : a_fast 105000 = 566 := by
  have h : a_fast (104000 + 1000) = a_fast_loop 1000 (3^104000) (2^104000) (a_fast 104000) := by
    apply a_fast_add
  rw [h]
  rw [a_fast_104000]
  rfl

lemma a_fast_106000 : a_fast 106000 = 570 := by
  have h : a_fast (105000 + 1000) = a_fast_loop 1000 (3^105000) (2^105000) (a_fast 105000) := by
    apply a_fast_add
  rw [h]
  rw [a_fast_105000]
  rfl

lemma a_fast_107000 : a_fast 107000 = 554 := by
  have h : a_fast (106000 + 1000) = a_fast_loop 1000 (3^106000) (2^106000) (a_fast 106000) := by
    apply a_fast_add
  rw [h]
  rw [a_fast_106000]
  rfl

lemma a_fast_108000 : a_fast 108000 = 578 := by
  have h : a_fast (107000 + 1000) = a_fast_loop 1000 (3^107000) (2^107000) (a_fast 107000) := by
    apply a_fast_add
  rw [h]
  rw [a_fast_107000]
  rfl

lemma a_fast_109000 : a_fast 109000 = 546 := by
  have h : a_fast (108000 + 1000) = a_fast_loop 1000 (3^108000) (2^108000) (a_fast 108000) := by
    apply a_fast_add
  rw [h]
  rw [a_fast_108000]
  rfl

lemma a_fast_110000 : a_fast 110000 = 500 := by
  have h : a_fast (109000 + 1000) = a_fast_loop 1000 (3^109000) (2^109000) (a_fast 109000) := by
    apply a_fast_add
  rw [h]
  rw [a_fast_109000]
  rfl

lemma a_fast_111000 : a_fast 111000 = 476 := by
  have h : a_fast (110000 + 1000) = a_fast_loop 1000 (3^110000) (2^110000) (a_fast 110000) := by
    apply a_fast_add
  rw [h]
  rw [a_fast_110000]
  rfl

lemma a_fast_112000 : a_fast 112000 = 476 := by
  have h : a_fast (111000 + 1000) = a_fast_loop 1000 (3^111000) (2^111000) (a_fast 111000) := by
    apply a_fast_add
  rw [h]
  rw [a_fast_111000]
  rfl

lemma a_fast_113000 : a_fast 113000 = 518 := by
  have h : a_fast (112000 + 1000) = a_fast_loop 1000 (3^112000) (2^112000) (a_fast 112000) := by
    apply a_fast_add
  rw [h]
  rw [a_fast_112000]
  rfl

lemma a_fast_114000 : a_fast 114000 = 548 := by
  have h : a_fast (113000 + 1000) = a_fast_loop 1000 (3^113000) (2^113000) (a_fast 113000) := by
    apply a_fast_add
  rw [h]
  rw [a_fast_113000]
  rfl

lemma a_fast_115000 : a_fast 115000 = 492 := by
  have h : a_fast (114000 + 1000) = a_fast_loop 1000 (3^114000) (2^114000) (a_fast 114000) := by
    apply a_fast_add
  rw [h]
  rw [a_fast_114000]
  rfl

lemma a_fast_116000 : a_fast 116000 = 500 := by
  have h : a_fast (115000 + 1000) = a_fast_loop 1000 (3^115000) (2^115000) (a_fast 115000) := by
    apply a_fast_add
  rw [h]
  rw [a_fast_115000]
  rfl

lemma a_fast_117000 : a_fast 117000 = 454 := by
  have h : a_fast (116000 + 1000) = a_fast_loop 1000 (3^116000) (2^116000) (a_fast 116000) := by
    apply a_fast_add
  rw [h]
  rw [a_fast_116000]
  rfl

lemma a_fast_118000 : a_fast 118000 = 480 := by
  have h : a_fast (117000 + 1000) = a_fast_loop 1000 (3^117000) (2^117000) (a_fast 117000) := by
    apply a_fast_add
  rw [h]
  rw [a_fast_117000]
  rfl

lemma a_fast_119000 : a_fast 119000 = 472 := by
  have h : a_fast (118000 + 1000) = a_fast_loop 1000 (3^118000) (2^118000) (a_fast 118000) := by
    apply a_fast_add
  rw [h]
  rw [a_fast_118000]
  rfl

lemma a_fast_120000 : a_fast 120000 = 432 := by
  have h : a_fast (119000 + 1000) = a_fast_loop 1000 (3^119000) (2^119000) (a_fast 119000) := by
    apply a_fast_add
  rw [h]
  rw [a_fast_119000]
  rfl

lemma a_fast_121000 : a_fast 121000 = 442 := by
  have h : a_fast (120000 + 1000) = a_fast_loop 1000 (3^120000) (2^120000) (a_fast 120000) := by
    apply a_fast_add
  rw [h]
  rw [a_fast_120000]
  rfl

lemma a_fast_122000 : a_fast 122000 = 424 := by
  have h : a_fast (121000 + 1000) = a_fast_loop 1000 (3^121000) (2^121000) (a_fast 121000) := by
    apply a_fast_add
  rw [h]
  rw [a_fast_121000]
  rfl

lemma a_fast_123000 : a_fast 123000 = 376 := by
  have h : a_fast (122000 + 1000) = a_fast_loop 1000 (3^122000) (2^122000) (a_fast 122000) := by
    apply a_fast_add
  rw [h]
  rw [a_fast_122000]
  rfl

lemma a_fast_124000 : a_fast 124000 = 396 := by
  have h : a_fast (123000 + 1000) = a_fast_loop 1000 (3^123000) (2^123000) (a_fast 123000) := by
    apply a_fast_add
  rw [h]
  rw [a_fast_123000]
  rfl

lemma a_fast_125000 : a_fast 125000 = 386 := by
  have h : a_fast (124000 + 1000) = a_fast_loop 1000 (3^124000) (2^124000) (a_fast 124000) := by
    apply a_fast_add
  rw [h]
  rw [a_fast_124000]
  rfl

lemma a_fast_126000 : a_fast 126000 = 364 := by
  have h : a_fast (125000 + 1000) = a_fast_loop 1000 (3^125000) (2^125000) (a_fast 125000) := by
    apply a_fast_add
  rw [h]
  rw [a_fast_125000]
  rfl

lemma a_fast_127000 : a_fast 127000 = 316 := by
  have h : a_fast (126000 + 1000) = a_fast_loop 1000 (3^126000) (2^126000) (a_fast 126000) := by
    apply a_fast_add
  rw [h]
  rw [a_fast_126000]
  rfl

lemma a_fast_128000 : a_fast 128000 = 340 := by
  have h : a_fast (127000 + 1000) = a_fast_loop 1000 (3^127000) (2^127000) (a_fast 127000) := by
    apply a_fast_add
  rw [h]
  rw [a_fast_127000]
  rfl

lemma a_fast_129000 : a_fast 129000 = 358 := by
  have h : a_fast (128000 + 1000) = a_fast_loop 1000 (3^128000) (2^128000) (a_fast 128000) := by
    apply a_fast_add
  rw [h]
  rw [a_fast_128000]
  rfl

lemma a_fast_130000 : a_fast 130000 = 366 := by
  have h : a_fast (129000 + 1000) = a_fast_loop 1000 (3^129000) (2^129000) (a_fast 129000) := by
    apply a_fast_add
  rw [h]
  rw [a_fast_129000]
  rfl

lemma a_fast_131000 : a_fast 131000 = 372 := by
  have h : a_fast (130000 + 1000) = a_fast_loop 1000 (3^130000) (2^130000) (a_fast 130000) := by
    apply a_fast_add
  rw [h]
  rw [a_fast_130000]
  rfl

lemma a_fast_132000 : a_fast 132000 = 384 := by
  have h : a_fast (131000 + 1000) = a_fast_loop 1000 (3^131000) (2^131000) (a_fast 131000) := by
    apply a_fast_add
  rw [h]
  rw [a_fast_131000]
  rfl

lemma a_fast_133000 : a_fast 133000 = 410 := by
  have h : a_fast (132000 + 1000) = a_fast_loop 1000 (3^132000) (2^132000) (a_fast 132000) := by
    apply a_fast_add
  rw [h]
  rw [a_fast_132000]
  rfl

lemma a_fast_134000 : a_fast 134000 = 412 := by
  have h : a_fast (133000 + 1000) = a_fast_loop 1000 (3^133000) (2^133000) (a_fast 133000) := by
    apply a_fast_add
  rw [h]
  rw [a_fast_133000]
  rfl

lemma a_fast_135000 : a_fast 135000 = 398 := by
  have h : a_fast (134000 + 1000) = a_fast_loop 1000 (3^134000) (2^134000) (a_fast 134000) := by
    apply a_fast_add
  rw [h]
  rw [a_fast_134000]
  rfl

lemma a_fast_136000 : a_fast 136000 = 390 := by
  have h : a_fast (135000 + 1000) = a_fast_loop 1000 (3^135000) (2^135000) (a_fast 135000) := by
    apply a_fast_add
  rw [h]
  rw [a_fast_135000]
  rfl

lemma a_fast_137000 : a_fast 137000 = 436 := by
  have h : a_fast (136000 + 1000) = a_fast_loop 1000 (3^136000) (2^136000) (a_fast 136000) := by
    apply a_fast_add
  rw [h]
  rw [a_fast_136000]
  rfl

lemma a_fast_138000 : a_fast 138000 = 470 := by
  have h : a_fast (137000 + 1000) = a_fast_loop 1000 (3^137000) (2^137000) (a_fast 137000) := by
    apply a_fast_add
  rw [h]
  rw [a_fast_137000]
  rfl

lemma a_fast_139000 : a_fast 139000 = 482 := by
  have h : a_fast (138000 + 1000) = a_fast_loop 1000 (3^138000) (2^138000) (a_fast 138000) := by
    apply a_fast_add
  rw [h]
  rw [a_fast_138000]
  rfl

lemma a_fast_140000 : a_fast 140000 = 542 := by
  have h : a_fast (139000 + 1000) = a_fast_loop 1000 (3^139000) (2^139000) (a_fast 139000) := by
    apply a_fast_add
  rw [h]
  rw [a_fast_139000]
  rfl

lemma a_fast_141000 : a_fast 141000 = 546 := by
  have h : a_fast (140000 + 1000) = a_fast_loop 1000 (3^140000) (2^140000) (a_fast 140000) := by
    apply a_fast_add
  rw [h]
  rw [a_fast_140000]
  rfl

lemma a_fast_142000 : a_fast 142000 = 546 := by
  have h : a_fast (141000 + 1000) = a_fast_loop 1000 (3^141000) (2^141000) (a_fast 141000) := by
    apply a_fast_add
  rw [h]
  rw [a_fast_141000]
  rfl

lemma a_fast_143000 : a_fast 143000 = 576 := by
  have h : a_fast (142000 + 1000) = a_fast_loop 1000 (3^142000) (2^142000) (a_fast 142000) := by
    apply a_fast_add
  rw [h]
  rw [a_fast_142000]
  rfl

lemma a_fast_144000 : a_fast 144000 = 576 := by
  have h : a_fast (143000 + 1000) = a_fast_loop 1000 (3^143000) (2^143000) (a_fast 143000) := by
    apply a_fast_add
  rw [h]
  rw [a_fast_143000]
  rfl

lemma a_fast_145000 : a_fast 145000 = 566 := by
  have h : a_fast (144000 + 1000) = a_fast_loop 1000 (3^144000) (2^144000) (a_fast 144000) := by
    apply a_fast_add
  rw [h]
  rw [a_fast_144000]
  rfl

lemma a_fast_146000 : a_fast 146000 = 562 := by
  have h : a_fast (145000 + 1000) = a_fast_loop 1000 (3^145000) (2^145000) (a_fast 145000) := by
    apply a_fast_add
  rw [h]
  rw [a_fast_145000]
  rfl

lemma a_fast_147000 : a_fast 147000 = 578 := by
  have h : a_fast (146000 + 1000) = a_fast_loop 1000 (3^146000) (2^146000) (a_fast 146000) := by
    apply a_fast_add
  rw [h]
  rw [a_fast_146000]
  rfl

lemma a_fast_148000 : a_fast 148000 = 558 := by
  have h : a_fast (147000 + 1000) = a_fast_loop 1000 (3^147000) (2^147000) (a_fast 147000) := by
    apply a_fast_add
  rw [h]
  rw [a_fast_147000]
  rfl

lemma a_fast_149000 : a_fast 149000 = 552 := by
  have h : a_fast (148000 + 1000) = a_fast_loop 1000 (3^148000) (2^148000) (a_fast 148000) := by
    apply a_fast_add
  rw [h]
  rw [a_fast_148000]
  rfl

lemma a_fast_150000 : a_fast 150000 = 508 := by
  have h : a_fast (149000 + 1000) = a_fast_loop 1000 (3^149000) (2^149000) (a_fast 149000) := by
    apply a_fast_add
  rw [h]
  rw [a_fast_149000]
  rfl

lemma a_fast_151000 : a_fast 151000 = 512 := by
  have h : a_fast (150000 + 1000) = a_fast_loop 1000 (3^150000) (2^150000) (a_fast 150000) := by
    apply a_fast_add
  rw [h]
  rw [a_fast_150000]
  rfl

lemma a_fast_152000 : a_fast 152000 = 466 := by
  have h : a_fast (151000 + 1000) = a_fast_loop 1000 (3^151000) (2^151000) (a_fast 151000) := by
    apply a_fast_add
  rw [h]
  rw [a_fast_151000]
  rfl

lemma a_fast_153000 : a_fast 153000 = 492 := by
  have h : a_fast (152000 + 1000) = a_fast_loop 1000 (3^152000) (2^152000) (a_fast 152000) := by
    apply a_fast_add
  rw [h]
  rw [a_fast_152000]
  rfl

lemma a_fast_154000 : a_fast 154000 = 528 := by
  have h : a_fast (153000 + 1000) = a_fast_loop 1000 (3^153000) (2^153000) (a_fast 153000) := by
    apply a_fast_add
  rw [h]
  rw [a_fast_153000]
  rfl

lemma a_fast_155000 : a_fast 155000 = 514 := by
  have h : a_fast (154000 + 1000) = a_fast_loop 1000 (3^154000) (2^154000) (a_fast 154000) := by
    apply a_fast_add
  rw [h]
  rw [a_fast_154000]
  rfl

lemma a_fast_156000 : a_fast 156000 = 558 := by
  have h : a_fast (155000 + 1000) = a_fast_loop 1000 (3^155000) (2^155000) (a_fast 155000) := by
    apply a_fast_add
  rw [h]
  rw [a_fast_155000]
  rfl

lemma a_fast_157000 : a_fast 157000 = 556 := by
  have h : a_fast (156000 + 1000) = a_fast_loop 1000 (3^156000) (2^156000) (a_fast 156000) := by
    apply a_fast_add
  rw [h]
  rw [a_fast_156000]
  rfl

lemma a_fast_158000 : a_fast 158000 = 542 := by
  have h : a_fast (157000 + 1000) = a_fast_loop 1000 (3^157000) (2^157000) (a_fast 157000) := by
    apply a_fast_add
  rw [h]
  rw [a_fast_157000]
  rfl

lemma a_fast_159000 : a_fast 159000 = 584 := by
  have h : a_fast (158000 + 1000) = a_fast_loop 1000 (3^158000) (2^158000) (a_fast 158000) := by
    apply a_fast_add
  rw [h]
  rw [a_fast_158000]
  rfl

lemma a_fast_160000 : a_fast 160000 = 590 := by
  have h : a_fast (159000 + 1000) = a_fast_loop 1000 (3^159000) (2^159000) (a_fast 159000) := by
    apply a_fast_add
  rw [h]
  rw [a_fast_159000]
  rfl

lemma a_fast_161000 : a_fast 161000 = 542 := by
  have h : a_fast (160000 + 1000) = a_fast_loop 1000 (3^160000) (2^160000) (a_fast 160000) := by
    apply a_fast_add
  rw [h]
  rw [a_fast_160000]
  rfl

lemma a_fast_162000 : a_fast 162000 = 594 := by
  have h : a_fast (161000 + 1000) = a_fast_loop 1000 (3^161000) (2^161000) (a_fast 161000) := by
    apply a_fast_add
  rw [h]
  rw [a_fast_161000]
  rfl

lemma a_fast_163000 : a_fast 163000 = 602 := by
  have h : a_fast (162000 + 1000) = a_fast_loop 1000 (3^162000) (2^162000) (a_fast 162000) := by
    apply a_fast_add
  rw [h]
  rw [a_fast_162000]
  rfl

lemma a_fast_164000 : a_fast 164000 = 596 := by
  have h : a_fast (163000 + 1000) = a_fast_loop 1000 (3^163000) (2^163000) (a_fast 163000) := by
    apply a_fast_add
  rw [h]
  rw [a_fast_163000]
  rfl

lemma a_fast_165000 : a_fast 165000 = 634 := by
  have h : a_fast (164000 + 1000) = a_fast_loop 1000 (3^164000) (2^164000) (a_fast 164000) := by
    apply a_fast_add
  rw [h]
  rw [a_fast_164000]
  rfl

lemma a_fast_166000 : a_fast 166000 = 658 := by
  have h : a_fast (165000 + 1000) = a_fast_loop 1000 (3^165000) (2^165000) (a_fast 165000) := by
    apply a_fast_add
  rw [h]
  rw [a_fast_165000]
  rfl

lemma a_fast_167000 : a_fast 167000 = 678 := by
  have h : a_fast (166000 + 1000) = a_fast_loop 1000 (3^166000) (2^166000) (a_fast 166000) := by
    apply a_fast_add
  rw [h]
  rw [a_fast_166000]
  rfl

lemma a_fast_168000 : a_fast 168000 = 656 := by
  have h : a_fast (167000 + 1000) = a_fast_loop 1000 (3^167000) (2^167000) (a_fast 167000) := by
    apply a_fast_add
  rw [h]
  rw [a_fast_167000]
  rfl

lemma a_fast_169000 : a_fast 169000 = 666 := by
  have h : a_fast (168000 + 1000) = a_fast_loop 1000 (3^168000) (2^168000) (a_fast 168000) := by
    apply a_fast_add
  rw [h]
  rw [a_fast_168000]
  rfl

lemma a_fast_170000 : a_fast 170000 = 642 := by
  have h : a_fast (169000 + 1000) = a_fast_loop 1000 (3^169000) (2^169000) (a_fast 169000) := by
    apply a_fast_add
  rw [h]
  rw [a_fast_169000]
  rfl

lemma a_fast_171000 : a_fast 171000 = 654 := by
  have h : a_fast (170000 + 1000) = a_fast_loop 1000 (3^170000) (2^170000) (a_fast 170000) := by
    apply a_fast_add
  rw [h]
  rw [a_fast_170000]
  rfl

lemma a_fast_172000 : a_fast 172000 = 638 := by
  have h : a_fast (171000 + 1000) = a_fast_loop 1000 (3^171000) (2^171000) (a_fast 171000) := by
    apply a_fast_add
  rw [h]
  rw [a_fast_171000]
  rfl

lemma a_fast_173000 : a_fast 173000 = 658 := by
  have h : a_fast (172000 + 1000) = a_fast_loop 1000 (3^172000) (2^172000) (a_fast 172000) := by
    apply a_fast_add
  rw [h]
  rw [a_fast_172000]
  rfl

lemma a_fast_174000 : a_fast 174000 = 684 := by
  have h : a_fast (173000 + 1000) = a_fast_loop 1000 (3^173000) (2^173000) (a_fast 173000) := by
    apply a_fast_add
  rw [h]
  rw [a_fast_173000]
  rfl

lemma a_fast_175000 : a_fast 175000 = 652 := by
  have h : a_fast (174000 + 1000) = a_fast_loop 1000 (3^174000) (2^174000) (a_fast 174000) := by
    apply a_fast_add
  rw [h]
  rw [a_fast_174000]
  rfl

lemma a_fast_176000 : a_fast 176000 = 654 := by
  have h : a_fast (175000 + 1000) = a_fast_loop 1000 (3^175000) (2^175000) (a_fast 175000) := by
    apply a_fast_add
  rw [h]
  rw [a_fast_175000]
  rfl

lemma a_fast_177000 : a_fast 177000 = 638 := by
  have h : a_fast (176000 + 1000) = a_fast_loop 1000 (3^176000) (2^176000) (a_fast 176000) := by
    apply a_fast_add
  rw [h]
  rw [a_fast_176000]
  rfl

lemma a_fast_178000 : a_fast 178000 = 616 := by
  have h : a_fast (177000 + 1000) = a_fast_loop 1000 (3^177000) (2^177000) (a_fast 177000) := by
    apply a_fast_add
  rw [h]
  rw [a_fast_177000]
  rfl

lemma a_fast_179000 : a_fast 179000 = 630 := by
  have h : a_fast (178000 + 1000) = a_fast_loop 1000 (3^178000) (2^178000) (a_fast 178000) := by
    apply a_fast_add
  rw [h]
  rw [a_fast_178000]
  rfl

lemma a_fast_180000 : a_fast 180000 = 620 := by
  have h : a_fast (179000 + 1000) = a_fast_loop 1000 (3^179000) (2^179000) (a_fast 179000) := by
    apply a_fast_add
  rw [h]
  rw [a_fast_179000]
  rfl

lemma a_fast_181000 : a_fast 181000 = 632 := by
  have h : a_fast (180000 + 1000) = a_fast_loop 1000 (3^180000) (2^180000) (a_fast 180000) := by
    apply a_fast_add
  rw [h]
  rw [a_fast_180000]
  rfl

lemma a_fast_182000 : a_fast 182000 = 610 := by
  have h : a_fast (181000 + 1000) = a_fast_loop 1000 (3^181000) (2^181000) (a_fast 181000) := by
    apply a_fast_add
  rw [h]
  rw [a_fast_181000]
  rfl

lemma a_fast_183000 : a_fast 183000 = 612 := by
  have h : a_fast (182000 + 1000) = a_fast_loop 1000 (3^182000) (2^182000) (a_fast 182000) := by
    apply a_fast_add
  rw [h]
  rw [a_fast_182000]
  rfl

lemma a_fast_184000 : a_fast 184000 = 540 := by
  have h : a_fast (183000 + 1000) = a_fast_loop 1000 (3^183000) (2^183000) (a_fast 183000) := by
    apply a_fast_add
  rw [h]
  rw [a_fast_183000]
  rfl

lemma a_fast_185000 : a_fast 185000 = 586 := by
  have h : a_fast (184000 + 1000) = a_fast_loop 1000 (3^184000) (2^184000) (a_fast 184000) := by
    apply a_fast_add
  rw [h]
  rw [a_fast_184000]
  rfl

lemma a_fast_186000 : a_fast 186000 = 538 := by
  have h : a_fast (185000 + 1000) = a_fast_loop 1000 (3^185000) (2^185000) (a_fast 185000) := by
    apply a_fast_add
  rw [h]
  rw [a_fast_185000]
  rfl

lemma a_fast_187000 : a_fast 187000 = 518 := by
  have h : a_fast (186000 + 1000) = a_fast_loop 1000 (3^186000) (2^186000) (a_fast 186000) := by
    apply a_fast_add
  rw [h]
  rw [a_fast_186000]
  rfl

lemma a_fast_188000 : a_fast 188000 = 516 := by
  have h : a_fast (187000 + 1000) = a_fast_loop 1000 (3^187000) (2^187000) (a_fast 187000) := by
    apply a_fast_add
  rw [h]
  rw [a_fast_187000]
  rfl

lemma a_fast_189000 : a_fast 189000 = 482 := by
  have h : a_fast (188000 + 1000) = a_fast_loop 1000 (3^188000) (2^188000) (a_fast 188000) := by
    apply a_fast_add
  rw [h]
  rw [a_fast_188000]
  rfl

lemma a_fast_190000 : a_fast 190000 = 502 := by
  have h : a_fast (189000 + 1000) = a_fast_loop 1000 (3^189000) (2^189000) (a_fast 189000) := by
    apply a_fast_add
  rw [h]
  rw [a_fast_189000]
  rfl

lemma a_fast_191000 : a_fast 191000 = 460 := by
  have h : a_fast (190000 + 1000) = a_fast_loop 1000 (3^190000) (2^190000) (a_fast 190000) := by
    apply a_fast_add
  rw [h]
  rw [a_fast_190000]
  rfl

lemma a_fast_192000 : a_fast 192000 = 462 := by
  have h : a_fast (191000 + 1000) = a_fast_loop 1000 (3^191000) (2^191000) (a_fast 191000) := by
    apply a_fast_add
  rw [h]
  rw [a_fast_191000]
  rfl

lemma a_fast_193000 : a_fast 193000 = 442 := by
  have h : a_fast (192000 + 1000) = a_fast_loop 1000 (3^192000) (2^192000) (a_fast 192000) := by
    apply a_fast_add
  rw [h]
  rw [a_fast_192000]
  rfl

lemma a_fast_194000 : a_fast 194000 = 482 := by
  have h : a_fast (193000 + 1000) = a_fast_loop 1000 (3^193000) (2^193000) (a_fast 193000) := by
    apply a_fast_add
  rw [h]
  rw [a_fast_193000]
  rfl

lemma a_fast_195000 : a_fast 195000 = 468 := by
  have h : a_fast (194000 + 1000) = a_fast_loop 1000 (3^194000) (2^194000) (a_fast 194000) := by
    apply a_fast_add
  rw [h]
  rw [a_fast_194000]
  rfl

lemma a_fast_196000 : a_fast 196000 = 456 := by
  have h : a_fast (195000 + 1000) = a_fast_loop 1000 (3^195000) (2^195000) (a_fast 195000) := by
    apply a_fast_add
  rw [h]
  rw [a_fast_195000]
  rfl

lemma a_fast_197000 : a_fast 197000 = 486 := by
  have h : a_fast (196000 + 1000) = a_fast_loop 1000 (3^196000) (2^196000) (a_fast 196000) := by
    apply a_fast_add
  rw [h]
  rw [a_fast_196000]
  rfl

lemma a_fast_198000 : a_fast 198000 = 488 := by
  have h : a_fast (197000 + 1000) = a_fast_loop 1000 (3^197000) (2^197000) (a_fast 197000) := by
    apply a_fast_add
  rw [h]
  rw [a_fast_197000]
  rfl

lemma a_fast_199000 : a_fast 199000 = 538 := by
  have h : a_fast (198000 + 1000) = a_fast_loop 1000 (3^198000) (2^198000) (a_fast 198000) := by
    apply a_fast_add
  rw [h]
  rw [a_fast_198000]
  rfl

lemma a_fast_200000 : a_fast 200000 = 554 := by
  have h : a_fast (199000 + 1000) = a_fast_loop 1000 (3^199000) (2^199000) (a_fast 199000) := by
    apply a_fast_add
  rw [h]
  rw [a_fast_199000]
  rfl

lemma a_fast_201000 : a_fast 201000 = 540 := by
  have h : a_fast (200000 + 1000) = a_fast_loop 1000 (3^200000) (2^200000) (a_fast 200000) := by
    apply a_fast_add
  rw [h]
  rw [a_fast_200000]
  rfl

lemma a_fast_202000 : a_fast 202000 = 546 := by
  have h : a_fast (201000 + 1000) = a_fast_loop 1000 (3^201000) (2^201000) (a_fast 201000) := by
    apply a_fast_add
  rw [h]
  rw [a_fast_201000]
  rfl

lemma a_fast_203000 : a_fast 203000 = 540 := by
  have h : a_fast (202000 + 1000) = a_fast_loop 1000 (3^202000) (2^202000) (a_fast 202000) := by
    apply a_fast_add
  rw [h]
  rw [a_fast_202000]
  rfl

lemma a_fast_204000 : a_fast 204000 = 544 := by
  have h : a_fast (203000 + 1000) = a_fast_loop 1000 (3^203000) (2^203000) (a_fast 203000) := by
    apply a_fast_add
  rw [h]
  rw [a_fast_203000]
  rfl

lemma a_fast_205000 : a_fast 205000 = 494 := by
  have h : a_fast (204000 + 1000) = a_fast_loop 1000 (3^204000) (2^204000) (a_fast 204000) := by
    apply a_fast_add
  rw [h]
  rw [a_fast_204000]
  rfl

lemma a_fast_206000 : a_fast 206000 = 494 := by
  have h : a_fast (205000 + 1000) = a_fast_loop 1000 (3^205000) (2^205000) (a_fast 205000) := by
    apply a_fast_add
  rw [h]
  rw [a_fast_205000]
  rfl

lemma a_fast_207000 : a_fast 207000 = 472 := by
  have h : a_fast (206000 + 1000) = a_fast_loop 1000 (3^206000) (2^206000) (a_fast 206000) := by
    apply a_fast_add
  rw [h]
  rw [a_fast_206000]
  rfl

lemma a_fast_208000 : a_fast 208000 = 490 := by
  have h : a_fast (207000 + 1000) = a_fast_loop 1000 (3^207000) (2^207000) (a_fast 207000) := by
    apply a_fast_add
  rw [h]
  rw [a_fast_207000]
  rfl

lemma a_fast_209000 : a_fast 209000 = 470 := by
  have h : a_fast (208000 + 1000) = a_fast_loop 1000 (3^208000) (2^208000) (a_fast 208000) := by
    apply a_fast_add
  rw [h]
  rw [a_fast_208000]
  rfl

lemma a_fast_210000 : a_fast 210000 = 394 := by
  have h : a_fast (209000 + 1000) = a_fast_loop 1000 (3^209000) (2^209000) (a_fast 209000) := by
    apply a_fast_add
  rw [h]
  rw [a_fast_209000]
  rfl

lemma a_fast_211000 : a_fast 211000 = 380 := by
  have h : a_fast (210000 + 1000) = a_fast_loop 1000 (3^210000) (2^210000) (a_fast 210000) := by
    apply a_fast_add
  rw [h]
  rw [a_fast_210000]
  rfl

lemma a_fast_212000 : a_fast 212000 = 392 := by
  have h : a_fast (211000 + 1000) = a_fast_loop 1000 (3^211000) (2^211000) (a_fast 211000) := by
    apply a_fast_add
  rw [h]
  rw [a_fast_211000]
  rfl

lemma a_fast_213000 : a_fast 213000 = 374 := by
  have h : a_fast (212000 + 1000) = a_fast_loop 1000 (3^212000) (2^212000) (a_fast 212000) := by
    apply a_fast_add
  rw [h]
  rw [a_fast_212000]
  rfl

lemma a_fast_214000 : a_fast 214000 = 380 := by
  have h : a_fast (213000 + 1000) = a_fast_loop 1000 (3^213000) (2^213000) (a_fast 213000) := by
    apply a_fast_add
  rw [h]
  rw [a_fast_213000]
  rfl

lemma a_fast_215000 : a_fast 215000 = 424 := by
  have h : a_fast (214000 + 1000) = a_fast_loop 1000 (3^214000) (2^214000) (a_fast 214000) := by
    apply a_fast_add
  rw [h]
  rw [a_fast_214000]
  rfl

lemma a_fast_216000 : a_fast 216000 = 362 := by
  have h : a_fast (215000 + 1000) = a_fast_loop 1000 (3^215000) (2^215000) (a_fast 215000) := by
    apply a_fast_add
  rw [h]
  rw [a_fast_215000]
  rfl

lemma a_fast_217000 : a_fast 217000 = 340 := by
  have h : a_fast (216000 + 1000) = a_fast_loop 1000 (3^216000) (2^216000) (a_fast 216000) := by
    apply a_fast_add
  rw [h]
  rw [a_fast_216000]
  rfl

lemma a_fast_218000 : a_fast 218000 = 352 := by
  have h : a_fast (217000 + 1000) = a_fast_loop 1000 (3^217000) (2^217000) (a_fast 217000) := by
    apply a_fast_add
  rw [h]
  rw [a_fast_217000]
  rfl

lemma a_fast_219000 : a_fast 219000 = 370 := by
  have h : a_fast (218000 + 1000) = a_fast_loop 1000 (3^218000) (2^218000) (a_fast 218000) := by
    apply a_fast_add
  rw [h]
  rw [a_fast_218000]
  rfl

lemma a_fast_220000 : a_fast 220000 = 430 := by
  have h : a_fast (219000 + 1000) = a_fast_loop 1000 (3^219000) (2^219000) (a_fast 219000) := by
    apply a_fast_add
  rw [h]
  rw [a_fast_219000]
  rfl

lemma a_fast_221000 : a_fast 221000 = 418 := by
  have h : a_fast (220000 + 1000) = a_fast_loop 1000 (3^220000) (2^220000) (a_fast 220000) := by
    apply a_fast_add
  rw [h]
  rw [a_fast_220000]
  rfl

lemma a_fast_222000 : a_fast 222000 = 468 := by
  have h : a_fast (221000 + 1000) = a_fast_loop 1000 (3^221000) (2^221000) (a_fast 221000) := by
    apply a_fast_add
  rw [h]
  rw [a_fast_221000]
  rfl

lemma a_fast_223000 : a_fast 223000 = 504 := by
  have h : a_fast (222000 + 1000) = a_fast_loop 1000 (3^222000) (2^222000) (a_fast 222000) := by
    apply a_fast_add
  rw [h]
  rw [a_fast_222000]
  rfl

lemma a_fast_224000 : a_fast 224000 = 504 := by
  have h : a_fast (223000 + 1000) = a_fast_loop 1000 (3^223000) (2^223000) (a_fast 223000) := by
    apply a_fast_add
  rw [h]
  rw [a_fast_223000]
  rfl

lemma a_fast_225000 : a_fast 225000 = 536 := by
  have h : a_fast (224000 + 1000) = a_fast_loop 1000 (3^224000) (2^224000) (a_fast 224000) := by
    apply a_fast_add
  rw [h]
  rw [a_fast_224000]
  rfl

lemma a_fast_226000 : a_fast 226000 = 540 := by
  have h : a_fast (225000 + 1000) = a_fast_loop 1000 (3^225000) (2^225000) (a_fast 225000) := by
    apply a_fast_add
  rw [h]
  rw [a_fast_225000]
  rfl

lemma a_fast_227000 : a_fast 227000 = 532 := by
  have h : a_fast (226000 + 1000) = a_fast_loop 1000 (3^226000) (2^226000) (a_fast 226000) := by
    apply a_fast_add
  rw [h]
  rw [a_fast_226000]
  rfl

lemma a_fast_228000 : a_fast 228000 = 552 := by
  have h : a_fast (227000 + 1000) = a_fast_loop 1000 (3^227000) (2^227000) (a_fast 227000) := by
    apply a_fast_add
  rw [h]
  rw [a_fast_227000]
  rfl

lemma a_fast_229000 : a_fast 229000 = 576 := by
  have h : a_fast (228000 + 1000) = a_fast_loop 1000 (3^228000) (2^228000) (a_fast 228000) := by
    apply a_fast_add
  rw [h]
  rw [a_fast_228000]
  rfl

lemma a_fast_230000 : a_fast 230000 = 558 := by
  have h : a_fast (229000 + 1000) = a_fast_loop 1000 (3^229000) (2^229000) (a_fast 229000) := by
    apply a_fast_add
  rw [h]
  rw [a_fast_229000]
  rfl

lemma a_fast_231000 : a_fast 231000 = 514 := by
  have h : a_fast (230000 + 1000) = a_fast_loop 1000 (3^230000) (2^230000) (a_fast 230000) := by
    apply a_fast_add
  rw [h]
  rw [a_fast_230000]
  rfl

lemma a_fast_232000 : a_fast 232000 = 586 := by
  have h : a_fast (231000 + 1000) = a_fast_loop 1000 (3^231000) (2^231000) (a_fast 231000) := by
    apply a_fast_add
  rw [h]
  rw [a_fast_231000]
  rfl

lemma a_fast_233000 : a_fast 233000 = 590 := by
  have h : a_fast (232000 + 1000) = a_fast_loop 1000 (3^232000) (2^232000) (a_fast 232000) := by
    apply a_fast_add
  rw [h]
  rw [a_fast_232000]
  rfl

lemma a_fast_234000 : a_fast 234000 = 578 := by
  have h : a_fast (233000 + 1000) = a_fast_loop 1000 (3^233000) (2^233000) (a_fast 233000) := by
    apply a_fast_add
  rw [h]
  rw [a_fast_233000]
  rfl

lemma a_fast_235000 : a_fast 235000 = 554 := by
  have h : a_fast (234000 + 1000) = a_fast_loop 1000 (3^234000) (2^234000) (a_fast 234000) := by
    apply a_fast_add
  rw [h]
  rw [a_fast_234000]
  rfl

lemma a_fast_236000 : a_fast 236000 = 522 := by
  have h : a_fast (235000 + 1000) = a_fast_loop 1000 (3^235000) (2^235000) (a_fast 235000) := by
    apply a_fast_add
  rw [h]
  rw [a_fast_235000]
  rfl

lemma a_fast_237000 : a_fast 237000 = 540 := by
  have h : a_fast (236000 + 1000) = a_fast_loop 1000 (3^236000) (2^236000) (a_fast 236000) := by
    apply a_fast_add
  rw [h]
  rw [a_fast_236000]
  rfl

lemma a_fast_238000 : a_fast 238000 = 542 := by
  have h : a_fast (237000 + 1000) = a_fast_loop 1000 (3^237000) (2^237000) (a_fast 237000) := by
    apply a_fast_add
  rw [h]
  rw [a_fast_237000]
  rfl

lemma a_fast_239000 : a_fast 239000 = 532 := by
  have h : a_fast (238000 + 1000) = a_fast_loop 1000 (3^238000) (2^238000) (a_fast 238000) := by
    apply a_fast_add
  rw [h]
  rw [a_fast_238000]
  rfl

lemma a_fast_240000 : a_fast 240000 = 566 := by
  have h : a_fast (239000 + 1000) = a_fast_loop 1000 (3^239000) (2^239000) (a_fast 239000) := by
    apply a_fast_add
  rw [h]
  rw [a_fast_239000]
  rfl

lemma a_fast_241000 : a_fast 241000 = 590 := by
  have h : a_fast (240000 + 1000) = a_fast_loop 1000 (3^240000) (2^240000) (a_fast 240000) := by
    apply a_fast_add
  rw [h]
  rw [a_fast_240000]
  rfl

lemma a_fast_242000 : a_fast 242000 = 592 := by
  have h : a_fast (241000 + 1000) = a_fast_loop 1000 (3^241000) (2^241000) (a_fast 241000) := by
    apply a_fast_add
  rw [h]
  rw [a_fast_241000]
  rfl

lemma a_fast_243000 : a_fast 243000 = 578 := by
  have h : a_fast (242000 + 1000) = a_fast_loop 1000 (3^242000) (2^242000) (a_fast 242000) := by
    apply a_fast_add
  rw [h]
  rw [a_fast_242000]
  rfl

lemma a_fast_244000 : a_fast 244000 = 538 := by
  have h : a_fast (243000 + 1000) = a_fast_loop 1000 (3^243000) (2^243000) (a_fast 243000) := by
    apply a_fast_add
  rw [h]
  rw [a_fast_243000]
  rfl

lemma a_fast_245000 : a_fast 245000 = 538 := by
  have h : a_fast (244000 + 1000) = a_fast_loop 1000 (3^244000) (2^244000) (a_fast 244000) := by
    apply a_fast_add
  rw [h]
  rw [a_fast_244000]
  rfl

lemma a_fast_246000 : a_fast 246000 = 538 := by
  have h : a_fast (245000 + 1000) = a_fast_loop 1000 (3^245000) (2^245000) (a_fast 245000) := by
    apply a_fast_add
  rw [h]
  rw [a_fast_245000]
  rfl

lemma a_fast_247000 : a_fast 247000 = 558 := by
  have h : a_fast (246000 + 1000) = a_fast_loop 1000 (3^246000) (2^246000) (a_fast 246000) := by
    apply a_fast_add
  rw [h]
  rw [a_fast_246000]
  rfl

lemma a_fast_248000 : a_fast 248000 = 560 := by
  have h : a_fast (247000 + 1000) = a_fast_loop 1000 (3^247000) (2^247000) (a_fast 247000) := by
    apply a_fast_add
  rw [h]
  rw [a_fast_247000]
  rfl

lemma a_fast_249000 : a_fast 249000 = 542 := by
  have h : a_fast (248000 + 1000) = a_fast_loop 1000 (3^248000) (2^248000) (a_fast 248000) := by
    apply a_fast_add
  rw [h]
  rw [a_fast_248000]
  rfl

lemma a_fast_250000 : a_fast 250000 = 450 := by
  have h : a_fast (249000 + 1000) = a_fast_loop 1000 (3^249000) (2^249000) (a_fast 249000) := by
    apply a_fast_add
  rw [h]
  rw [a_fast_249000]
  rfl

lemma a_fast_251000 : a_fast 251000 = 448 := by
  have h : a_fast (250000 + 1000) = a_fast_loop 1000 (3^250000) (2^250000) (a_fast 250000) := by
    apply a_fast_add
  rw [h]
  rw [a_fast_250000]
  rfl

lemma a_fast_252000 : a_fast 252000 = 458 := by
  have h : a_fast (251000 + 1000) = a_fast_loop 1000 (3^251000) (2^251000) (a_fast 251000) := by
    apply a_fast_add
  rw [h]
  rw [a_fast_251000]
  rfl

lemma a_fast_253000 : a_fast 253000 = 430 := by
  have h : a_fast (252000 + 1000) = a_fast_loop 1000 (3^252000) (2^252000) (a_fast 252000) := by
    apply a_fast_add
  rw [h]
  rw [a_fast_252000]
  rfl

lemma a_fast_254000 : a_fast 254000 = 414 := by
  have h : a_fast (253000 + 1000) = a_fast_loop 1000 (3^253000) (2^253000) (a_fast 253000) := by
    apply a_fast_add
  rw [h]
  rw [a_fast_253000]
  rfl

lemma a_fast_255000 : a_fast 255000 = 372 := by
  have h : a_fast (254000 + 1000) = a_fast_loop 1000 (3^254000) (2^254000) (a_fast 254000) := by
    apply a_fast_add
  rw [h]
  rw [a_fast_254000]
  rfl

lemma a_fast_256000 : a_fast 256000 = 354 := by
  have h : a_fast (255000 + 1000) = a_fast_loop 1000 (3^255000) (2^255000) (a_fast 255000) := by
    apply a_fast_add
  rw [h]
  rw [a_fast_255000]
  rfl

lemma a_fast_257000 : a_fast 257000 = 332 := by
  have h : a_fast (256000 + 1000) = a_fast_loop 1000 (3^256000) (2^256000) (a_fast 256000) := by
    apply a_fast_add
  rw [h]
  rw [a_fast_256000]
  rfl

lemma a_fast_258000 : a_fast 258000 = 298 := by
  have h : a_fast (257000 + 1000) = a_fast_loop 1000 (3^257000) (2^257000) (a_fast 257000) := by
    apply a_fast_add
  rw [h]
  rw [a_fast_257000]
  rfl

lemma a_fast_259000 : a_fast 259000 = 320 := by
  have h : a_fast (258000 + 1000) = a_fast_loop 1000 (3^258000) (2^258000) (a_fast 258000) := by
    apply a_fast_add
  rw [h]
  rw [a_fast_258000]
  rfl

lemma a_fast_260000 : a_fast 260000 = 298 := by
  have h : a_fast (259000 + 1000) = a_fast_loop 1000 (3^259000) (2^259000) (a_fast 259000) := by
    apply a_fast_add
  rw [h]
  rw [a_fast_259000]
  rfl

lemma a_fast_261000 : a_fast 261000 = 258 := by
  have h : a_fast (260000 + 1000) = a_fast_loop 1000 (3^260000) (2^260000) (a_fast 260000) := by
    apply a_fast_add
  rw [h]
  rw [a_fast_260000]
  rfl

lemma a_fast_262000 : a_fast 262000 = 264 := by
  have h : a_fast (261000 + 1000) = a_fast_loop 1000 (3^261000) (2^261000) (a_fast 261000) := by
    apply a_fast_add
  rw [h]
  rw [a_fast_261000]
  rfl

lemma a_fast_263000 : a_fast 263000 = 238 := by
  have h : a_fast (262000 + 1000) = a_fast_loop 1000 (3^262000) (2^262000) (a_fast 262000) := by
    apply a_fast_add
  rw [h]
  rw [a_fast_262000]
  rfl

lemma a_fast_264000 : a_fast 264000 = 206 := by
  have h : a_fast (263000 + 1000) = a_fast_loop 1000 (3^263000) (2^263000) (a_fast 263000) := by
    apply a_fast_add
  rw [h]
  rw [a_fast_263000]
  rfl

lemma a_fast_265000 : a_fast 265000 = 272 := by
  have h : a_fast (264000 + 1000) = a_fast_loop 1000 (3^264000) (2^264000) (a_fast 264000) := by
    apply a_fast_add
  rw [h]
  rw [a_fast_264000]
  rfl

lemma a_fast_266000 : a_fast 266000 = 256 := by
  have h : a_fast (265000 + 1000) = a_fast_loop 1000 (3^265000) (2^265000) (a_fast 265000) := by
    apply a_fast_add
  rw [h]
  rw [a_fast_265000]
  rfl

lemma a_fast_267000 : a_fast 267000 = 222 := by
  have h : a_fast (266000 + 1000) = a_fast_loop 1000 (3^266000) (2^266000) (a_fast 266000) := by
    apply a_fast_add
  rw [h]
  rw [a_fast_266000]
  rfl

lemma a_fast_268000 : a_fast 268000 = 244 := by
  have h : a_fast (267000 + 1000) = a_fast_loop 1000 (3^267000) (2^267000) (a_fast 267000) := by
    apply a_fast_add
  rw [h]
  rw [a_fast_267000]
  rfl

lemma a_fast_269000 : a_fast 269000 = 140 := by
  have h : a_fast (268000 + 1000) = a_fast_loop 1000 (3^268000) (2^268000) (a_fast 268000) := by
    apply a_fast_add
  rw [h]
  rw [a_fast_268000]
  rfl

lemma a_fast_270000 : a_fast 270000 = 68 := by
  have h : a_fast (269000 + 1000) = a_fast_loop 1000 (3^269000) (2^269000) (a_fast 269000) := by
    apply a_fast_add
  rw [h]
  rw [a_fast_269000]
  rfl

lemma a_fast_271000 : a_fast 271000 = 100 := by
  have h : a_fast (270000 + 1000) = a_fast_loop 1000 (3^270000) (2^270000) (a_fast 270000) := by
    apply a_fast_add
  rw [h]
  rw [a_fast_270000]
  rfl

lemma a_fast_272000 : a_fast 272000 = 78 := by
  have h : a_fast (271000 + 1000) = a_fast_loop 1000 (3^271000) (2^271000) (a_fast 271000) := by
    apply a_fast_add
  rw [h]
  rw [a_fast_271000]
  rfl

lemma a_fast_273000 : a_fast 273000 = 78 := by
  have h : a_fast (272000 + 1000) = a_fast_loop 1000 (3^272000) (2^272000) (a_fast 272000) := by
    apply a_fast_add
  rw [h]
  rw [a_fast_272000]
  rfl

lemma a_fast_274000 : a_fast 274000 = 154 := by
  have h : a_fast (273000 + 1000) = a_fast_loop 1000 (3^273000) (2^273000) (a_fast 273000) := by
    apply a_fast_add
  rw [h]
  rw [a_fast_273000]
  rfl

lemma a_fast_275000 : a_fast 275000 = 206 := by
  have h : a_fast (274000 + 1000) = a_fast_loop 1000 (3^274000) (2^274000) (a_fast 274000) := by
    apply a_fast_add
  rw [h]
  rw [a_fast_274000]
  rfl

lemma a_fast_276000 : a_fast 276000 = 264 := by
  have h : a_fast (275000 + 1000) = a_fast_loop 1000 (3^275000) (2^275000) (a_fast 275000) := by
    apply a_fast_add
  rw [h]
  rw [a_fast_275000]
  rfl

lemma a_fast_277000 : a_fast 277000 = 238 := by
  have h : a_fast (276000 + 1000) = a_fast_loop 1000 (3^276000) (2^276000) (a_fast 276000) := by
    apply a_fast_add
  rw [h]
  rw [a_fast_276000]
  rfl

lemma a_fast_278000 : a_fast 278000 = 262 := by
  have h : a_fast (277000 + 1000) = a_fast_loop 1000 (3^277000) (2^277000) (a_fast 277000) := by
    apply a_fast_add
  rw [h]
  rw [a_fast_277000]
  rfl

lemma a_fast_279000 : a_fast 279000 = 244 := by
  have h : a_fast (278000 + 1000) = a_fast_loop 1000 (3^278000) (2^278000) (a_fast 278000) := by
    apply a_fast_add
  rw [h]
  rw [a_fast_278000]
  rfl

lemma a_fast_280000 : a_fast 280000 = 256 := by
  have h : a_fast (279000 + 1000) = a_fast_loop 1000 (3^279000) (2^279000) (a_fast 279000) := by
    apply a_fast_add
  rw [h]
  rw [a_fast_279000]
  rfl

lemma a_fast_281000 : a_fast 281000 = 242 := by
  have h : a_fast (280000 + 1000) = a_fast_loop 1000 (3^280000) (2^280000) (a_fast 280000) := by
    apply a_fast_add
  rw [h]
  rw [a_fast_280000]
  rfl

lemma a_fast_282000 : a_fast 282000 = 260 := by
  have h : a_fast (281000 + 1000) = a_fast_loop 1000 (3^281000) (2^281000) (a_fast 281000) := by
    apply a_fast_add
  rw [h]
  rw [a_fast_281000]
  rfl

lemma a_fast_283000 : a_fast 283000 = 252 := by
  have h : a_fast (282000 + 1000) = a_fast_loop 1000 (3^282000) (2^282000) (a_fast 282000) := by
    apply a_fast_add
  rw [h]
  rw [a_fast_282000]
  rfl

lemma a_fast_284000 : a_fast 284000 = 206 := by
  have h : a_fast (283000 + 1000) = a_fast_loop 1000 (3^283000) (2^283000) (a_fast 283000) := by
    apply a_fast_add
  rw [h]
  rw [a_fast_283000]
  rfl

lemma a_fast_285000 : a_fast 285000 = 214 := by
  have h : a_fast (284000 + 1000) = a_fast_loop 1000 (3^284000) (2^284000) (a_fast 284000) := by
    apply a_fast_add
  rw [h]
  rw [a_fast_284000]
  rfl

lemma a_fast_286000 : a_fast 286000 = 210 := by
  have h : a_fast (285000 + 1000) = a_fast_loop 1000 (3^285000) (2^285000) (a_fast 285000) := by
    apply a_fast_add
  rw [h]
  rw [a_fast_285000]
  rfl

lemma a_fast_287000 : a_fast 287000 = 196 := by
  have h : a_fast (286000 + 1000) = a_fast_loop 1000 (3^286000) (2^286000) (a_fast 286000) := by
    apply a_fast_add
  rw [h]
  rw [a_fast_286000]
  rfl

lemma a_fast_288000 : a_fast 288000 = 218 := by
  have h : a_fast (287000 + 1000) = a_fast_loop 1000 (3^287000) (2^287000) (a_fast 287000) := by
    apply a_fast_add
  rw [h]
  rw [a_fast_287000]
  rfl

lemma a_fast_289000 : a_fast 289000 = 204 := by
  have h : a_fast (288000 + 1000) = a_fast_loop 1000 (3^288000) (2^288000) (a_fast 288000) := by
    apply a_fast_add
  rw [h]
  rw [a_fast_288000]
  rfl

lemma a_fast_290000 : a_fast 290000 = 194 := by
  have h : a_fast (289000 + 1000) = a_fast_loop 1000 (3^289000) (2^289000) (a_fast 289000) := by
    apply a_fast_add
  rw [h]
  rw [a_fast_289000]
  rfl

lemma a_fast_291000 : a_fast 291000 = 162 := by
  have h : a_fast (290000 + 1000) = a_fast_loop 1000 (3^290000) (2^290000) (a_fast 290000) := by
    apply a_fast_add
  rw [h]
  rw [a_fast_290000]
  rfl

lemma a_fast_292000 : a_fast 292000 = 158 := by
  have h : a_fast (291000 + 1000) = a_fast_loop 1000 (3^291000) (2^291000) (a_fast 291000) := by
    apply a_fast_add
  rw [h]
  rw [a_fast_291000]
  rfl

lemma a_fast_293000 : a_fast 293000 = 120 := by
  have h : a_fast (292000 + 1000) = a_fast_loop 1000 (3^292000) (2^292000) (a_fast 292000) := by
    apply a_fast_add
  rw [h]
  rw [a_fast_292000]
  rfl

lemma a_fast_294000 : a_fast 294000 = 112 := by
  have h : a_fast (293000 + 1000) = a_fast_loop 1000 (3^293000) (2^293000) (a_fast 293000) := by
    apply a_fast_add
  rw [h]
  rw [a_fast_293000]
  rfl

lemma a_fast_295000 : a_fast 295000 = 134 := by
  have h : a_fast (294000 + 1000) = a_fast_loop 1000 (3^294000) (2^294000) (a_fast 294000) := by
    apply a_fast_add
  rw [h]
  rw [a_fast_294000]
  rfl

lemma a_fast_296000 : a_fast 296000 = 112 := by
  have h : a_fast (295000 + 1000) = a_fast_loop 1000 (3^295000) (2^295000) (a_fast 295000) := by
    apply a_fast_add
  rw [h]
  rw [a_fast_295000]
  rfl

lemma a_fast_297000 : a_fast 297000 = 86 := by
  have h : a_fast (296000 + 1000) = a_fast_loop 1000 (3^296000) (2^296000) (a_fast 296000) := by
    apply a_fast_add
  rw [h]
  rw [a_fast_296000]
  rfl

lemma a_fast_298000 : a_fast 298000 = 50 := by
  have h : a_fast (297000 + 1000) = a_fast_loop 1000 (3^297000) (2^297000) (a_fast 297000) := by
    apply a_fast_add
  rw [h]
  rw [a_fast_297000]
  rfl

lemma a_fast_299000 : a_fast 299000 = 112 := by
  have h : a_fast (298000 + 1000) = a_fast_loop 1000 (3^298000) (2^298000) (a_fast 298000) := by
    apply a_fast_add
  rw [h]
  rw [a_fast_298000]
  rfl

lemma a_fast_300000 : a_fast 300000 = 118 := by
  have h : a_fast (299000 + 1000) = a_fast_loop 1000 (3^299000) (2^299000) (a_fast 299000) := by
    apply a_fast_add
  rw [h]
  rw [a_fast_299000]
  rfl

lemma a_fast_301000 : a_fast 301000 = 128 := by
  have h : a_fast (300000 + 1000) = a_fast_loop 1000 (3^300000) (2^300000) (a_fast 300000) := by
    apply a_fast_add
  rw [h]
  rw [a_fast_300000]
  rfl

lemma a_fast_302000 : a_fast 302000 = 108 := by
  have h : a_fast (301000 + 1000) = a_fast_loop 1000 (3^301000) (2^301000) (a_fast 301000) := by
    apply a_fast_add
  rw [h]
  rw [a_fast_301000]
  rfl

lemma a_fast_303000 : a_fast 303000 = 186 := by
  have h : a_fast (302000 + 1000) = a_fast_loop 1000 (3^302000) (2^302000) (a_fast 302000) := by
    apply a_fast_add
  rw [h]
  rw [a_fast_302000]
  rfl

lemma a_fast_304000 : a_fast 304000 = 206 := by
  have h : a_fast (303000 + 1000) = a_fast_loop 1000 (3^303000) (2^303000) (a_fast 303000) := by
    apply a_fast_add
  rw [h]
  rw [a_fast_303000]
  rfl

lemma a_fast_305000 : a_fast 305000 = 192 := by
  have h : a_fast (304000 + 1000) = a_fast_loop 1000 (3^304000) (2^304000) (a_fast 304000) := by
    apply a_fast_add
  rw [h]
  rw [a_fast_304000]
  rfl

lemma a_fast_306000 : a_fast 306000 = 192 := by
  have h : a_fast (305000 + 1000) = a_fast_loop 1000 (3^305000) (2^305000) (a_fast 305000) := by
    apply a_fast_add
  rw [h]
  rw [a_fast_305000]
  rfl

lemma a_fast_307000 : a_fast 307000 = 210 := by
  have h : a_fast (306000 + 1000) = a_fast_loop 1000 (3^306000) (2^306000) (a_fast 306000) := by
    apply a_fast_add
  rw [h]
  rw [a_fast_306000]
  rfl

lemma a_fast_308000 : a_fast 308000 = 220 := by
  have h : a_fast (307000 + 1000) = a_fast_loop 1000 (3^307000) (2^307000) (a_fast 307000) := by
    apply a_fast_add
  rw [h]
  rw [a_fast_307000]
  rfl

lemma a_fast_309000 : a_fast 309000 = 192 := by
  have h : a_fast (308000 + 1000) = a_fast_loop 1000 (3^308000) (2^308000) (a_fast 308000) := by
    apply a_fast_add
  rw [h]
  rw [a_fast_308000]
  rfl

lemma a_fast_310000 : a_fast 310000 = 196 := by
  have h : a_fast (309000 + 1000) = a_fast_loop 1000 (3^309000) (2^309000) (a_fast 309000) := by
    apply a_fast_add
  rw [h]
  rw [a_fast_309000]
  rfl

lemma a_fast_311000 : a_fast 311000 = 132 := by
  have h : a_fast (310000 + 1000) = a_fast_loop 1000 (3^310000) (2^310000) (a_fast 310000) := by
    apply a_fast_add
  rw [h]
  rw [a_fast_310000]
  rfl

lemma a_fast_312000 : a_fast 312000 = 120 := by
  have h : a_fast (311000 + 1000) = a_fast_loop 1000 (3^311000) (2^311000) (a_fast 311000) := by
    apply a_fast_add
  rw [h]
  rw [a_fast_311000]
  rfl

lemma a_fast_313000 : a_fast 313000 = 146 := by
  have h : a_fast (312000 + 1000) = a_fast_loop 1000 (3^312000) (2^312000) (a_fast 312000) := by
    apply a_fast_add
  rw [h]
  rw [a_fast_312000]
  rfl

lemma a_fast_314000 : a_fast 314000 = 154 := by
  have h : a_fast (313000 + 1000) = a_fast_loop 1000 (3^313000) (2^313000) (a_fast 313000) := by
    apply a_fast_add
  rw [h]
  rw [a_fast_313000]
  rfl

lemma a_fast_315000 : a_fast 315000 = 136 := by
  have h : a_fast (314000 + 1000) = a_fast_loop 1000 (3^314000) (2^314000) (a_fast 314000) := by
    apply a_fast_add
  rw [h]
  rw [a_fast_314000]
  rfl

lemma a_fast_316000 : a_fast 316000 = 222 := by
  have h : a_fast (315000 + 1000) = a_fast_loop 1000 (3^315000) (2^315000) (a_fast 315000) := by
    apply a_fast_add
  rw [h]
  rw [a_fast_315000]
  rfl

lemma a_fast_317000 : a_fast 317000 = 214 := by
  have h : a_fast (316000 + 1000) = a_fast_loop 1000 (3^316000) (2^316000) (a_fast 316000) := by
    apply a_fast_add
  rw [h]
  rw [a_fast_316000]
  rfl

lemma a_fast_318000 : a_fast 318000 = 144 := by
  have h : a_fast (317000 + 1000) = a_fast_loop 1000 (3^317000) (2^317000) (a_fast 317000) := by
    apply a_fast_add
  rw [h]
  rw [a_fast_317000]
  rfl

lemma a_fast_319000 : a_fast 319000 = 138 := by
  have h : a_fast (318000 + 1000) = a_fast_loop 1000 (3^318000) (2^318000) (a_fast 318000) := by
    apply a_fast_add
  rw [h]
  rw [a_fast_318000]
  rfl

lemma a_fast_320000 : a_fast 320000 = 178 := by
  have h : a_fast (319000 + 1000) = a_fast_loop 1000 (3^319000) (2^319000) (a_fast 319000) := by
    apply a_fast_add
  rw [h]
  rw [a_fast_319000]
  rfl

lemma a_fast_321000 : a_fast 321000 = 156 := by
  have h : a_fast (320000 + 1000) = a_fast_loop 1000 (3^320000) (2^320000) (a_fast 320000) := by
    apply a_fast_add
  rw [h]
  rw [a_fast_320000]
  rfl

lemma a_fast_322000 : a_fast 322000 = 92 := by
  have h : a_fast (321000 + 1000) = a_fast_loop 1000 (3^321000) (2^321000) (a_fast 321000) := by
    apply a_fast_add
  rw [h]
  rw [a_fast_321000]
  rfl

lemma a_fast_323000 : a_fast 323000 = 104 := by
  have h : a_fast (322000 + 1000) = a_fast_loop 1000 (3^322000) (2^322000) (a_fast 322000) := by
    apply a_fast_add
  rw [h]
  rw [a_fast_322000]
  rfl

lemma a_fast_324000 : a_fast 324000 = 56 := by
  have h : a_fast (323000 + 1000) = a_fast_loop 1000 (3^323000) (2^323000) (a_fast 323000) := by
    apply a_fast_add
  rw [h]
  rw [a_fast_323000]
  rfl

lemma a_fast_325000 : a_fast 325000 = 76 := by
  have h : a_fast (324000 + 1000) = a_fast_loop 1000 (3^324000) (2^324000) (a_fast 324000) := by
    apply a_fast_add
  rw [h]
  rw [a_fast_324000]
  rfl

lemma a_fast_326000 : a_fast 326000 = 68 := by
  have h : a_fast (325000 + 1000) = a_fast_loop 1000 (3^325000) (2^325000) (a_fast 325000) := by
    apply a_fast_add
  rw [h]
  rw [a_fast_325000]
  rfl

lemma a_fast_327000 : a_fast 327000 = 108 := by
  have h : a_fast (326000 + 1000) = a_fast_loop 1000 (3^326000) (2^326000) (a_fast 326000) := by
    apply a_fast_add
  rw [h]
  rw [a_fast_326000]
  rfl

lemma a_fast_328000 : a_fast 328000 = 178 := by
  have h : a_fast (327000 + 1000) = a_fast_loop 1000 (3^327000) (2^327000) (a_fast 327000) := by
    apply a_fast_add
  rw [h]
  rw [a_fast_327000]
  rfl

lemma a_fast_329000 : a_fast 329000 = 134 := by
  have h : a_fast (328000 + 1000) = a_fast_loop 1000 (3^328000) (2^328000) (a_fast 328000) := by
    apply a_fast_add
  rw [h]
  rw [a_fast_328000]
  rfl

lemma a_fast_330000 : a_fast 330000 = 116 := by
  have h : a_fast (329000 + 1000) = a_fast_loop 1000 (3^329000) (2^329000) (a_fast 329000) := by
    apply a_fast_add
  rw [h]
  rw [a_fast_329000]
  rfl

lemma a_fast_331000 : a_fast 331000 = 60 := by
  have h : a_fast (330000 + 1000) = a_fast_loop 1000 (3^330000) (2^330000) (a_fast 330000) := by
    apply a_fast_add
  rw [h]
  rw [a_fast_330000]
  rfl

lemma a_fast_331523 : a_fast 331523 = -1 := by
  have h : a_fast (331000 + 523) = a_fast_loop 523 (3^331000) (2^331000) (a_fast 331000) := by
    apply a_fast_add
  rw [h]
  rw [a_fast_331000]
  rfl
