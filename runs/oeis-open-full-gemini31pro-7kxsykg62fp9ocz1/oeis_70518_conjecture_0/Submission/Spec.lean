import FormalConjectures.Util.ProblemImports

open Polynomial

set_option maxRecDepth 2000000
set_option exponentiation.threshold 30000

def myN : ℕ := 80321794921
def myP : ℕ := 283411

def x0 : ℕ := 28341
def x1 : ℕ := 803212281
def x2 : ℕ := 10305286175
def x3 : ℕ := 56856623504
def x4 : ℕ := 11119560660
def x5 : ℕ := 34823658856
def x6 : ℕ := 7305860158
def x7 : ℕ := 72720565854
def x8 : ℕ := 77339958728
def x9 : ℕ := 48530202121
def x10 : ℕ := 18484540212
def x11 : ℕ := 77970117019
def x12 : ℕ := 39630026099
def x13 : ℕ := 23437256541
def x14 : ℕ := 8780247748
lemma h0 : 28341 ^ 1 % myN = x0 := by rfl
lemma h1 : 28341 ^ 2 % myN = x1 := by
  have H : 28341 ^ 2 = (28341 ^ 1) ^ 2 := by
    have e : 2 = 1 * 2 := by decide
    rw [e, Nat.pow_mul]
  rw [H, Nat.pow_mod, h0]
  decide
lemma h2 : 28341 ^ 4 % myN = x2 := by
  have H : 28341 ^ 4 = (28341 ^ 2) ^ 2 := by
    have e : 4 = 2 * 2 := by decide
    rw [e, Nat.pow_mul]
  rw [H, Nat.pow_mod, h1]
  decide
lemma h3 : 28341 ^ 8 % myN = x3 := by
  have H : 28341 ^ 8 = (28341 ^ 4) ^ 2 := by
    have e : 8 = 4 * 2 := by decide
    rw [e, Nat.pow_mul]
  rw [H, Nat.pow_mod, h2]
  decide
lemma h4 : 28341 ^ 16 % myN = x4 := by
  have H : 28341 ^ 16 = (28341 ^ 8) ^ 2 := by
    have e : 16 = 8 * 2 := by decide
    rw [e, Nat.pow_mul]
  rw [H, Nat.pow_mod, h3]
  decide
lemma h5 : 28341 ^ 32 % myN = x5 := by
  have H : 28341 ^ 32 = (28341 ^ 16) ^ 2 := by
    have e : 32 = 16 * 2 := by decide
    rw [e, Nat.pow_mul]
  rw [H, Nat.pow_mod, h4]
  decide
lemma h6 : 28341 ^ 64 % myN = x6 := by
  have H : 28341 ^ 64 = (28341 ^ 32) ^ 2 := by
    have e : 64 = 32 * 2 := by decide
    rw [e, Nat.pow_mul]
  rw [H, Nat.pow_mod, h5]
  decide
lemma h7 : 28341 ^ 128 % myN = x7 := by
  have H : 28341 ^ 128 = (28341 ^ 64) ^ 2 := by
    have e : 128 = 64 * 2 := by decide
    rw [e, Nat.pow_mul]
  rw [H, Nat.pow_mod, h6]
  decide
lemma h8 : 28341 ^ 256 % myN = x8 := by
  have H : 28341 ^ 256 = (28341 ^ 128) ^ 2 := by
    have e : 256 = 128 * 2 := by decide
    rw [e, Nat.pow_mul]
  rw [H, Nat.pow_mod, h7]
  decide
lemma h9 : 28341 ^ 512 % myN = x9 := by
  have H : 28341 ^ 512 = (28341 ^ 256) ^ 2 := by
    have e : 512 = 256 * 2 := by decide
    rw [e, Nat.pow_mul]
  rw [H, Nat.pow_mod, h8]
  decide
lemma h10 : 28341 ^ 1024 % myN = x10 := by
  have H : 28341 ^ 1024 = (28341 ^ 512) ^ 2 := by
    have e : 1024 = 512 * 2 := by decide
    rw [e, Nat.pow_mul]
  rw [H, Nat.pow_mod, h9]
  decide
lemma h11 : 28341 ^ 2048 % myN = x11 := by
  have H : 28341 ^ 2048 = (28341 ^ 1024) ^ 2 := by
    have e : 2048 = 1024 * 2 := by decide
    rw [e, Nat.pow_mul]
  rw [H, Nat.pow_mod, h10]
  decide
lemma h12 : 28341 ^ 4096 % myN = x12 := by
  have H : 28341 ^ 4096 = (28341 ^ 2048) ^ 2 := by
    have e : 4096 = 2048 * 2 := by decide
    rw [e, Nat.pow_mul]
  rw [H, Nat.pow_mod, h11]
  decide
lemma h13 : 28341 ^ 8192 % myN = x13 := by
  have H : 28341 ^ 8192 = (28341 ^ 4096) ^ 2 := by
    have e : 8192 = 4096 * 2 := by decide
    rw [e, Nat.pow_mul]
  rw [H, Nat.pow_mod, h12]
  decide
lemma h14 : 28341 ^ 16384 % myN = x14 := by
  have H : 28341 ^ 16384 = (28341 ^ 8192) ^ 2 := by
    have e : 16384 = 8192 * 2 := by decide
    rw [e, Nat.pow_mul]
  rw [H, Nat.pow_mod, h13]
  decide
def e0 : ℕ := 1
def p0 : ℕ := x0
lemma hp0 : 28341 ^ e0 % myN = p0 := h0
def e1 : ℕ := 5
def p1 : ℕ := 12069152919
lemma hp1 : 28341 ^ e1 % myN = p1 := by
  have e : e1 = e0 + 4 := by decide
  have e2 : p0 * x2 % myN = p1 := by decide
  rw [e, Nat.pow_add, Nat.mul_mod, hp0, h2, e2]
def e2 : ℕ := 21
def p2 : ℕ := 58902886234
lemma hp2 : 28341 ^ e2 % myN = p2 := by
  have e : e2 = e1 + 16 := by decide
  have e2 : p1 * x4 % myN = p2 := by decide
  rw [e, Nat.pow_add, Nat.mul_mod, hp1, h4, e2]
def e3 : ℕ := 53
def p3 : ℕ := 3524814247
lemma hp3 : 28341 ^ e3 % myN = p3 := by
  have e : e3 = e2 + 32 := by decide
  have e2 : p2 * x5 % myN = p3 := by decide
  rw [e, Nat.pow_add, Nat.mul_mod, hp2, h5, e2]
def e4 : ℕ := 181
def p4 : ℕ := 59346352675
lemma hp4 : 28341 ^ e4 % myN = p4 := by
  have e : e4 = e3 + 128 := by decide
  have e2 : p3 * x7 % myN = p4 := by decide
  rw [e, Nat.pow_add, Nat.mul_mod, hp3, h7, e2]
def e5 : ℕ := 693
def p5 : ℕ := 71235197045
lemma hp5 : 28341 ^ e5 % myN = p5 := by
  have e : e5 = e4 + 512 := by decide
  have e2 : p4 * x9 % myN = p5 := by decide
  rw [e, Nat.pow_add, Nat.mul_mod, hp4, h9, e2]
def e6 : ℕ := 1717
def p6 : ℕ := 8309007975
lemma hp6 : 28341 ^ e6 % myN = p6 := by
  have e : e6 = e5 + 1024 := by decide
  have e2 : p5 * x10 % myN = p6 := by decide
  rw [e, Nat.pow_add, Nat.mul_mod, hp5, h10, e2]
def e7 : ℕ := 3765
def p7 : ℕ := 79405617822
lemma hp7 : 28341 ^ e7 % myN = p7 := by
  have e : e7 = e6 + 2048 := by decide
  have e2 : p6 * x11 % myN = p7 := by decide
  rw [e, Nat.pow_add, Nat.mul_mod, hp6, h11, e2]
def e8 : ℕ := 11957
def p8 : ℕ := 20736622302
lemma hp8 : 28341 ^ e8 % myN = p8 := by
  have e : e8 = e7 + 8192 := by decide
  have e2 : p7 * x13 % myN = p8 := by decide
  rw [e, Nat.pow_add, Nat.mul_mod, hp7, h13, e2]
def e9 : ℕ := 28341
def p9 : ℕ := 1
lemma hp9 : 28341 ^ e9 % myN = p9 := by
  have e : e9 = e8 + 16384 := by decide
  have e2 : p8 * x14 % myN = p9 := by decide
  rw [e, Nat.pow_add, Nat.mul_mod, hp8, h14, e2]
lemma final_pow : 28341 ^ 28341 % myN = 1 := hp9

lemma myN_dvd : myN ∣ 28341 ^ 28341 - 1 := by
  have H := final_pow
  have eq : 28341 ^ 28341 = myN * (28341 ^ 28341 / myN) + 28341 ^ 28341 % myN := (Nat.div_add_mod _ myN).symm
  rw [H] at eq
  have H2 : 28341 ^ 28341 - 1 = myN * (28341 ^ 28341 / myN) := by omega
  rw [H2]
  exact dvd_mul_right myN (28341 ^ 28341 / myN)

lemma myN_dvd_int : ((283411 : ℕ)^2 : ℤ) ∣ (28341 : ℤ) ^ 28341 - 1 := by
  have H : (myN : ℤ) ∣ ((28341 ^ 28341 - 1 : ℕ) : ℤ) := Int.ofNat_dvd.mpr myN_dvd
  have e1 : ((28341 ^ 28341 - 1 : ℕ) : ℤ) = (28341 : ℤ) ^ 28341 - 1 := by push_cast
  have e2 : ((283411 : ℕ)^2 : ℤ) = myN := by rfl
  rw [e2, ←e1]
  exact H
def xp0 : ℕ := 28341
def xp1 : ℕ := 25507
def xp2 : ℕ := 178804
def xp3 : ℕ := 125739
def xp4 : ℕ := 213486
def xp5 : ℕ := 99053
def xp6 : ℕ := 91400
def xp7 : ℕ := 137364
def xp8 : ℕ := 214349
def xp9 : ℕ := 36125
def xp10 : ℕ := 191381
def xp11 : ℕ := 66576
def xp12 : ℕ := 99147
def xp13 : ℕ := 17074
def xp14 : ℕ := 174968
lemma hp_0 : 28341 ^ 1 % myP = xp0 := by rfl
lemma hp_1 : 28341 ^ 2 % myP = xp1 := by
  have H : 28341 ^ 2 = (28341 ^ 1) ^ 2 := by
    have e : 2 = 1 * 2 := by decide
    rw [e, Nat.pow_mul]
  rw [H, Nat.pow_mod, hp_0]
  decide
lemma hp_2 : 28341 ^ 4 % myP = xp2 := by
  have H : 28341 ^ 4 = (28341 ^ 2) ^ 2 := by
    have e : 4 = 2 * 2 := by decide
    rw [e, Nat.pow_mul]
  rw [H, Nat.pow_mod, hp_1]
  decide
lemma hp_3 : 28341 ^ 8 % myP = xp3 := by
  have H : 28341 ^ 8 = (28341 ^ 4) ^ 2 := by
    have e : 8 = 4 * 2 := by decide
    rw [e, Nat.pow_mul]
  rw [H, Nat.pow_mod, hp_2]
  decide
lemma hp_4 : 28341 ^ 16 % myP = xp4 := by
  have H : 28341 ^ 16 = (28341 ^ 8) ^ 2 := by
    have e : 16 = 8 * 2 := by decide
    rw [e, Nat.pow_mul]
  rw [H, Nat.pow_mod, hp_3]
  decide
lemma hp_5 : 28341 ^ 32 % myP = xp5 := by
  have H : 28341 ^ 32 = (28341 ^ 16) ^ 2 := by
    have e : 32 = 16 * 2 := by decide
    rw [e, Nat.pow_mul]
  rw [H, Nat.pow_mod, hp_4]
  decide
lemma hp_6 : 28341 ^ 64 % myP = xp6 := by
  have H : 28341 ^ 64 = (28341 ^ 32) ^ 2 := by
    have e : 64 = 32 * 2 := by decide
    rw [e, Nat.pow_mul]
  rw [H, Nat.pow_mod, hp_5]
  decide
lemma hp_7 : 28341 ^ 128 % myP = xp7 := by
  have H : 28341 ^ 128 = (28341 ^ 64) ^ 2 := by
    have e : 128 = 64 * 2 := by decide
    rw [e, Nat.pow_mul]
  rw [H, Nat.pow_mod, hp_6]
  decide
lemma hp_8 : 28341 ^ 256 % myP = xp8 := by
  have H : 28341 ^ 256 = (28341 ^ 128) ^ 2 := by
    have e : 256 = 128 * 2 := by decide
    rw [e, Nat.pow_mul]
  rw [H, Nat.pow_mod, hp_7]
  decide
lemma hp_9 : 28341 ^ 512 % myP = xp9 := by
  have H : 28341 ^ 512 = (28341 ^ 256) ^ 2 := by
    have e : 512 = 256 * 2 := by decide
    rw [e, Nat.pow_mul]
  rw [H, Nat.pow_mod, hp_8]
  decide
lemma hp_10 : 28341 ^ 1024 % myP = xp10 := by
  have H : 28341 ^ 1024 = (28341 ^ 512) ^ 2 := by
    have e : 1024 = 512 * 2 := by decide
    rw [e, Nat.pow_mul]
  rw [H, Nat.pow_mod, hp_9]
  decide
lemma hp_11 : 28341 ^ 2048 % myP = xp11 := by
  have H : 28341 ^ 2048 = (28341 ^ 1024) ^ 2 := by
    have e : 2048 = 1024 * 2 := by decide
    rw [e, Nat.pow_mul]
  rw [H, Nat.pow_mod, hp_10]
  decide
lemma hp_12 : 28341 ^ 4096 % myP = xp12 := by
  have H : 28341 ^ 4096 = (28341 ^ 2048) ^ 2 := by
    have e : 4096 = 2048 * 2 := by decide
    rw [e, Nat.pow_mul]
  rw [H, Nat.pow_mod, hp_11]
  decide
lemma hp_13 : 28341 ^ 8192 % myP = xp13 := by
  have H : 28341 ^ 8192 = (28341 ^ 4096) ^ 2 := by
    have e : 8192 = 4096 * 2 := by decide
    rw [e, Nat.pow_mul]
  rw [H, Nat.pow_mod, hp_12]
  decide
lemma hp_14 : 28341 ^ 16384 % myP = xp14 := by
  have H : 28341 ^ 16384 = (28341 ^ 8192) ^ 2 := by
    have e : 16384 = 8192 * 2 := by decide
    rw [e, Nat.pow_mul]
  rw [H, Nat.pow_mod, hp_13]
  decide
def eM_9447_0 : ℕ := 1
def pM_9447_0 : ℕ := xp0
lemma hpM_9447_0 : 28341 ^ eM_9447_0 % myP = pM_9447_0 := hp_0
def eM_9447_1 : ℕ := 3
def pM_9447_1 : ℕ := 195837
lemma hpM_9447_1 : 28341 ^ eM_9447_1 % myP = pM_9447_1 := by
  have e : eM_9447_1 = eM_9447_0 + 2 := by decide
  have e2 : pM_9447_0 * xp1 % myP = pM_9447_1 := by decide
  rw [e, Nat.pow_add, Nat.mul_mod, hpM_9447_0, hp_1, e2]
def eM_9447_2 : ℕ := 7
def pM_9447_2 : ℕ := 159665
lemma hpM_9447_2 : 28341 ^ eM_9447_2 % myP = pM_9447_2 := by
  have e : eM_9447_2 = eM_9447_1 + 4 := by decide
  have e2 : pM_9447_1 * xp2 % myP = pM_9447_2 := by decide
  rw [e, Nat.pow_add, Nat.mul_mod, hpM_9447_1, hp_2, e2]
def eM_9447_3 : ℕ := 39
def pM_9447_3 : ℕ := 113212
lemma hpM_9447_3 : 28341 ^ eM_9447_3 % myP = pM_9447_3 := by
  have e : eM_9447_3 = eM_9447_2 + 32 := by decide
  have e2 : pM_9447_2 * xp5 % myP = pM_9447_3 := by decide
  rw [e, Nat.pow_add, Nat.mul_mod, hpM_9447_2, hp_5, e2]
def eM_9447_4 : ℕ := 103
def pM_9447_4 : ℕ := 241190
lemma hpM_9447_4 : 28341 ^ eM_9447_4 % myP = pM_9447_4 := by
  have e : eM_9447_4 = eM_9447_3 + 64 := by decide
  have e2 : pM_9447_3 * xp6 % myP = pM_9447_4 := by decide
  rw [e, Nat.pow_add, Nat.mul_mod, hpM_9447_3, hp_6, e2]
def eM_9447_5 : ℕ := 231
def pM_9447_5 : ℕ := 77260
lemma hpM_9447_5 : 28341 ^ eM_9447_5 % myP = pM_9447_5 := by
  have e : eM_9447_5 = eM_9447_4 + 128 := by decide
  have e2 : pM_9447_4 * xp7 % myP = pM_9447_5 := by decide
  rw [e, Nat.pow_add, Nat.mul_mod, hpM_9447_4, hp_7, e2]
def eM_9447_6 : ℕ := 1255
def pM_9447_6 : ℕ := 260779
lemma hpM_9447_6 : 28341 ^ eM_9447_6 % myP = pM_9447_6 := by
  have e : eM_9447_6 = eM_9447_5 + 1024 := by decide
  have e2 : pM_9447_5 * xp10 % myP = pM_9447_6 := by decide
  rw [e, Nat.pow_add, Nat.mul_mod, hpM_9447_5, hp_10, e2]
def eM_9447_7 : ℕ := 9447
def pM_9447_7 : ℕ := 153836
lemma hpM_9447_7 : 28341 ^ eM_9447_7 % myP = pM_9447_7 := by
  have e : eM_9447_7 = eM_9447_6 + 8192 := by decide
  have e2 : pM_9447_6 * xp13 % myP = pM_9447_7 := by decide
  rw [e, Nat.pow_add, Nat.mul_mod, hpM_9447_6, hp_13, e2]
lemma mod_p_9447 : 28341 ^ 9447 % myP = 153836 := hpM_9447_7
lemma not_dvd_9447 (contra : (283411 : ℤ) ∣ (28341 : ℤ)^9447 - 1) : False := by
  have H1 : ((28341^9447 - 1 : ℕ) : ℤ) = (28341 : ℤ)^9447 - 1 := by push_cast
  have H2 : (283411 : ℤ) ∣ ((28341^9447 - 1 : ℕ) : ℤ) := by rw [H1]; exact contra
  have H3 : 283411 ∣ 28341^9447 - 1 := Int.ofNat_dvd.mp H2
  have H4 : (28341^9447 - 1) % 283411 = 0 := Nat.mod_eq_zero_of_dvd H3
  have H7 := mod_p_9447
  have eP : myP = 283411 := rfl
  rw [eP] at H7
  have H5 : 28341^9447 = 283411 * (28341^9447 / 283411) + 28341^9447 % 283411 := (Nat.div_add_mod _ _).symm
  omega
def eM_603_0 : ℕ := 1
def pM_603_0 : ℕ := xp0
lemma hpM_603_0 : 28341 ^ eM_603_0 % myP = pM_603_0 := hp_0
def eM_603_1 : ℕ := 3
def pM_603_1 : ℕ := 195837
lemma hpM_603_1 : 28341 ^ eM_603_1 % myP = pM_603_1 := by
  have e : eM_603_1 = eM_603_0 + 2 := by decide
  have e2 : pM_603_0 * xp1 % myP = pM_603_1 := by decide
  rw [e, Nat.pow_add, Nat.mul_mod, hpM_603_0, hp_1, e2]
def eM_603_2 : ℕ := 11
def pM_603_2 : ℕ := 183808
lemma hpM_603_2 : 28341 ^ eM_603_2 % myP = pM_603_2 := by
  have e : eM_603_2 = eM_603_1 + 8 := by decide
  have e2 : pM_603_1 * xp3 % myP = pM_603_2 := by decide
  rw [e, Nat.pow_add, Nat.mul_mod, hpM_603_1, hp_3, e2]
def eM_603_3 : ℕ := 27
def pM_603_3 : ℕ := 197861
lemma hpM_603_3 : 28341 ^ eM_603_3 % myP = pM_603_3 := by
  have e : eM_603_3 = eM_603_2 + 16 := by decide
  have e2 : pM_603_2 * xp4 % myP = pM_603_3 := by decide
  rw [e, Nat.pow_add, Nat.mul_mod, hpM_603_2, hp_4, e2]
def eM_603_4 : ℕ := 91
def pM_603_4 : ℕ := 39490
lemma hpM_603_4 : 28341 ^ eM_603_4 % myP = pM_603_4 := by
  have e : eM_603_4 = eM_603_3 + 64 := by decide
  have e2 : pM_603_3 * xp6 % myP = pM_603_4 := by decide
  rw [e, Nat.pow_add, Nat.mul_mod, hpM_603_3, hp_6, e2]
def eM_603_5 : ℕ := 603
def pM_603_5 : ℕ := 168687
lemma hpM_603_5 : 28341 ^ eM_603_5 % myP = pM_603_5 := by
  have e : eM_603_5 = eM_603_4 + 512 := by decide
  have e2 : pM_603_4 * xp9 % myP = pM_603_5 := by decide
  rw [e, Nat.pow_add, Nat.mul_mod, hpM_603_4, hp_9, e2]
lemma mod_p_603 : 28341 ^ 603 % myP = 168687 := hpM_603_5
lemma not_dvd_603 (contra : (283411 : ℤ) ∣ (28341 : ℤ)^603 - 1) : False := by
  have H1 : ((28341^603 - 1 : ℕ) : ℤ) = (28341 : ℤ)^603 - 1 := by push_cast
  have H2 : (283411 : ℤ) ∣ ((28341^603 - 1 : ℕ) : ℤ) := by rw [H1]; exact contra
  have H3 : 283411 ∣ 28341^603 - 1 := Int.ofNat_dvd.mp H2
  have H4 : (28341^603 - 1) % 283411 = 0 := Nat.mod_eq_zero_of_dvd H3
  have H7 := mod_p_603
  have eP : myP = 283411 := rfl
  rw [eP] at H7
  have H5 : 28341^603 = 283411 * (28341^603 / 283411) + 28341^603 % 283411 := (Nat.div_add_mod _ _).symm
  omega
def eM_423_0 : ℕ := 1
def pM_423_0 : ℕ := xp0
lemma hpM_423_0 : 28341 ^ eM_423_0 % myP = pM_423_0 := hp_0
def eM_423_1 : ℕ := 3
def pM_423_1 : ℕ := 195837
lemma hpM_423_1 : 28341 ^ eM_423_1 % myP = pM_423_1 := by
  have e : eM_423_1 = eM_423_0 + 2 := by decide
  have e2 : pM_423_0 * xp1 % myP = pM_423_1 := by decide
  rw [e, Nat.pow_add, Nat.mul_mod, hpM_423_0, hp_1, e2]
def eM_423_2 : ℕ := 7
def pM_423_2 : ℕ := 159665
lemma hpM_423_2 : 28341 ^ eM_423_2 % myP = pM_423_2 := by
  have e : eM_423_2 = eM_423_1 + 4 := by decide
  have e2 : pM_423_1 * xp2 % myP = pM_423_2 := by decide
  rw [e, Nat.pow_add, Nat.mul_mod, hpM_423_1, hp_2, e2]
def eM_423_3 : ℕ := 39
def pM_423_3 : ℕ := 113212
lemma hpM_423_3 : 28341 ^ eM_423_3 % myP = pM_423_3 := by
  have e : eM_423_3 = eM_423_2 + 32 := by decide
  have e2 : pM_423_2 * xp5 % myP = pM_423_3 := by decide
  rw [e, Nat.pow_add, Nat.mul_mod, hpM_423_2, hp_5, e2]
def eM_423_4 : ℕ := 167
def pM_423_4 : ℕ := 208187
lemma hpM_423_4 : 28341 ^ eM_423_4 % myP = pM_423_4 := by
  have e : eM_423_4 = eM_423_3 + 128 := by decide
  have e2 : pM_423_3 * xp7 % myP = pM_423_4 := by decide
  rw [e, Nat.pow_add, Nat.mul_mod, hpM_423_3, hp_7, e2]
def eM_423_5 : ℕ := 423
def pM_423_5 : ℕ := 196258
lemma hpM_423_5 : 28341 ^ eM_423_5 % myP = pM_423_5 := by
  have e : eM_423_5 = eM_423_4 + 256 := by decide
  have e2 : pM_423_4 * xp8 % myP = pM_423_5 := by decide
  rw [e, Nat.pow_add, Nat.mul_mod, hpM_423_4, hp_8, e2]
lemma mod_p_423 : 28341 ^ 423 % myP = 196258 := hpM_423_5
lemma not_dvd_423 (contra : (283411 : ℤ) ∣ (28341 : ℤ)^423 - 1) : False := by
  have H1 : ((28341^423 - 1 : ℕ) : ℤ) = (28341 : ℤ)^423 - 1 := by push_cast
  have H2 : (283411 : ℤ) ∣ ((28341^423 - 1 : ℕ) : ℤ) := by rw [H1]; exact contra
  have H3 : 283411 ∣ 28341^423 - 1 := Int.ofNat_dvd.mp H2
  have H4 : (28341^423 - 1) % 283411 = 0 := Nat.mod_eq_zero_of_dvd H3
  have H7 := mod_p_423
  have eP : myP = 283411 := rfl
  rw [eP] at H7
  have H5 : 28341^423 = 283411 * (28341^423 / 283411) + 28341^423 % 283411 := (Nat.div_add_mod _ _).symm
  omega

lemma eval_cyclo_prod (n : ℕ) (x : ℤ) (hn : 0 < n) :
  x ^ n - 1 = ∏ i ∈ n.divisors, eval x (cyclotomic i ℤ) := by
  have eq := prod_cyclotomic_eq_X_pow_sub_one hn ℤ
  have eq2 := congrArg (eval x) eq
  simp only [eval_prod, eval_sub, eval_pow, eval_X, eval_one] at eq2
  exact eq2.symm

lemma dvd_47 (c : ℕ) (hc : c ∣ 47) : c = 1 ∨ c = 47 := by
  have H : Nat.Prime 47 := by norm_num
  exact Nat.Prime.eq_one_or_self_of_dvd H c hc

lemma dvd_67 (d : ℕ) (hd : d ∣ 67) : d = 1 ∨ d = 67 := by
  have H : Nat.Prime 67 := by norm_num
  exact Nat.Prime.eq_one_or_self_of_dvd H d hd

lemma dvd_9 (a : ℕ) (ha : a ∣ 9) : a = 1 ∨ a = 3 ∨ a = 9 := by
  have H2 : a ≤ 9 := Nat.le_of_dvd (by decide) ha
  match a with
  | 0 => revert ha; decide
  | 1 => decide
  | 2 => revert ha; decide
  | 3 => decide
  | 4 => revert ha; decide
  | 5 => revert ha; decide
  | 6 => revert ha; decide
  | 7 => revert ha; decide
  | 8 => revert ha; decide
  | 9 => decide
  | _ + 10 => omega

lemma get_k_cases (k : ℕ) (hk : k ∣ 28341) (hneq : k ≠ 28341) : k ∣ 9447 ∨ k ∣ 603 ∨ k ∣ 423 := by
  have hk2 : k ∣ 9 * 3149 := hk
  rcases Nat.dvd_mul.mp hk2 with ⟨a, b, ha, hb, hab⟩
  have hb2 : b ∣ 47 * 67 := hb
  rcases Nat.dvd_mul.mp hb2 with ⟨c, d, hc, hd, hcd⟩
  subst hcd
  subst hab
  rcases dvd_9 a ha with rfl | rfl | rfl
  · rcases dvd_47 c hc with rfl | rfl
    · rcases dvd_67 d hd with rfl | rfl
      · left; decide
      · left; decide
    · rcases dvd_67 d hd with rfl | rfl
      · left; decide
      · left; decide
  · rcases dvd_47 c hc with rfl | rfl
    · rcases dvd_67 d hd with rfl | rfl
      · left; decide
      · left; decide
    · rcases dvd_67 d hd with rfl | rfl
      · left; decide
      · left; decide
  · rcases dvd_47 c hc with rfl | rfl
    · rcases dvd_67 d hd with rfl | rfl
      · right; left; decide
      · right; left; decide
    · rcases dvd_67 d hd with rfl | rfl
      · right; right; decide
      · exfalso; apply hneq; decide

lemma cyclo_dvd (d : ℕ) (hd : 0 < d) (x : ℤ) : eval x (cyclotomic d ℤ) ∣ x ^ d - 1 := by
  have H1 : eval x (cyclotomic d ℤ) ∣ ∏ i ∈ d.divisors, eval x (cyclotomic i ℤ) :=
    Finset.dvd_prod_of_mem _ (Nat.mem_divisors.mpr ⟨dvd_rfl, ne_of_gt hd⟩)
  have eq2 := eval_cyclo_prod d x hd
  rwa [←eq2] at H1

lemma not_p_dvd_cyclo (k : ℕ) (hk : k ∣ 28341) (hneq : k ≠ 28341) : ¬ (283411 : ℤ) ∣ eval 28341 (cyclotomic k ℤ) := by
  intro contra
  have H : eval 28341 (cyclotomic k ℤ) ∣ (28341 : ℤ) ^ k - 1 := by
    apply cyclo_dvd
    rcases Nat.eq_zero_or_pos k with rfl | hpos
    · exfalso; exact absurd hk (by decide)
    · exact hpos
  have H2 : (283411 : ℤ) ∣ (28341 : ℤ) ^ k - 1 := dvd_trans contra H
  rcases get_k_cases k hk hneq with hk9447 | hk603 | hk423
  · rcases hk9447 with ⟨m, hm⟩
    have h_sub := sub_dvd_pow_sub_pow ((28341 : ℤ) ^ k) (1 : ℤ) m
    have e_pow : ((28341 : ℤ) ^ k) ^ m = (28341 : ℤ) ^ (k * m) := by rw [←pow_mul]
    have e_one : (1 : ℤ) ^ m = 1 := one_pow m
    rw [e_pow, e_one] at h_sub
    have H4 : (283411 : ℤ) ∣ (28341 : ℤ) ^ (k * m) - 1 := dvd_trans H2 h_sub
    rw [←hm] at H4
    exact not_dvd_9447 H4
  · rcases hk603 with ⟨m, hm⟩
    have h_sub := sub_dvd_pow_sub_pow ((28341 : ℤ) ^ k) (1 : ℤ) m
    have e_pow : ((28341 : ℤ) ^ k) ^ m = (28341 : ℤ) ^ (k * m) := by rw [←pow_mul]
    have e_one : (1 : ℤ) ^ m = 1 := one_pow m
    rw [e_pow, e_one] at h_sub
    have H4 : (283411 : ℤ) ∣ (28341 : ℤ) ^ (k * m) - 1 := dvd_trans H2 h_sub
    rw [←hm] at H4
    exact not_dvd_603 H4
  · rcases hk423 with ⟨m, hm⟩
    have h_sub := sub_dvd_pow_sub_pow ((28341 : ℤ) ^ k) (1 : ℤ) m
    have e_pow : ((28341 : ℤ) ^ k) ^ m = (28341 : ℤ) ^ (k * m) := by rw [←pow_mul]
    have e_one : (1 : ℤ) ^ m = 1 := one_pow m
    rw [e_pow, e_one] at h_sub
    have H4 : (283411 : ℤ) ∣ (28341 : ℤ) ^ (k * m) - 1 := dvd_trans H2 h_sub
    rw [←hm] at H4
    exact not_dvd_423 H4

lemma prime_p_int : Prime (283411 : ℤ) := by
  have : Nat.Prime 283411 := by norm_num
  exact Nat.prime_iff_prime_int.mp this

lemma not_p_dvd_prod : ¬ (283411 : ℤ) ∣ ∏ i ∈ (28341 : ℕ).divisors.erase 28341, eval 28341 (cyclotomic i ℤ) := by
  intro contra
  have h_prime := prime_p_int
  have H := (Prime.dvd_finset_prod_iff h_prime _).mp contra
  rcases H with ⟨k, hk, hk2⟩
  simp only [Finset.mem_erase, Nat.mem_divisors] at hk
  rcases hk with ⟨hneq, h_dvd, _⟩
  exact not_p_dvd_cyclo k h_dvd hneq hk2

/--
A070518: Value of $n$-th cyclotomic polynomial at $n$.
$$ a(n) = \Phi_n(n) $$
-/
noncomputable def a (n : ℕ) : ℕ :=
  (Polynomial.eval (Int.ofNat n) (cyclotomic n ℤ)).natAbs

theorem oeis_70518_conjecture_0 :
  (283411 : ℕ) ^ 2 ∣ a 28341 := by
  have eq1 : (28341 : ℤ) ^ 28341 - 1 = ∏ i ∈ (28341 : ℕ).divisors, eval (28341 : ℤ) (cyclotomic i ℤ) :=
    eval_cyclo_prod 28341 (28341 : ℤ) (by decide)
  have eq2 : ∏ i ∈ (28341 : ℕ).divisors, eval (28341 : ℤ) (cyclotomic i ℤ) =
    eval (28341 : ℤ) (cyclotomic 28341 ℤ) * ∏ i ∈ (28341 : ℕ).divisors.erase 28341, eval 28341 (cyclotomic i ℤ) := by
    have : 28341 ∈ (28341 : ℕ).divisors := Nat.mem_divisors.mpr ⟨dvd_rfl, by decide⟩
    exact (Finset.mul_prod_erase (28341 : ℕ).divisors (fun i => eval 28341 (cyclotomic i ℤ)) this).symm
  have eq3 : (28341 : ℤ) ^ 28341 - 1 = eval 28341 (cyclotomic 28341 ℤ) * ∏ i ∈ (28341 : ℕ).divisors.erase 28341, eval 28341 (cyclotomic i ℤ) := by
    rw [eq1, eq2]
  have H : ((283411 : ℕ)^2 : ℤ) ∣ eval 28341 (cyclotomic 28341 ℤ) * ∏ i ∈ (28341 : ℕ).divisors.erase 28341, eval 28341 (cyclotomic i ℤ) := by
    rw [←eq3]
    exact myN_dvd_int
  have H_coprime : IsCoprime (283411 : ℤ) (∏ i ∈ (28341 : ℕ).divisors.erase 28341, eval 28341 (cyclotomic i ℤ)) := by
    apply (Prime.coprime_iff_not_dvd prime_p_int).mpr not_p_dvd_prod
  have H_coprime2 : IsCoprime ((283411 : ℤ)^2) (∏ i ∈ (28341 : ℕ).divisors.erase 28341, eval 28341 (cyclotomic i ℤ)) := by
    exact IsCoprime.pow_left H_coprime
  have H_dvd : ((283411 : ℕ)^2 : ℤ) ∣ eval 28341 (cyclotomic 28341 ℤ) := by
    have e_pow : ((283411 : ℕ)^2 : ℤ) = (283411 : ℤ)^2 := by push_cast
    rw [e_pow] at H
    exact IsCoprime.dvd_of_dvd_mul_right H_coprime2 H
  have h1 : ((283411 : ℕ)^2 : ℤ).natAbs = (283411 : ℕ)^2 := rfl
  have h2 := Int.natAbs_dvd_natAbs.mpr H_dvd
  rw [h1] at h2
  have H_a : a 28341 = (eval (28341 : ℤ) (cyclotomic 28341 ℤ)).natAbs := rfl
  rw [H_a]
  exact h2

theorem oeis_70518_conjecture_0.disproof : ¬ (type_of% @oeis_70518_conjecture_0) := sorry
