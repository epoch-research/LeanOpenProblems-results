import Submission.Proof1
set_option maxRecDepth 1000000
abbrev M := ZMod 195318521017
def MatZ := (M × M) × (M × M) deriving DecidableEq
def mul_Z (A B : MatZ) : MatZ := let ((a, b), (c, d)) := A; let ((e, f), (g, h)) := B; (((a*e + b*g), (a*f + b*h)), ((c*e + d*g), (c*f + d*h)))
def m0_Z : MatZ := ((1, 0), (0, 1))
def T_Z : MatZ := ((1, 1), (1, 0))
def mat_pow_Z : ℕ → MatZ | 0 => m0_Z | n + 1 => mul_Z T_Z (mat_pow_Z n)
lemma ext_MatZ {A B : MatZ} (h1 : A.1.1 = B.1.1) (h2 : A.1.2 = B.1.2) (h3 : A.2.1 = B.2.1) (h4 : A.2.2 = B.2.2) : A = B := by rcases A with ⟨⟨a, b⟩, ⟨c, d⟩⟩; rcases B with ⟨⟨e, f⟩, ⟨g, h⟩⟩; dsimp at h1 h2 h3 h4; rw [h1, h2, h3, h4]
lemma my_mul_assoc (A B C : MatZ) : mul_Z (mul_Z A B) C = mul_Z A (mul_Z B C) := by rcases A with ⟨⟨a, b⟩, ⟨c, d⟩⟩; rcases B with ⟨⟨e, f⟩, ⟨g, h⟩⟩; rcases C with ⟨⟨i, j⟩, ⟨k, l⟩⟩; apply ext_MatZ <;> (dsimp [mul_Z]; ring)
lemma my_mul_m0 (A : MatZ) : mul_Z m0_Z A = A := by rcases A with ⟨⟨a, b⟩, ⟨c, d⟩⟩; apply ext_MatZ <;> (dsimp [mul_Z, m0_Z]; ring)
lemma mat_pow_add (n m : ℕ) : mat_pow_Z (n + m) = mul_Z (mat_pow_Z n) (mat_pow_Z m) := by induction n with | zero => rw [Nat.zero_add]; change mat_pow_Z m = mul_Z m0_Z (mat_pow_Z m); rw [my_mul_m0] | succ k ih => rw [Nat.succ_add]; change mul_Z T_Z (mat_pow_Z (k + m)) = mul_Z (mul_Z T_Z (mat_pow_Z k)) (mat_pow_Z m); rw [ih, my_mul_assoc]
lemma mat_pow_mul2 (n : ℕ) : mat_pow_Z (n * 2) = mul_Z (mat_pow_Z n) (mat_pow_Z n) := by
  have h : n * 2 = n + n := by omega
  rw [h]
  rw [mat_pow_add]
def m1_Z : MatZ := let sq := mul_Z m0_Z m0_Z; mul_Z T_Z sq
def m2_Z : MatZ := let sq := mul_Z m1_Z m1_Z; mul_Z T_Z sq
def m3_Z : MatZ := let sq := mul_Z m2_Z m2_Z; mul_Z T_Z sq
def m4_Z : MatZ := let sq := mul_Z m3_Z m3_Z; sq
def m5_Z : MatZ := let sq := mul_Z m4_Z m4_Z; mul_Z T_Z sq
def m6_Z : MatZ := let sq := mul_Z m5_Z m5_Z; sq
def m7_Z : MatZ := let sq := mul_Z m6_Z m6_Z; sq
def m8_Z : MatZ := let sq := mul_Z m7_Z m7_Z; sq
def m9_Z : MatZ := let sq := mul_Z m8_Z m8_Z; sq
def m10_Z : MatZ := let sq := mul_Z m9_Z m9_Z; mul_Z T_Z sq
def m11_Z : MatZ := let sq := mul_Z m10_Z m10_Z; mul_Z T_Z sq
def m12_Z : MatZ := let sq := mul_Z m11_Z m11_Z; mul_Z T_Z sq
def m13_Z : MatZ := let sq := mul_Z m12_Z m12_Z; sq
def m14_Z : MatZ := let sq := mul_Z m13_Z m13_Z; sq
def m15_Z : MatZ := let sq := mul_Z m14_Z m14_Z; sq
def m16_Z : MatZ := let sq := mul_Z m15_Z m15_Z; sq
def m17_Z : MatZ := let sq := mul_Z m16_Z m16_Z; mul_Z T_Z sq
def m18_Z : MatZ := let sq := mul_Z m17_Z m17_Z; sq
def m19_Z : MatZ := let sq := mul_Z m18_Z m18_Z; sq
def m20_Z : MatZ := let sq := mul_Z m19_Z m19_Z; sq
def m21_Z : MatZ := let sq := mul_Z m20_Z m20_Z; sq
def m22_Z : MatZ := let sq := mul_Z m21_Z m21_Z; mul_Z T_Z sq
def m23_Z : MatZ := let sq := mul_Z m22_Z m22_Z; mul_Z T_Z sq
def m24_Z : MatZ := let sq := mul_Z m23_Z m23_Z; sq
def m25_Z : MatZ := let sq := mul_Z m24_Z m24_Z; mul_Z T_Z sq
def m26_Z : MatZ := let sq := mul_Z m25_Z m25_Z; mul_Z T_Z sq
def m27_Z : MatZ := let sq := mul_Z m26_Z m26_Z; sq
def m28_Z : MatZ := let sq := mul_Z m27_Z m27_Z; sq
def m29_Z : MatZ := let sq := mul_Z m28_Z m28_Z; sq
def m30_Z : MatZ := let sq := mul_Z m29_Z m29_Z; mul_Z T_Z sq
def m31_Z : MatZ := let sq := mul_Z m30_Z m30_Z; sq
def m32_Z : MatZ := let sq := mul_Z m31_Z m31_Z; sq
def m33_Z : MatZ := let sq := mul_Z m32_Z m32_Z; sq
def m34_Z : MatZ := let sq := mul_Z m33_Z m33_Z; mul_Z T_Z sq
def m35_Z : MatZ := let sq := mul_Z m34_Z m34_Z; sq
def m36_Z : MatZ := let sq := mul_Z m35_Z m35_Z; sq
def m37_Z : MatZ := let sq := mul_Z m36_Z m36_Z; sq
def m38_Z : MatZ := let sq := mul_Z m37_Z m37_Z; mul_Z T_Z sq
lemma eval_m0 : mat_pow_Z 0 = m0_Z := rfl
lemma eval_m1 : mat_pow_Z 1 = m1_Z := by
  have h1 : 1 = 1 + 0 * 2 := by rfl
  rw [h1]
  rw [mat_pow_add, mat_pow_mul2, eval_m0]
  rfl
lemma eval_m2 : mat_pow_Z 3 = m2_Z := by
  have h1 : 3 = 1 + 1 * 2 := by rfl
  rw [h1]
  rw [mat_pow_add, mat_pow_mul2, eval_m1]
  rfl
lemma eval_m3 : mat_pow_Z 7 = m3_Z := by
  have h1 : 7 = 1 + 3 * 2 := by rfl
  rw [h1]
  rw [mat_pow_add, mat_pow_mul2, eval_m2]
  rfl
lemma eval_m4 : mat_pow_Z 14 = m4_Z := by
  have h1 : 14 = 7 * 2 := by rfl
  rw [h1]
  rw [mat_pow_mul2, eval_m3]
  rfl
lemma eval_m5 : mat_pow_Z 29 = m5_Z := by
  have h1 : 29 = 1 + 14 * 2 := by rfl
  rw [h1]
  rw [mat_pow_add, mat_pow_mul2, eval_m4]
  rfl
lemma eval_m6 : mat_pow_Z 58 = m6_Z := by
  have h1 : 58 = 29 * 2 := by rfl
  rw [h1]
  rw [mat_pow_mul2, eval_m5]
  rfl
lemma eval_m7 : mat_pow_Z 116 = m7_Z := by
  have h1 : 116 = 58 * 2 := by rfl
  rw [h1]
  rw [mat_pow_mul2, eval_m6]
  rfl
lemma eval_m8 : mat_pow_Z 232 = m8_Z := by
  have h1 : 232 = 116 * 2 := by rfl
  rw [h1]
  rw [mat_pow_mul2, eval_m7]
  rfl
lemma eval_m9 : mat_pow_Z 464 = m9_Z := by
  have h1 : 464 = 232 * 2 := by rfl
  rw [h1]
  rw [mat_pow_mul2, eval_m8]
  rfl
lemma eval_m10 : mat_pow_Z 929 = m10_Z := by
  have h1 : 929 = 1 + 464 * 2 := by rfl
  rw [h1]
  rw [mat_pow_add, mat_pow_mul2, eval_m9]
  rfl
lemma eval_m11 : mat_pow_Z 1859 = m11_Z := by
  have h1 : 1859 = 1 + 929 * 2 := by rfl
  rw [h1]
  rw [mat_pow_add, mat_pow_mul2, eval_m10]
  rfl
lemma eval_m12 : mat_pow_Z 3719 = m12_Z := by
  have h1 : 3719 = 1 + 1859 * 2 := by rfl
  rw [h1]
  rw [mat_pow_add, mat_pow_mul2, eval_m11]
  rfl
lemma eval_m13 : mat_pow_Z 7438 = m13_Z := by
  have h1 : 7438 = 3719 * 2 := by rfl
  rw [h1]
  rw [mat_pow_mul2, eval_m12]
  rfl
lemma eval_m14 : mat_pow_Z 14876 = m14_Z := by
  have h1 : 14876 = 7438 * 2 := by rfl
  rw [h1]
  rw [mat_pow_mul2, eval_m13]
  rfl
lemma eval_m15 : mat_pow_Z 29752 = m15_Z := by
  have h1 : 29752 = 14876 * 2 := by rfl
  rw [h1]
  rw [mat_pow_mul2, eval_m14]
  rfl
lemma eval_m16 : mat_pow_Z 59504 = m16_Z := by
  have h1 : 59504 = 29752 * 2 := by rfl
  rw [h1]
  rw [mat_pow_mul2, eval_m15]
  rfl
lemma eval_m17 : mat_pow_Z 119009 = m17_Z := by
  have h1 : 119009 = 1 + 59504 * 2 := by rfl
  rw [h1]
  rw [mat_pow_add, mat_pow_mul2, eval_m16]
  rfl
lemma eval_m18 : mat_pow_Z 238018 = m18_Z := by
  have h1 : 238018 = 119009 * 2 := by rfl
  rw [h1]
  rw [mat_pow_mul2, eval_m17]
  rfl
lemma eval_m19 : mat_pow_Z 476036 = m19_Z := by
  have h1 : 476036 = 238018 * 2 := by rfl
  rw [h1]
  rw [mat_pow_mul2, eval_m18]
  rfl
lemma eval_m20 : mat_pow_Z 952072 = m20_Z := by
  have h1 : 952072 = 476036 * 2 := by rfl
  rw [h1]
  rw [mat_pow_mul2, eval_m19]
  rfl
lemma eval_m21 : mat_pow_Z 1904144 = m21_Z := by
  have h1 : 1904144 = 952072 * 2 := by rfl
  rw [h1]
  rw [mat_pow_mul2, eval_m20]
  rfl
lemma eval_m22 : mat_pow_Z 3808289 = m22_Z := by
  have h1 : 3808289 = 1 + 1904144 * 2 := by rfl
  rw [h1]
  rw [mat_pow_add, mat_pow_mul2, eval_m21]
  rfl
lemma eval_m23 : mat_pow_Z 7616579 = m23_Z := by
  have h1 : 7616579 = 1 + 3808289 * 2 := by rfl
  rw [h1]
  rw [mat_pow_add, mat_pow_mul2, eval_m22]
  rfl
lemma eval_m24 : mat_pow_Z 15233158 = m24_Z := by
  have h1 : 15233158 = 7616579 * 2 := by rfl
  rw [h1]
  rw [mat_pow_mul2, eval_m23]
  rfl
lemma eval_m25 : mat_pow_Z 30466317 = m25_Z := by
  have h1 : 30466317 = 1 + 15233158 * 2 := by rfl
  rw [h1]
  rw [mat_pow_add, mat_pow_mul2, eval_m24]
  rfl
lemma eval_m26 : mat_pow_Z 60932635 = m26_Z := by
  have h1 : 60932635 = 1 + 30466317 * 2 := by rfl
  rw [h1]
  rw [mat_pow_add, mat_pow_mul2, eval_m25]
  rfl
lemma eval_m27 : mat_pow_Z 121865270 = m27_Z := by
  have h1 : 121865270 = 60932635 * 2 := by rfl
  rw [h1]
  rw [mat_pow_mul2, eval_m26]
  rfl
lemma eval_m28 : mat_pow_Z 243730540 = m28_Z := by
  have h1 : 243730540 = 121865270 * 2 := by rfl
  rw [h1]
  rw [mat_pow_mul2, eval_m27]
  rfl
lemma eval_m29 : mat_pow_Z 487461080 = m29_Z := by
  have h1 : 487461080 = 243730540 * 2 := by rfl
  rw [h1]
  rw [mat_pow_mul2, eval_m28]
  rfl
lemma eval_m30 : mat_pow_Z 974922161 = m30_Z := by
  have h1 : 974922161 = 1 + 487461080 * 2 := by rfl
  rw [h1]
  rw [mat_pow_add, mat_pow_mul2, eval_m29]
  rfl
lemma eval_m31 : mat_pow_Z 1949844322 = m31_Z := by
  have h1 : 1949844322 = 974922161 * 2 := by rfl
  rw [h1]
  rw [mat_pow_mul2, eval_m30]
  rfl
lemma eval_m32 : mat_pow_Z 3899688644 = m32_Z := by
  have h1 : 3899688644 = 1949844322 * 2 := by rfl
  rw [h1]
  rw [mat_pow_mul2, eval_m31]
  rfl
lemma eval_m33 : mat_pow_Z 7799377288 = m33_Z := by
  have h1 : 7799377288 = 3899688644 * 2 := by rfl
  rw [h1]
  rw [mat_pow_mul2, eval_m32]
  rfl
lemma eval_m34 : mat_pow_Z 15598754577 = m34_Z := by
  have h1 : 15598754577 = 1 + 7799377288 * 2 := by rfl
  rw [h1]
  rw [mat_pow_add, mat_pow_mul2, eval_m33]
  rfl
lemma eval_m35 : mat_pow_Z 31197509154 = m35_Z := by
  have h1 : 31197509154 = 15598754577 * 2 := by rfl
  rw [h1]
  rw [mat_pow_mul2, eval_m34]
  rfl
lemma eval_m36 : mat_pow_Z 62395018308 = m36_Z := by
  have h1 : 62395018308 = 31197509154 * 2 := by rfl
  rw [h1]
  rw [mat_pow_mul2, eval_m35]
  rfl
lemma eval_m37 : mat_pow_Z 124790036616 = m37_Z := by
  have h1 : 124790036616 = 62395018308 * 2 := by rfl
  rw [h1]
  rw [mat_pow_mul2, eval_m36]
  rfl
lemma eval_m38 : mat_pow_Z 249580073233 = m38_Z := by
  have h1 : 249580073233 = 1 + 124790036616 * 2 := by rfl
  rw [h1]
  rw [mat_pow_add, mat_pow_mul2, eval_m37]
  rfl
def vec_mul_Z (A : MatZ) (v : M × M) : M × M := let ((a, b), (c, d)) := A; let (x, y) := v; (((a*x + b*y), (c*x + d*y)))
lemma hit_one_one_Z : vec_mul_Z (mat_pow_Z 249580073233) (99768150822, 77940394259) = (1, 1) := by
  rw [eval_m38]
  decide
