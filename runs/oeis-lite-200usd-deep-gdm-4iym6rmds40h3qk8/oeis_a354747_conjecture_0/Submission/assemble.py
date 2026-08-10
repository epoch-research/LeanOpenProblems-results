import sys

sys.set_int_max_str_digits(100000)

with open("/workspace/leanproject/Submission/temp_test.lean", "r") as f:
    temp_test_lines = f.readlines()

with open("/workspace/leanproject/Submission/test_proof.lean", "r") as f:
    test_proof_lines = f.readlines()

# Part 1: temp_test.lean lines 1 to 374 (1-based index: 0 to 373)
part1 = "".join(temp_test_lines[0:374])

# Part 2: Hierarchical cubing definitions and correct lemmas
part2 = """
-- Hierarchical cubing definitions
def cube_1 (x : LucasRing N_val D_val) : LucasRing N_val D_val :=
  let x3 := x * x * x
  ⟨ZMod.val x3.re, ZMod.val x3.im⟩

def cube_2 (x : LucasRing N_val D_val) : LucasRing N_val D_val := cube_1 (cube_1 x)
def cube_4 (x : LucasRing N_val D_val) : LucasRing N_val D_val := cube_2 (cube_2 x)
def cube_8 (x : LucasRing N_val D_val) : LucasRing N_val D_val := cube_4 (cube_4 x)
def cube_16 (x : LucasRing N_val D_val) : LucasRing N_val D_val := cube_8 (cube_8 x)
def cube_32 (x : LucasRing N_val D_val) : LucasRing N_val D_val := cube_16 (cube_16 x)
def cube_64 (x : LucasRing N_val D_val) : LucasRing N_val D_val := cube_32 (cube_32 x)
def cube_128 (x : LucasRing N_val D_val) : LucasRing N_val D_val := cube_64 (cube_64 x)
def cube_256 (x : LucasRing N_val D_val) : LucasRing N_val D_val := cube_128 (cube_128 x)
def cube_512 (x : LucasRing N_val D_val) : LucasRing N_val D_val := cube_256 (cube_256 x)
def cube_1024 (x : LucasRing N_val D_val) : LucasRing N_val D_val := cube_512 (cube_512 x)
def cube_2048 (x : LucasRing N_val D_val) : LucasRing N_val D_val := cube_1024 (cube_1024 x)
def cube_4096 (x : LucasRing N_val D_val) : LucasRing N_val D_val := cube_2048 (cube_2048 x)
def cube_8192 (x : LucasRing N_val D_val) : LucasRing N_val D_val := cube_4096 (cube_4096 x)
def cube_16384 (x : LucasRing N_val D_val) : LucasRing N_val D_val := cube_8192 (cube_8192 x)
def cube_32768 (x : LucasRing N_val D_val) : LucasRing N_val D_val := cube_16384 (cube_16384 x)

lemma cube_1_eq (x : LucasRing N_val D_val) : cube_1 x = x ^ (3 ^ 1) := by
  unfold cube_1
  have h_eq : (⟨(x * x * x).re.val, (x * x * x).im.val⟩ : LucasRing N_val D_val) = x * x * x := by
    ext <;> simp [ZMod.natCast_zmod_val]
  rw [h_eq]
  ring

lemma cube_2_eq (x : LucasRing N_val D_val) : cube_2 x = x ^ (3 ^ 2) := by
  unfold cube_2; rw [cube_1_eq, cube_1_eq, ← pow_mul]; congr 1

lemma cube_4_eq (x : LucasRing N_val D_val) : cube_4 x = x ^ (3 ^ 4) := by
  unfold cube_4; rw [cube_2_eq, cube_2_eq, ← pow_mul]; congr 1

lemma cube_8_eq (x : LucasRing N_val D_val) : cube_8 x = x ^ (3 ^ 8) := by
  unfold cube_8; rw [cube_4_eq, cube_4_eq, ← pow_mul]; congr 1

lemma cube_16_eq (x : LucasRing N_val D_val) : cube_16 x = x ^ (3 ^ 16) := by
  unfold cube_16; rw [cube_8_eq, cube_8_eq, ← pow_mul]; congr 1

lemma cube_32_eq (x : LucasRing N_val D_val) : cube_32 x = x ^ (3 ^ 32) := by
  unfold cube_32; rw [cube_16_eq, cube_16_eq, ← pow_mul]; congr 1

lemma cube_64_eq (x : LucasRing N_val D_val) : cube_64 x = x ^ (3 ^ 64) := by
  unfold cube_64; rw [cube_32_eq, cube_32_eq, ← pow_mul]; congr 1

lemma cube_128_eq (x : LucasRing N_val D_val) : cube_128 x = x ^ (3 ^ 128) := by
  unfold cube_128; rw [cube_64_eq, cube_64_eq, ← pow_mul]; congr 1

lemma cube_256_eq (x : LucasRing N_val D_val) : cube_256 x = x ^ (3 ^ 256) := by
  unfold cube_256; rw [cube_128_eq, cube_128_eq, ← pow_mul]; congr 1

lemma cube_512_eq (x : LucasRing N_val D_val) : cube_512 x = x ^ (3 ^ 512) := by
  unfold cube_512; rw [cube_256_eq, cube_256_eq, ← pow_mul]; congr 1

lemma cube_1024_eq (x : LucasRing N_val D_val) : cube_1024 x = x ^ (3 ^ 1024) := by
  unfold cube_1024; rw [cube_512_eq, cube_512_eq, ← pow_mul]; congr 1

lemma cube_2048_eq (x : LucasRing N_val D_val) : cube_2048 x = x ^ (3 ^ 2048) := by
  unfold cube_2048; rw [cube_1024_eq, cube_1024_eq, ← pow_mul]; congr 1

lemma cube_4096_eq (x : LucasRing N_val D_val) : cube_4096 x = x ^ (3 ^ 4096) := by
  unfold cube_4096; rw [cube_2048_eq, cube_2048_eq, ← pow_mul]; congr 1

lemma cube_8192_eq (x : LucasRing N_val D_val) : cube_8192 x = x ^ (3 ^ 8192) := by
  unfold cube_8192; rw [cube_4096_eq, cube_4096_eq, ← pow_mul]; congr 1

lemma cube_16384_eq (x : LucasRing N_val D_val) : cube_16384 x = x ^ (3 ^ 16384) := by
  unfold cube_16384; rw [cube_8192_eq, cube_8192_eq, ← pow_mul]; congr 1

lemma cube_32768_eq (x : LucasRing N_val D_val) : cube_32768 x = x ^ (3 ^ 32768) := by
  unfold cube_32768; rw [cube_16384_eq, cube_16384_eq, ← pow_mul]; congr 1

def cube_39101 (x : LucasRing N_val D_val) : LucasRing N_val D_val :=
  cube_1 (cube_4 (cube_8 (cube_16 (cube_32 (cube_128 (cube_2048 (cube_4096 (cube_32768 x))))))))

def cube_39100 (x : LucasRing N_val D_val) : LucasRing N_val D_val :=
  cube_8 (cube_16 (cube_64 (cube_2048 (cube_4096 (cube_32768 x)))))

lemma cube_39101_eq (x : LucasRing N_val D_val) : cube_39101 x = x ^ (3 ^ 39101) := by
  unfold cube_39101
  rw [cube_32768_eq, cube_4096_eq, cube_2048_eq, cube_128_eq, cube_32_eq, cube_16_eq, cube_8_eq, cube_4_eq, cube_1_eq]
  repeat rw [← pow_mul]
  congr 1

lemma cube_39100_eq (x : LucasRing N_val D_val) : cube_39100 x = x ^ (3 ^ 39100) := by
  unfold cube_39100
  rw [cube_32768_eq, cube_4096_eq, cube_2048_eq, cube_64_eq, cube_16_eq, cube_8_eq]
  repeat rw [← pow_mul]
  congr 1
"""

# Part 3: temp_test.lean lines 402 to 470 (0-based index: 401 to 469)
part3 = "".join(temp_test_lines[401:470])

# Part 4: Our fast definitions and their _eq lemmas
part4 = """
variable {p : ℕ}

def get_W2 (x : LucasRing p 5) : LucasRing p 5 :=
  cube_39101 (pow_chunk_loop 18 x 1 100943)

def get_W3 (x : LucasRing p 5) : LucasRing p 5 :=
  cube_39100 (pow_chunk_loop 18 (x * x) 1 100943)

def get_W100943 (x : LucasRing p 5) : LucasRing p 5 :=
  cube_39101 (x * x)

def get_W_all (x : LucasRing p 5) : LucasRing p 5 :=
  let w2 := get_W2 x
  w2 * w2

lemma get_W2_eq [NeZero p] (x : LucasRing p 5) : get_W2 x = x ^ ((N+1)/2) := by
  unfold get_W2
  rw [cube_39101_eq]
  have h_pow : pow_chunk_loop 18 x 1 100943 = x ^ 100943 := by
    rw [pow_chunk_loop_eq 18 100943 x 1 (by decide), one_mul]
  rw [h_pow]
  rw [← pow_mul]
  have h_eq : 100943 * 3 ^ 39101 = (N+1)/2 := by
    change 100943 * 3 ^ 39101 = (2 * 100943 * 3 ^ 39101 - 1 + 1) / 2
    have h_pos : 2 * 100943 * 3 ^ 39101 > 0 := by decide
    omega
  rw [h_eq]

lemma get_W3_eq [NeZero p] (x : LucasRing p 5) : get_W3 x = x ^ ((N+1)/3) := by
  unfold get_W3
  rw [cube_39100_eq]
  have h_pow : pow_chunk_loop 18 (x * x) 1 100943 = (x * x) ^ 100943 := by
    rw [pow_chunk_loop_eq 18 100943 (x * x) 1 (by decide), one_mul]
  rw [h_pow]
  have h_x2 : x * x = x^2 := by ring
  rw [h_x2]
  rw [← pow_mul, ← pow_mul]
  have h_div : 2 * (100943 * 3 ^ 39100) = (N+1)/3 := by
    change 2 * (100943 * 3 ^ 39100) = (2 * 100943 * 3 ^ 39101 - 1 + 1) / 3
    have h_pos : 2 * 100943 * 3 ^ 39101 > 0 := by decide
    have h_pow3 : 3 ^ 39100 * 3 = 3 ^ 39101 := rfl
    omega
  rw [h_div]

lemma get_W100943_eq [NeZero p] (x : LucasRing p 5) : get_W100943 x = x ^ ((N+1)/100943) := by
  unfold get_W100943
  rw [cube_39101_eq]
  have h_x2 : x * x = x^2 := by ring
  rw [h_x2]
  rw [← pow_mul]
  have h_eq : 2 * 3 ^ 39101 * 100943 = (N+1) := by
    change 2 * 3 ^ 39101 * 100943 = 2 * 100943 * 3 ^ 39101 - 1 + 1
    have h_pos : 2 * 100943 * 3 ^ 39101 > 0 := by decide
    omega
  have h_div : 2 * 3 ^ 39101 = (N+1)/100943 := by
    rw [← h_eq]
    exact (Nat.mul_div_cancel (2 * 3 ^ 39101) (by decide)).symm
  rw [h_div]

lemma get_W_all_eq [NeZero p] (x : LucasRing p 5) : get_W_all x = x ^ (N+1) := by
  unfold get_W_all
  rw [get_W2_eq]
  have h_sq : x ^ ((N+1)/2) * x ^ ((N+1)/2) = x ^ (2 * ((N+1)/2)) := by
    rw [← pow_add, ← mul_two]
    congr 1
  rw [h_sq]
  congr 1
"""

# Part 5: temp_test.lean lines 509 to 623 (0-based index: 508 to 623)
part5 = "".join(temp_test_lines[508:623])

# Part 6: test_proof.lean lines 692 to 881 (1-based index 692 to 881: 0-based 691 to 881)
part6 = "".join(test_proof_lines[691:881])

final_code = part1 + part2 + part3 + part4 + part5 + part6

with open("/workspace/leanproject/Submission/Spec.lean", "w") as f:
    f.write(final_code)

print("Spec.lean successfully assembled!")
