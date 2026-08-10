import sys

sys.set_int_max_str_digits(100000)

with open("/workspace/leanproject/Submission/temp_test.lean", "r") as f:
    temp_test_lines = f.readlines()

with open("/workspace/leanproject/Submission/test_proof.lean", "r") as f:
    test_proof_lines = f.readlines()

# Part 1: temp_test.lean lines 1 to 374 (1-based index: 0 to 373)
part1_lines = temp_test_lines[0:374]

# Insert set_option linter.all false
part1_lines.insert(2, "set_option linter.all false\n")

part1 = "".join(part1_lines)

# Set maxRecDepth to 1000000
part1 = part1.replace("set_option maxRecDepth 100000", "set_option maxRecDepth 1000000")

# Optimize NeZero N and Fact (1 < N)
part1 = part1.replace("instance : NeZero N := ⟨by decide⟩", """instance : NeZero N := ⟨by
  unfold N
  have h_pow : 3 ^ 39101 > 0 := Nat.pow_pos (by decide)
  omega⟩""")

part1 = part1.replace("instance : Fact (1 < N) := ⟨by decide⟩", """instance : Fact (1 < N) := ⟨by
  unfold N
  have h_pow : 3 ^ 39101 > 0 := Nat.pow_pos (by decide)
  omega⟩

attribute [irreducible] N""")

# Replace rfl on ZMod N with unfold N; rfl
part1 = part1.replace("have h_five : (5 : ZMod N).val = 5 := rfl", "have h_five : (5 : ZMod N).val = 5 := by unfold N; rfl")
part1 = part1.replace("have h_one : (1 : ZMod N).val = 1 := rfl", "have h_one : (1 : ZMod N).val = 1 := by unfold N; rfl")
part1 = part1.replace("have h_zero : (0 : ZMod N).val = 0 := rfl", "have h_zero : (0 : ZMod N).val = 0 := by unfold N; rfl")
part1 = part1.replace("have h2 : (1 : ZMod N).val = 1 := rfl", "have h2 : (1 : ZMod N).val = 1 := by unfold N; rfl")


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

lemma cube_1_eq [NeZero N_val] (x : LucasRing N_val D_val) : cube_1 x = x ^ (3 ^ 1) := by
  unfold cube_1
  have h_eq : (⟨(x * x * x).re.val, (x * x * x).im.val⟩ : LucasRing N_val D_val) = x * x * x := by
    ext <;> simp [ZMod.natCast_zmod_val]
  rw [h_eq]
  ring

lemma cube_2_eq [NeZero N_val] (x : LucasRing N_val D_val) : cube_2 x = x ^ (3 ^ 2) := by
  unfold cube_2; rw [cube_1_eq, cube_1_eq, ← pow_mul]; congr 1

lemma cube_4_eq [NeZero N_val] (x : LucasRing N_val D_val) : cube_4 x = x ^ (3 ^ 4) := by
  unfold cube_4; rw [cube_2_eq, cube_2_eq, ← pow_mul]; congr 1

lemma cube_8_eq [NeZero N_val] (x : LucasRing N_val D_val) : cube_8 x = x ^ (3 ^ 8) := by
  unfold cube_8; rw [cube_4_eq, cube_4_eq, ← pow_mul]; congr 1

lemma cube_16_eq [NeZero N_val] (x : LucasRing N_val D_val) : cube_16 x = x ^ (3 ^ 16) := by
  unfold cube_16; rw [cube_8_eq, cube_8_eq, ← pow_mul]; congr 1

lemma cube_32_eq [NeZero N_val] (x : LucasRing N_val D_val) : cube_32 x = x ^ (3 ^ 32) := by
  unfold cube_32; rw [cube_16_eq, cube_16_eq, ← pow_mul]; congr 1

lemma cube_64_eq [NeZero N_val] (x : LucasRing N_val D_val) : cube_64 x = x ^ (3 ^ 64) := by
  unfold cube_64; rw [cube_32_eq, cube_32_eq, ← pow_mul]; congr 1

lemma cube_128_eq [NeZero N_val] (x : LucasRing N_val D_val) : cube_128 x = x ^ (3 ^ 128) := by
  unfold cube_128; rw [cube_64_eq, cube_64_eq, ← pow_mul]; congr 1

lemma cube_256_eq [NeZero N_val] (x : LucasRing N_val D_val) : cube_256 x = x ^ (3 ^ 256) := by
  unfold cube_256; rw [cube_128_eq, cube_128_eq, ← pow_mul]; congr 1

lemma cube_512_eq [NeZero N_val] (x : LucasRing N_val D_val) : cube_512 x = x ^ (3 ^ 512) := by
  unfold cube_512; rw [cube_256_eq, cube_256_eq, ← pow_mul]; congr 1

lemma cube_1024_eq [NeZero N_val] (x : LucasRing N_val D_val) : cube_1024 x = x ^ (3 ^ 1024) := by
  unfold cube_1024; rw [cube_512_eq, cube_512_eq, ← pow_mul]; congr 1

lemma cube_2048_eq [NeZero N_val] (x : LucasRing N_val D_val) : cube_2048 x = x ^ (3 ^ 2048) := by
  unfold cube_2048; rw [cube_1024_eq, cube_1024_eq, ← pow_mul]; congr 1

lemma cube_4096_eq [NeZero N_val] (x : LucasRing N_val D_val) : cube_4096 x = x ^ (3 ^ 4096) := by
  unfold cube_4096; rw [cube_2048_eq, cube_2048_eq, ← pow_mul]; congr 1

lemma cube_8192_eq [NeZero N_val] (x : LucasRing N_val D_val) : cube_8192 x = x ^ (3 ^ 8192) := by
  unfold cube_8192; rw [cube_4096_eq, cube_4096_eq, ← pow_mul]; congr 1

lemma cube_16384_eq [NeZero N_val] (x : LucasRing N_val D_val) : cube_16384 x = x ^ (3 ^ 16384) := by
  unfold cube_16384; rw [cube_8192_eq, cube_8192_eq, ← pow_mul]; congr 1

lemma cube_32768_eq [NeZero N_val] (x : LucasRing N_val D_val) : cube_32768 x = x ^ (3 ^ 32768) := by
  unfold cube_32768; rw [cube_16384_eq, cube_16384_eq, ← pow_mul]; congr 1

def cube_39101 (x : LucasRing N_val D_val) : LucasRing N_val D_val :=
  cube_1 (cube_4 (cube_8 (cube_16 (cube_32 (cube_128 (cube_2048 (cube_4096 (cube_32768 x))))))))

def cube_39100 (x : LucasRing N_val D_val) : LucasRing N_val D_val :=
  cube_4 (cube_8 (cube_16 (cube_32 (cube_128 (cube_2048 (cube_4096 (cube_32768 x)))))))

lemma cube_39101_eq [NeZero N_val] (x : LucasRing N_val D_val) : cube_39101 x = x ^ (3 ^ 39101) := by
  unfold cube_39101
  rw [cube_32768_eq, cube_4096_eq, cube_2048_eq, cube_128_eq, cube_32_eq, cube_16_eq, cube_8_eq, cube_4_eq, cube_1_eq]
  repeat rw [← pow_mul]
  congr 1

lemma cube_39100_eq [NeZero N_val] (x : LucasRing N_val D_val) : cube_39100 x = x ^ (3 ^ 39100) := by
  unfold cube_39100
  rw [cube_32768_eq, cube_4096_eq, cube_2048_eq, cube_128_eq, cube_32_eq, cube_16_eq, cube_8_eq, cube_4_eq]
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
    unfold N
    have h_pos : 2 * 100943 * 3 ^ 39101 > 0 := by
      have h_pow : 3 ^ 39101 > 0 := Nat.pow_pos (by decide)
      omega
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
    unfold N
    have h_pos : 2 * 100943 * 3 ^ 39101 > 0 := by
      have h_pow : 3 ^ 39101 > 0 := Nat.pow_pos (by decide)
      omega
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
    unfold N
    have h_pos : 2 * 100943 * 3 ^ 39101 > 0 := by
      have h_pow : 3 ^ 39101 > 0 := Nat.pow_pos (by decide)
      omega
    omega
  have h_div : 2 * 3 ^ 39101 = (N+1)/100943 := by
    rw [← h_eq]
    exact (Nat.mul_div_cancel (2 * 3 ^ 39101) (by decide)).symm
  rw [h_div]

lemma get_W_all_eq [NeZero p] (x : LucasRing p 5) : get_W_all x = x ^ (N+1) := by
  unfold get_W_all
  rw [get_W2_eq]
  have h_sq : x ^ ((N+1)/2) * x ^ ((N+1)/2) = x ^ (2 * ((N+1)/2)) := by
    rw [← pow_add]
    congr 1
    unfold N
    have h_pow : 3 ^ 39101 > 0 := Nat.pow_pos (by decide)
    omega
  rw [h_sq]
  congr 1
  unfold N
  have h_pow : 3 ^ 39101 > 0 := Nat.pow_pos (by decide)
  omega
"""

# Part 5: Complete custom replacement of Part 5 to prevent rfl errors on ZMod N
part5 = """
lemma get_W2_phi (p : ℕ) [Fact (Nat.Prime p)] (hp : p ∣ N) (x : LucasRing N 5) :
    get_W2 (phi p x) = phi p (get_W2 x) := by
  rw [get_W2_eq (phi p x), get_W2_eq x, ← phi_pow p hp]

lemma get_W3_phi (p : ℕ) [Fact (Nat.Prime p)] (hp : p ∣ N) (x : LucasRing N 5) :
    get_W3 (phi p x) = phi p (get_W3 x) := by
  rw [get_W3_eq (phi p x), get_W3_eq x, ← phi_pow p hp]

lemma get_W100943_phi (p : ℕ) [Fact (Nat.Prime p)] (hp : p ∣ N) (x : LucasRing N 5) :
    get_W100943 (phi p x) = phi p (get_W100943 x) := by
  rw [get_W100943_eq (phi p x), get_W100943_eq x, ← phi_pow p hp]

lemma get_W_all_phi (p : ℕ) [Fact (Nat.Prime p)] (hp : p ∣ N) (x : LucasRing N 5) :
    get_W_all (phi p x) = phi p (get_W_all x) := by
  rw [get_W_all_eq (phi p x), get_W_all_eq x, ← phi_pow p hp]

lemma orderOf_le_fintype_card {G : Type*} [Group G] [Fintype G] (x : G) :
    orderOf x ≤ Fintype.card G := by
  have h_card_eq : Nat.card G = Fintype.card G := Nat.card_eq_fintype_card
  have h_le := orderOf_le_card (x := x)
  rw [h_card_eq] at h_le
  exact h_le

lemma pow_eq_one_of_dvd_orderOf {G : Type*} [Group G] {x : G} {k : ℕ} (h : orderOf x ∣ k) : x ^ k = 1 := by
  rcases h with ⟨m, rfl⟩
  rw [pow_mul, pow_orderOf_eq_one, one_pow]

lemma card_ge_of_witness {G : Type*} [Group G] [Fintype G] (x : G) (M : ℕ) (hM : x ^ M = 1) (hM_pos : M > 0)
    (h2 : x ^ (M / 2) ≠ 1)
    (h3 : x ^ (M / 3) ≠ 1)
    (h100943 : x ^ (M / 100943) ≠ 1)
    (h_factors : ∀ q : ℕ, q.Prime → q ∣ M → q = 2 ∨ q = 3 ∨ q = 100943) :
    M ≤ Fintype.card G := by
  have hd : orderOf x ∣ M := orderOf_dvd_of_pow_eq_one hM
  rcases hd with ⟨k, rfl⟩
  by_cases hk1 : k = 1
  · subst hk1
    simp only [mul_one]
    exact orderOf_le_fintype_card x
  · have hk_ne_zero : k ≠ 0 := by
      intro hk0
      subst hk0
      rw [mul_zero] at hM_pos
      omega
    have hk_gt_one : k > 1 := by omega
    have hk_prime_factor : ∃ q : ℕ, q.Prime ∧ q ∣ k := Nat.exists_prime_and_dvd hk_gt_one.ne'
    rcases hk_prime_factor with ⟨q, hq_prime, hq_dvd⟩
    have hq_dvd_M : q ∣ (orderOf x * k) := dvd_mul_of_dvd_right hq_dvd (orderOf x)
    have hq_eq := h_factors q hq_prime hq_dvd_M
    have h_dvd_div : orderOf x ∣ (orderOf x * k / q) := by
      rcases hq_dvd with ⟨m, rfl⟩
      have hq_pos : q > 0 := hq_prime.pos
      have h_eq : orderOf x * (q * m) / q = orderOf x * m := by
        rw [mul_comm q m]
        rw [← mul_assoc]
        exact Nat.mul_div_cancel (orderOf x * m) hq_pos
      rw [h_eq]
      exact dvd_mul_right (orderOf x) m
    have h_pow_eq_one : x ^ (orderOf x * k / q) = 1 := pow_eq_one_of_dvd_orderOf h_dvd_div
    rcases hq_eq with rfl | rfl | rfl
    · contradiction
    · contradiction
    · contradiction
"""

# Part 6: test_proof.lean lines 662 to 881 (1-based index 662 to 881: 0-based 661 to 881)
part6 = "".join(test_proof_lines[661:881])

# Optimize prime_factors_of_N_plus_one, bar_alpha_card_bound, prime_proof, prime_39101
part6 = part6.replace("have h_pos : 2 * 100943 * 3 ^ 39101 > 0 := by decide", """have h_pos : 2 * 100943 * 3 ^ 39101 > 0 := by
      have h_pow : 3 ^ 39101 > 0 := Nat.pow_pos (by decide)
      omega""")

part6 = part6.replace("have hM_pos : N + 1 > 0 := by decide", """have hM_pos : N + 1 > 0 := by
    unfold N
    have h_pow : 3 ^ 39101 > 0 := Nat.pow_pos (by decide)
    omega""")

part6 = part6.replace("have h_ge : N ≥ 3 := by decide", """have h_ge : N ≥ 3 := by
    unfold N
    have h_pow : 3 ^ 39101 > 0 := Nat.pow_pos (by decide)
    omega""")

part6 = part6.replace("have h_odd : N % 2 = 1 := by decide", """have h_odd : N % 2 = 1 := by
    unfold N
    have h_pow : 3 ^ 39101 > 0 := Nat.pow_pos (by decide)
    have h_eq : 2 * 100943 * 3 ^ 39101 - 1 = 2 * (100943 * 3 ^ 39101 - 1) + 1 := by omega
    rw [h_eq]
    rw [Nat.add_mod]
    simp""")

part6 = part6.replace("have h_gt : N > 1 := by decide", """have h_gt : N > 1 := by
    unfold N
    have h_pow : 3 ^ 39101 > 0 := Nat.pow_pos (by decide)
    omega""")

# Correct the Nat.mul_mod call by passing 2
part6 = part6.replace("have h_mul_mod := Nat.mul_mod p k", "have h_mul_mod := Nat.mul_mod p k 2")

# Correct the Fact.out.pos to Nat.Prime.pos Fact.out
part6 = part6.replace("have h_p_pos : p > 0 := Fact.out.pos", "have h_p_pos : p > 0 := Nat.Prime.pos Fact.out")

# Correct the Nat.exists_prime_and_dvd argument in prime_of_prime_divisors_eq
part6 = part6.replace("have h_exists := Nat.exists_prime_and_dvd (by omega)", "have h_exists := Nat.exists_prime_and_dvd h_gt.ne'")


# Now insert noncomputable def a354747 right before the disproof theorem!
a354747_def = """
noncomputable def a354747 (n : ℕ) : ℕ :=
  let prime_steps : Set ℕ :=
    { m : ℕ | m > 0 ∧ Nat.Prime (2 * n * 3 ^ m - 1) }
  sInf prime_steps
"""

# Find where oeis_a354747_conjecture_0.disproof starts in part6 and insert before it
disproof_str = "theorem oeis_a354747_conjecture_0.disproof"
idx = part6.find(disproof_str)
if idx != -1:
    part6 = part6[:idx] + a354747_def + "\n" + part6[idx:]
else:
    print("Warning: disproof theorem not found in part6!")

# Replace by decide in heavy computation proofs to unfold N first
part6 = part6.replace("lemma alpha_norm_eq_one : alpha_const.re^2 - 5 * alpha_const.im^2 = 1 := by decide",
                      "lemma alpha_norm_eq_one : alpha_const.re^2 - 5 * alpha_const.im^2 = 1 := by\\n  unfold N\\n  decide")

part6 = part6.replace("lemma W2_invertible : (get_W2 alpha_const - 1) * v2_const = 1 := by decide",
                      "lemma W2_invertible : (get_W2 alpha_const - 1) * v2_const = 1 := by\\n  unfold N\\n  decide")

part6 = part6.replace("lemma W3_invertible : (get_W3 alpha_const - 1) * v3_const = 1 := by decide",
                      "lemma W3_invertible : (get_W3 alpha_const - 1) * v3_const = 1 := by\\n  unfold N\\n  decide")

part6 = part6.replace("lemma W100943_invertible : (get_W100943 alpha_const - 1) * v100943_const = 1 := by decide",
                      "lemma W100943_invertible : (get_W100943 alpha_const - 1) * v100943_const = 1 := by\\n  unfold N\\n  decide")

part6 = part6.replace("lemma W_all_eq_one : get_W_all alpha_const = 1 := by decide",
                      "lemma W_all_eq_one : get_W_all alpha_const = 1 := by\\n  unfold N\\n  decide")

# Fix the change failure in bar_alpha_pow_N_plus_one etc by using rw [u1_pow_val]
part6 = part6.replace("  change (phi p alpha_const) ^ (N+1) = 1", "  rw [u1_pow_val]")
part6 = part6.replace("  change (phi p alpha_const) ^ ((N+1)/2) = 1 at h_val_sub", "  rw [u1_pow_val] at h_val_sub")
part6 = part6.replace("  change (phi p alpha_const) ^ ((N+1)/3) = 1 at h_val_sub", "  rw [u1_pow_val] at h_val_sub")
part6 = part6.replace("  change (phi p alpha_const) ^ ((N+1)/100943) = 1 at h_val_sub", "  rw [u1_pow_val] at h_val_sub")


final_code = part1 + part2 + part3 + part4 + part5 + part6

with open("/workspace/leanproject/Submission/Spec.lean", "w") as f:
    f.write(final_code)

print("Spec.lean successfully fully assembled!")
