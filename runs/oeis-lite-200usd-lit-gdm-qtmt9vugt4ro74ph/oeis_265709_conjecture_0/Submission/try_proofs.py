import subprocess

path = "/workspace/leanproject/Submission/Spec.lean"
with open(path, "r") as f:
    orig_content = f.read()

# We will replace "      sorry" on line 1961 with our candidate proof.
sorry_str = "      sorry"

candidates = [
    # Candidate 1: Pure 2-adic valuation contradiction using padicValRat_two_sum_divisors_odd_le
    """      have h_val_neg : padicValRat 2 q2 < 0 := hm_val
      have h_val_q1_pos : padicValRat 2 q1 ≥ 1 := h_odd_val
      -- Since padicValRat 2 q2 ≤ - (padicValNat 2 (p + 1) : ℤ), and padicValNat 2 (p + 1) ≥ 1:
      -- We want to see if we can get a contradiction by showing val2(q1 * q2) < 0
      -- But we only have val2(q1 * q2) = val2(q1) + val2(q2) ≥ 0, which doesn't directly contradict.
      -- Let's try to prove False by using the fact that q1 * q2 is an integer, so q2.den ∣ q1.num.natAbs.
      -- If q2.den ∣ q1.num.natAbs, then padicValNat 2 q2.den ≤ padicValNat 2 q1.num.natAbs.
      -- Since q1.den is odd, padicValNat 2 q1.num.natAbs = padicValRat 2 q1.
      -- And (padicValNat 2 q2.den : ℤ) ≥ - padicValRat 2 q2.
      -- So padicValRat 2 q1 ≥ - padicValRat 2 q2.
      -- Since padicValRat 2 q2 ≤ - (padicValNat 2 (p + 1) : ℤ), we have - padicValRat 2 q2 ≥ padicValNat 2 (p + 1).
      -- So padicValRat 2 q1 ≥ padicValNat 2 (p + 1).
      -- If we can show that padicValRat 2 q1 < padicValNat 2 (p + 1) for some cases?
      -- Since we don't have this, let's try a size contradiction on q2.
      have h_cop_den : q1.den.Coprime q2.den := coprime_den q1 q2 hq1_pos h_den_q
      have hd21 : q2.den ∣ q1.num.natAbs := by
        have h_dvd : (q2.den : ℤ) ∣ q1.num := rat_mul_int_dvd q1 q2 h_den_q
        have h_eq : q1.num = (q1.num.natAbs : ℤ) := (Int.natAbs_of_nonneg (le_of_lt hq1_pos)).symm
        rw [h_eq] at h_dvd
        exact_mod_cast h_dvd
      have hd12 : q1.den ∣ q2.num.natAbs := by
        have h_dvd : (q1.den : ℤ) ∣ q2.num := rat_mul_int_dvd_left q1 q2 h_den_q
        have h_eq : q2.num = (q2.num.natAbs : ℤ) := (Int.natAbs_of_nonneg (le_of_lt hq2_pos)).symm
        rw [h_eq] at h_dvd
        exact_mod_cast h_dvd
      -- Since q2.den is even (2 | q2.den) and q1.den is odd (¬ 2 | q1.den):
      have h_q2_den_even : 2 ∣ q2.den := even_den_of_padicValRat_neg 2 q2 hm_val
      have h_val_q1_ge : padicValRat 2 q1 ≥ 0 := by omega
      have h_q1_den_zero : padicValNat 2 q1.den = 0 := den_odd_of_val_nonneg q1 h_val_q1_ge
      have h_q1_den_odd : ¬ 2 ∣ q1.den := by
        intro h_dvd
        have : 1 ≤ padicValNat 2 q1.den := one_le_padicValNat_of_dvd (by positivity) h_dvd
        omega
      -- Since q1 * q2 is an integer, let's write q1 * q2 = B_int * A_int
      -- We will use coprime_den and divisibility to show a contradiction.
      -- Let's try to use linarith or omega on valuations.
      have h_val_sum : padicValRat 2 q1 + padicValRat 2 q2 ≥ 0 := by omega
      have h_val_le : padicValRat 2 q2 ≤ - (padicValNat 2 (p + 1) : ℤ) := h_q2_val_le
      have h_val_q1_val : (padicValNat 2 q1.num.natAbs : ℤ) = padicValRat 2 q1 := by
        have h_def : padicValRat 2 q1 = padicValInt 2 q1.num - padicValNat 2 q1.den := padicValRat_def 2 q1
        have h_cast : padicValInt 2 q1.num = padicValNat 2 q1.num.natAbs := rfl
        rw [h_cast, h_q1_den_zero] at h_def
        omega
      have h_val_q2_val : (padicValNat 2 q2.den : ℤ) ≥ - padicValRat 2 q2 := by
        have h_def : padicValRat 2 q2 = padicValInt 2 q2.num - padicValNat 2 q2.den := padicValRat_def 2 q2
        have h_num_ge : (padicValInt 2 q2.num : ℤ) ≥ 0 := Int.ofNat_nonneg _
        omega
      have h_val_dvd_ge : padicValNat 2 q1.num.natAbs ≥ padicValNat 2 q2.den := by
        have h_nz : q1.num.natAbs ≠ 0 := by
          have : q1.num > 0 := hq1_pos
          omega
        exact padicValNat_le_of_dvd h_nz hd21
      have hp_val_ge_1 : (padicValNat 2 (p + 1) : ℤ) ≥ 1 := hp_val_ge
      -- Let's check if we can get a contradiction if padicValRat 2 q1 < padicValNat 2 (p+1)
      -- Wait, can we prove that padicValRat 2 q1 is actually bounded?
      -- If b = 1, padicValRat 2 q1 = 2.
      -- If b ≥ 3:
      -- Let's see if we can prove False by showing that q2.den and q2.num are both even if A_int = 2
      -- If q1 * q2 = B_int * A_int:
      -- We don't have B_int and A_int explicitly, but we can define them.
      let B_int := q1.num.natAbs / q2.den
      let A_int := q2.num.natAbs / q1.den
      have h_q1_num : q1.num.natAbs = B_int * q2.den := (Nat.div_mul_cancel hd21).symm
      have h_q2_num : q2.num.natAbs = A_int * q1.den := (Nat.div_mul_cancel hd12).symm
      -- If A_int * B_int = q1 * q2:
      -- Since q1 < 2 and q2 < 2 (if we can prove it)
      -- Let's see if we can use g_mul_of_coprime or coprime_den.
      have h_gcd : Nat.gcd q2.num.natAbs q2.den = 1 := q2.reduced
      -- If we can show that 2 divides both q2.num.natAbs and q2.den:
      -- We know 2 | q2.den (h_q2_den_even).
      -- If we can show 2 | q2.num.natAbs:
      -- Since q2.num.natAbs = A_int * q1.den.
      -- Since q1.den is odd, 2 ∣ q2.num.natAbs iff 2 ∣ A_int.
      -- So if A_int is even, we get a contradiction!
      -- When is A_int even?
      -- Since B_int * A_int = q1 * q2.
      -- If B_int * A_int is even, and B_int is odd, then A_int is even.
      -- Or we can do a cases on A_int % 2.
      rcases Nat.mod_two_eq_zero_or_one A_int with hA_even | hA_odd
      · -- A_int is even, so 2 | A_int
        have h_dvd_num : 2 ∣ q2.num.natAbs := by
          rw [h_q2_num]
          exact dvd_mul_of_dvd_left hA_even q1.den
        have h_dvd_gcd : 2 ∣ Nat.gcd q2.num.natAbs q2.den := Nat.dvd_gcd h_dvd_num h_q2_den_even
        rw [h_gcd] at h_dvd_gcd
        have : 2 ≤ 1 := Nat.le_of_dvd (by decide) h_dvd_gcd
        omega
      · -- A_int is odd.
        -- If A_int is odd, and B_int * A_int = q1 * q2.
        -- Let's show a contradiction if B_int = 1 or something.
        -- Since A_int is odd, and q2.num.natAbs = A_int * q1.den.
        -- Since q1.den is odd, q2.num.natAbs is odd.
        -- So padicValInt 2 q2.num = 0.
        -- So padicValRat 2 q2 = - padicValNat 2 q2.den.
        -- So padicValNat 2 q2.den ≤ padicValRat 2 q1 (since h_val_sum : val2(q1) + val2(q2) ≥ 0).
        -- Since padicValNat 2 q2.den = padicValNat 2 q1.num.natAbs - padicValNat 2 B_int.
        -- We must have padicValNat 2 B_int = padicValRat 2 q1 + padicValRat 2 q2.
        -- Since val2(q1 * q2) = val2(q1) + val2(q2) ≥ 0.
        -- So padicValNat 2 B_int = padicValRat 2 (q1 * q2).
        -- If we can show that B_int must be a power of 2?
        -- No, let's try to get a contradiction by size or valuation.
        sorry
"""
]

for i, cand in enumerate(candidates):
    print(f"Trying Candidate {i+1}...")
    temp_content = orig_content.replace(sorry_str, cand)
    with open(path, "w") as f:
        f.write(temp_content)
    
    # Run Lean compiler
    res = subprocess.run(["lake", "env", "lean", path], capture_output=True, text=True)
    if res.returncode == 0:
        print("Success! Candidate found.")
        # Check if there are any sorry left
        if "sorry" not in cand:
            print("Completed successfully with no sorry!")
            exit(0)
    else:
        print("Failed.")
        print(res.stdout)
        print(res.stderr)
        # print(res.stdout)
        # print(res.stderr)

# Restore original content
with open(path, "w") as f:
    f.write(orig_content)
