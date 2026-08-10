import sys

# We will generate a partitioned proof up to 5000 in Spec.lean, using chunks of size 50.
# We also keep the original definitions and lemmas from Spec.lean.

with open("/workspace/leanproject/Submission/Spec.lean", "r") as f:
    orig_lines = f.readlines()

# Let's keep the first 208 lines of Spec.lean (up to lemma no_sol definition).
orig_spec = "".join(orig_lines[:208])

# Let's append our partitioned lemmas.
out = []
out.append(orig_spec)
out.append("\n-- Bounded partition lemmas to avoid stack/memory overflows\n")

chunk_size = 50
max_val = 5000

for i in range(0, max_val, chunk_size):
    start = i
    end = i + chunk_size
    out.append(f"lemma no_sol_{start}_{end} : ∀ x < {end}, x ≥ {start} → x ≠ 0 → (sigma 1 x) % x ≠ 5 := by decide\n")

# Now we write the master bounded lemma
out.append(f"\nlemma no_sol_bounded (x : ℕ) (hx : x ≠ 0) (h_lt : x < {max_val}) : (sigma 1 x) % x ≠ 5 := by\n")
for i in range(0, max_val, chunk_size):
    start = i
    end = i + chunk_size
    if i == max_val - chunk_size:
        out.append(f"  have h_ge : x ≥ {start} := by omega\n")
        out.append(f"  exact no_sol_{start}_{end} x h_lt h_ge hx\n")
    else:
        out.append(f"  by_cases h{end} : x < {end}\n")
        if start == 0:
            out.append(f"  · exact no_sol_{start}_{end} x h{end} hx\n")
        else:
            out.append(f"  · have h_ge : x ≥ {start} := by omega\n")
            out.append(f"    exact no_sol_{start}_{end} x h{end} h_ge hx\n")
        out.append(f"  · -- case x >= {end}\n")

# Close the master bounded lemma
out.append(" " * (2 * (max_val // chunk_size)) + "omega\n") # This is just a fallback, should never be reached since x < max_val

# Now we rewrite the no_sol lemma
out.append("""
lemma no_sol (x : ℕ) (hx : x ≠ 0) : (sigma 1 x) % x ≠ 5 := by
  by_cases h_lt : x < 5000
  · exact no_sol_bounded x hx h_lt
  · -- x ≥ 5000
    intro h_mod
    have hx_ge : x ≥ 5 := by omega
    have h_div : sigma 1 x = x * (sigma 1 x / x) + 5 := by
      have h1 : sigma 1 x = x * (sigma 1 x / x) + (sigma 1 x) % x := (Nat.div_add_mod (sigma 1 x) x).symm
      rw [h_mod] at h1
      exact h1
    by_cases hk1 : sigma 1 x / x = 1
    · have h_sig : sigma 1 x = x + 5 := by
        rw [h_div, hk1]
        ring
      exact sigma_eq_x_add_5_contradiction x hx_ge h_sig
    · by_cases hk0 : sigma 1 x / x = 0
      · have h_sig : sigma 1 x = 5 := by
          rw [h_div, hk0]
          ring
        have h_decomp := divisors_decomp x hx_ge
        rw [← sigma_one_apply] at h_decomp
        have h_ge_six : sigma 1 x ≥ 6 := by omega
        omega
      · generalize hk : sigma 1 x / x = k at h_div hk1 hk0 ⊢
        have hk2 : k ≥ 2 := by omega
        by_cases h_def : sigma 1 x < 2 * x
        · exact deficient_no_sol x hx h_mod h_def
        · -- sigma 1 x ≥ 2 * x, meaning x is abundant/perfect
          -- Since we know x ≥ 5000, let's see if we can get a contradiction
          sorry
""")

# Re-append oeis_76495_conjecture_0
out.append("""
theorem oeis_76495_conjecture_0 : A076495 5 = 0 := by
  unfold A076495
  rw [Nat.sInf_eq_zero]
  right
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
  intro h
  exact no_sol x h.1 h.2
""")

with open("/workspace/leanproject/Submission/Spec.lean", "w") as f:
    f.writelines(out)
print("Spec.lean updated successfully.")
