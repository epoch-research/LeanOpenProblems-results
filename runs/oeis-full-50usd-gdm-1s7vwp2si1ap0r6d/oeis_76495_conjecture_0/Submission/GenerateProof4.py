import sys

# We will generate a partitioned proof up to 5000 in Spec.lean, using chunks of size 50.
# We also keep the original definitions and lemmas from Spec.lean.

with open("/workspace/leanproject/Submission/Spec.lean", "r") as f:
    orig_lines = f.readlines()

# Let's find the line that starts with 'import' in the original Spec.lean.
# Wait, in GenerateProof3.py, the first line of the file became 'set_option...'.
# So the original Spec.lean has 'set_option' on the first two lines, and then 'import...' on line 3 or 4.
# Let's find 'import' first.
import_idx = -1
for i, line in enumerate(orig_lines):
    if line.strip().startswith("import "):
        import_idx = i
        break

if import_idx == -1:
    print("Could not find import line.")
    sys.exit(1)

# The import statement and other initial commands
import_line = orig_lines[import_idx]

# Let's keep the lines of the original spec after the import statement
# we can just use the indices of the original spec.
# Wait, the first 208 lines of the original spec:
# Since GenerateProof3.py added 4 lines at the top, the original 208 lines are now at 212.
# Let's find the originalSpec by searching for 'lemma no_sol' in orig_lines.
no_sol_idx = -1
for i, line in enumerate(orig_lines):
    if "lemma no_sol " in line:
        no_sol_idx = i
        break

if no_sol_idx == -1:
    print("Could not find lemma no_sol line.")
    sys.exit(1)

# Now we construct the new spec lines.
out = []
out.append(import_line)
out.append("set_option maxRecDepth 10000000\nset_option maxHeartbeats 10000000\n\n")

# Append everything from import_idx + 1 to no_sol_idx
for i in range(import_idx + 1, no_sol_idx):
    # skip any set_option lines that got duplicated
    if orig_lines[i].strip().startswith("set_option "):
        continue
    out.append(orig_lines[i])

out.append("\n-- Bounded partition lemmas to avoid stack/memory overflows\n")

chunk_size = 50
max_val = 5000

for i in range(0, max_val, chunk_size):
    start = i
    end = i + chunk_size
    if start == 0:
        out.append(f"lemma no_sol_{start}_{end} : ∀ x < {end}, x ≠ 0 → (sigma 1 x) % x ≠ 5 := by decide\n")
    else:
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
