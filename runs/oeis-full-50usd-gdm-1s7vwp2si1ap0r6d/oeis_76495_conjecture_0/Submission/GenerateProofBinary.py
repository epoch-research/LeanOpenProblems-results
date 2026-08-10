import sys

# We will generate a partitioned proof in Spec.lean, using chunks of size 50.
# We keep the original definitions and lemmas from Spec.lean up to lines 212.

with open("/workspace/leanproject/Submission/Spec.lean", "r") as f:
    orig_lines = f.readlines()

# Keep lines up to the start of bounded partition lemmas
# In our Spec.lean, the original content is up to line 212 (index 211).
# Let's find "-- Bounded partition lemmas" to be safe.
boundary_idx = -1
for i, line in enumerate(orig_lines):
    if "Bounded partition lemmas" in line:
        boundary_idx = i
        break

if boundary_idx == -1:
    print("Could not find boundary line.")
    boundary_idx = 212  # fallback

orig_spec = "".join(orig_lines[:boundary_idx])

out = []
out.append(orig_spec)
out.append("\n-- Bounded partition lemmas to avoid stack/memory overflows\n")

chunk_size = 5000000
max_val = 100000000  # Let's try 100000000

for i in range(0, max_val, chunk_size):
    start = i
    end = i + chunk_size
    if start == 0:
        out.append(f"lemma no_sol_{start}_{end} : ∀ x < {end}, x ≠ 0 → (sigma 1 x) % x ≠ 5 := by decide\n")
    else:
        out.append(f"lemma no_sol_{start}_{end} : ∀ x < {end}, x ≥ {start} → x ≠ 0 → (sigma 1 x) % x ≠ 5 := by decide\n")

# Now we write the binary tree generator for the master bounded lemma
out.append(f"\nlemma no_sol_bounded (x : ℕ) (hx : x ≠ 0) (h_lt : x < {max_val}) : (sigma 1 x) % x ≠ 5 := by\n")

num_chunks = max_val // chunk_size

def gen_tree(L, R, indent=2):
    ind = " " * indent
    if L == R:
        start = L * chunk_size
        end = (L + 1) * chunk_size
        out_lines = []
        out_lines.append(f"{ind}have h_lt_leaf : x < {end} := by omega\n")
        if L == 0:
            out_lines.append(f"{ind}exact no_sol_0_{end} x h_lt_leaf hx\n")
        else:
            out_lines.append(f"{ind}have h_ge_leaf : x ≥ {start} := by omega\n")
            out_lines.append(f"{ind}exact no_sol_{start}_{end} x h_lt_leaf h_ge_leaf hx\n")
        return "".join(out_lines)
    else:
        M = (L + R) // 2
        boundary = (M + 1) * chunk_size
        out_lines = []
        out_lines.append(f"{ind}by_cases h_lt_{boundary} : x < {boundary}\n")
        out_lines.append(f"{ind}· -- x < {boundary}\n")
        out_lines.append(gen_tree(L, M, indent + 2))
        out_lines.append(f"{ind}· -- x ≥ {boundary}\n")
        out_lines.append(gen_tree(M + 1, R, indent + 2))
        return "".join(out_lines)

out.append(gen_tree(0, num_chunks - 1))

# Now we rewrite the no_sol lemma
out.append(f"""
lemma no_sol (x : ℕ) (hx : x ≠ 0) : (sigma 1 x) % x ≠ 5 := by
  by_cases h_lt : x < {max_val}
  · exact no_sol_bounded x hx h_lt
  · -- x ≥ {max_val}
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
          -- Since we know x ≥ {max_val}, let's see if we can get a contradiction
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
print("Spec.lean updated successfully with binary tree.")
