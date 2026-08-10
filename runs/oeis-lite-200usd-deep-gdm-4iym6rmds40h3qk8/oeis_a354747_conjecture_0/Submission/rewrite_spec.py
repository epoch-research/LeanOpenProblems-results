with open("/workspace/leanproject/Submission/output_vals.txt", "r") as f:
    flattened_defs = f.read()

with open("/workspace/leanproject/Submission/Spec.lean", "r") as f:
    content = f.read()

# Replace get_W2_eq etc by removing the extra "rfl"
content = content.replace(
    "  rw [← pow_mul]\n  congr 1\n  rfl",
    "  rw [← pow_mul]\n  congr 1"
)

# Replace the phi lemmas
content = content.replace(
    "lemma get_W2_phi (p : ℕ) [Fact (Nat.Prime p)] (hp : p ∣ N) (x : LucasRing N 5) :\n    get_W2 (phi p x) = phi p (get_W2 x) := by\n  rw [get_W2_eq, ← phi_pow p hp]",
    "lemma get_W2_phi (p : ℕ) [Fact (Nat.Prime p)] (hp : p ∣ N) (x : LucasRing N 5) :\n    get_W2 (phi p x) = phi p (get_W2 x) := by\n  rw [get_W2_eq (phi p x), get_W2_eq x, ← phi_pow p hp]"
)

content = content.replace(
    "lemma get_W3_phi (p : ℕ) [Fact (Nat.Prime p)] (hp : p ∣ N) (x : LucasRing N 5) :\n    get_W3 (phi p x) = phi p (get_W3 x) := by\n  rw [get_W3_eq, ← phi_pow p hp]",
    "lemma get_W3_phi (p : ℕ) [Fact (Nat.Prime p)] (hp : p ∣ N) (x : LucasRing N 5) :\n    get_W3 (phi p x) = phi p (get_W3 x) := by\n  rw [get_W3_eq (phi p x), get_W3_eq x, ← phi_pow p hp]"
)

content = content.replace(
    "lemma get_W100943_phi (p : ℕ) [Fact (Nat.Prime p)] (hp : p ∣ N) (x : LucasRing N 5) :\n    get_W100943 (phi p x) = phi p (get_W100943 x) := by\n  rw [get_W100943_eq, ← phi_pow p hp]",
    "lemma get_W100943_phi (p : ℕ) [Fact (Nat.Prime p)] (hp : p ∣ N) (x : LucasRing N 5) :\n    get_W100943 (phi p x) = phi p (get_W100943 x) := by\n  rw [get_W100943_eq (phi p x), get_W100943_eq x, ← phi_pow p hp]"
)

content = content.replace(
    "lemma get_W_all_phi (p : ℕ) [Fact (Nat.Prime p)] (hp : p ∣ N) (x : LucasRing N 5) :\n    get_W_all (phi p x) = phi p (get_W_all x) := by\n  rw [get_W_all_eq, ← phi_pow p hp]",
    "lemma get_W_all_phi (p : ℕ) [Fact (Nat.Prime p)] (hp : p ∣ N) (x : LucasRing N 5) :\n    get_W_all (phi p x) = phi p (get_W_all x) := by\n  rw [get_W_all_eq (phi p x), get_W_all_eq x, ← phi_pow p hp]"
)

# Now, find the block of lines to remove.
# The block starts at "def alpha_re_val_nat_nat_0" and ends before "def alpha_re_val : ZMod N"
start_marker = "def alpha_re_val_nat_nat_0"
end_marker = "def alpha_re_val : ZMod N"

start_idx = content.find(start_marker)
end_idx = content.find(end_marker)

if start_idx == -1 or end_idx == -1:
    print("Error: markers not found")
    sys.exit(1)

new_content = content[:start_idx] + flattened_defs + "\n" + content[end_idx:]

with open("/workspace/leanproject/Submission/Spec.lean", "w") as f:
    f.write(new_content)

print("Spec.lean successfully rewritten!")
