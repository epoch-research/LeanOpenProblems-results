import subprocess

# Generate 6401 cases
lines = [
    "import FormalConjectures.Util.ProblemImports",
    "",
    "def blocking_prime (v : ℕ) : ℕ :=",
    "  match v with"
]

for i in range(1, 6402):
    lines.append(f"  | {i} => 3")

lines.append("  | _ => 3\n")

with open("Submission/TestMatch.lean", "w") as f:
    f.write("\n".join(row for row in lines))

print("Wrote TestMatch.lean")
