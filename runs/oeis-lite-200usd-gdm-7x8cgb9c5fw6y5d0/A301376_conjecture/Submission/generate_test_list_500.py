lines = [
    "import FormalConjectures.Util.ProblemImports",
    "",
    "def blocking_primes_list : List (ℕ × ℕ) := ["
]

for i in range(1, 500):
    lines.append(f"  ({i}, 3),")

lines.append("  (500, 3)")
lines.append("]\n")

with open("Submission/TestMatch.lean", "w") as f:
    f.write("\n".join(row for row in lines))

print("Wrote TestMatch.lean")
