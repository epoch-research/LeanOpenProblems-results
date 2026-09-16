import re

files = [
    "TestHugeSum3.lean",
    "TestHugeSum2.lean",
    "TestHugeSum6.lean",
    "TestHugeSum7.lean",
    "TestCommRing.lean",
    "TestIfEquiv.lean",
    "TestHugeSum14.lean",
    "TestHugeSum9.lean",
    "TestHugeSum12.lean",
    "Proof.lean",
    "Proof3.lean",
    "Proof2.lean",
    "TestHugeSum8.lean"
]

out = []
for f in files:
    with open("Submission/" + f) as file:
        content = file.read()
        # Remove imports
        content = re.sub(r"^import .*\n?", "", content, flags=re.MULTILINE)
        # Remove "open ..."
        content = re.sub(r"^open .*\n?", "", content, flags=re.MULTILINE)
        out.append(content)

with open("Submission/SpecMerged.lean", "w") as out_file:
    out_file.write("import FormalConjectures.Util.ProblemImports\n")
    out_file.write("open Finset Nat Polynomial MvPolynomial Finsupp\n")
    
    with open("Submission/Spec.lean") as s:
        spec_content = s.read()
        # Only take until oeis_2897_conjecture_0
        spec_head = spec_content.split("theorem oeis_2897_conjecture_0 (n : ℕ) :")[0]
        # Remove import and open
        spec_head = re.sub(r"^import .*\n?", "", spec_head, flags=re.MULTILINE)
        spec_head = re.sub(r"^open .*\n?", "", spec_head, flags=re.MULTILINE)
        out_file.write(spec_head)
        
    for o in out:
        out_file.write(o)
        out_file.write("\n")
        
    out_file.write("theorem oeis_2897_conjecture_0 (n : ℕ) :\n")
    out_file.write("  (a n : ℤ) = MvPolynomial.coeff (xyz_pow_n n) (P_n n) := by\n")
    out_file.write("  have h1 := small_sum2_eq_a n (small_sum2_simplified n) (drop_filter_sum n) (inner_sum_eval n) (sum_choose_square n)\n")
    out_file.write("  have h2 := my_small_sum2_eq_coeff_full n\n")
    out_file.write("  rw [← h1, h2]\n")
    out_file.write("\n")
    out_file.write("theorem oeis_2897_conjecture_0.disproof : ¬ (type_of% @oeis_2897_conjecture_0) := sorry\n")

