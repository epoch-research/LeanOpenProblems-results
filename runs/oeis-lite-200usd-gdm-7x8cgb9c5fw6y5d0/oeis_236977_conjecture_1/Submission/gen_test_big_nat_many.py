def main():
    code = []
    code.append("import FormalConjectures.Util.ProblemImports")
    code.append("")
    for i in range(240):
        hnat = "a" * 20000
        code.append(f"def huge_nat_{i} : Nat := 0x{hnat}")
    code.append("")
    code.append("theorem test_huge : huge_nat_0 > 0 := by decide")
    code.append("")

    with open("/workspace/leanproject/Submission/TestBigNatMany.lean", "w") as f:
        f.write("\n".join(code))
    print("Generated TestBigNatMany.lean!")

if __name__ == "__main__":
    main()
