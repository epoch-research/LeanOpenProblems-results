def main():
    # 1.2 million hex characters is 300,000 bytes.
    # Let's generate a string of 1.2 million 'a's
    hnat = "a" * 1200000
    
    code = []
    code.append("import FormalConjectures.Util.ProblemImports")
    code.append("")
    code.append(f"def huge_nat_test : Nat := 0x{hnat}")
    code.append("")
    code.append("theorem test_huge : huge_nat_test > 0 := by")
    code.append("  decide")
    code.append("")

    with open("/workspace/leanproject/Submission/TestNatSpeed.lean", "w") as f:
        f.write("\n".join(code))
    print("Generated TestNatSpeed.lean!")

if __name__ == "__main__":
    main()
