def main():
    s = "a" * 1200000
    code = []
    code.append("import FormalConjectures.Util.ProblemImports")
    code.append("")
    code.append(f'def huge_string_test : String := "{s}"')
    code.append("")
    code.append("theorem test_huge : huge_string_test.length > 0 := by")
    code.append("  decide")
    code.append("")

    with open("/workspace/leanproject/Submission/TestStringSpeed.lean", "w") as f:
        f.write("\n".join(code))
    print("Generated TestStringSpeed.lean!")

if __name__ == "__main__":
    main()
