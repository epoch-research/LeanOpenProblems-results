def main():
    arr = [i for i in range(10000)]
    arr_str = ", ".join(map(str, arr))
    code = []
    code.append("import FormalConjectures.Util.ProblemImports")
    code.append("")
    code.append(f"def arr : Array Nat := #[{arr_str}]")
    code.append("")
    code.append("theorem test : arr[5000]! = 5000 := by decide")
    code.append("")

    with open("/workspace/leanproject/Submission/TestArrayLiteral.lean", "w") as f:
        f.write("\n".join(code))
    print("Generated TestArrayLiteral.lean!")

if __name__ == "__main__":
    main()
