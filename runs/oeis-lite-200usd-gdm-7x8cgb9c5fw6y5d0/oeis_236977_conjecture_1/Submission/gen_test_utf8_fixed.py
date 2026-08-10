def main():
    s = "a" * 1000000 + "b"
    code = []
    code.append("import FormalConjectures.Util.ProblemImports")
    code.append("")
    code.append(f'def s : String := "{s}"')
    code.append("")
    code.append("theorem test_utf8 : s.get ⟨1000000⟩ = 'b' := by")
    code.append("  decide")
    code.append("")

    with open("/workspace/leanproject/Submission/TestUTF8Speed.lean", "w") as f:
        f.write("\n".join(code))
    print("Generated TestUTF8Speed.lean!")

if __name__ == "__main__":
    main()
