import os

def main():
    print("Reading witnesses.hex...")
    with open("/workspace/leanproject/Submission/witnesses.hex", "r") as f:
        hex_str = f.read().strip()
    print(f"Read {len(hex_str)} characters of hex string.")

    witnesses = [int(hex_str[i:i+4], 16) for i in range(0, len(hex_str), 4)]
    print(f"Total witnesses: {len(witnesses)}")

    chunk_size = 12500
    chunks = []
    for i in range(0, len(witnesses), chunk_size):
        chunks.append(witnesses[i:i+chunk_size])
    print(f"Divided into {len(chunks)} chunks.")

    huge_nats = []
    for chunk in chunks:
        val = 0
        for i, w in enumerate(chunk):
            val |= (int(w) & 0xFFFF) << (16 * i)
        huge_nats.append(f"0x{val:x}")

    code = []
    code.append("import FormalConjectures.Util.ProblemImports")
    code.append("")
    code.append("open Nat")
    code.append("")

    for i, hnat in enumerate(huge_nats):
        code.append(f"def huge_nat_{i} : Nat := {hnat}")
        code.append("")

    # Add a test theorem to check lookup
    code.append(f"theorem test_lookup : (shiftRight huge_nat_0 0) % 65536 = {witnesses[0]} := by decide")
    code.append(f"theorem test_lookup_end : (shiftRight huge_nat_95 (16 * 12493)) % 65536 = {witnesses[-1]} := by decide")

    with open("/workspace/leanproject/Submission/test_96_actual.lean", "w") as f:
        f.write("\n".join(code))
    print("test_96_actual.lean written successfully!")

if __name__ == "__main__":
    main()
