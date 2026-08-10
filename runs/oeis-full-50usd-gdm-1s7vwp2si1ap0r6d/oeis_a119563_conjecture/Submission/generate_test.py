import sys

sys.set_int_max_str_digits(20000)

val = 2**32768 + 32767
exp = 2**32768 + 32766
rhs = pow(3, exp, val)

with open("/workspace/leanproject/Submission/test_32768.lean", "w") as f:
    f.write("import Mathlib\n\n")
    f.write("set_option maxRecDepth 200000\n\n")
    f.write("def mod_pow_fuel (base : ℕ) (exp : ℕ) (modulus : ℕ) : ℕ :=\n")
    f.write("  let rec loop (fuel : ℕ) (acc : ℕ) (b : ℕ) (e : ℕ) : ℕ :=\n")
    f.write("    match fuel with\n")
    f.write("    | 0 => acc\n")
    f.write("    | fuel' + 1 =>\n")
    f.write("      if e = 0 then acc\n")
    f.write("      else\n")
    f.write("        let acc' := if e % 2 = 1 then (acc * b) % modulus else acc\n")
    f.write("        let b' := (b * b) % modulus\n")
    f.write("        let e' := e / 2\n")
    f.write("        loop fuel' acc' b' e'\n")
    f.write("  loop 33000 1 (base % modulus) exp\n\n")
    f.write(f"def val_32768 : ℕ := {val}\n\n")
    f.write(f"def exp_32768 : ℕ := {exp}\n\n")
    f.write(f"def rhs_32768 : ℕ := {rhs}\n\n")
    f.write("theorem test_32768 : mod_pow_fuel 3 exp_32768 val_32768 = rhs_32768 := by decide\n")
