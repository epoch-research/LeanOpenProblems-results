import sympy

def generate_mod_lemmas_lean():
    moduli = [3, 4, 5, 7, 8, 11, 13, 17, 19, 23, 29, 31, 37, 53]
    out = []
    for m in moduli:
        # Generate quadratic non-residues for m
        qr = set((x*x)%m for x in range(m))
        non_qr = sorted([r for r in range(m) if r not in qr])
        
        # We want to write a lemma of the form:
        # theorem not_is_square_mod_m (x : ℕ) (h : x % m = r1 ∨ x % m = r2 ∨ ...) : ¬ IsSquare x
        disj_terms = " ∨ ".join(f"x % {m} = {r}" for r in non_qr)
        
        out.append(f"theorem not_isSquare_mod_{m} (x : ℕ) (h : {disj_terms}) : ¬ IsSquare x := by")
        out.append("  intro hsq")
        out.append("  rcases hsq with ⟨y, rfl⟩")
        out.append(f"  rw [Nat.mul_mod] at h")
        out.append(f"  have h1 : y % {m} < {m} := Nat.mod_lt y (by decide)")
        out.append(f"  interval_cases y % {m}")
        for r in range(m):
            out.append(f"  · revert h; decide")
        out.append("")
    return "\n".join(out)

print(generate_mod_lemmas_lean()[:1000])
