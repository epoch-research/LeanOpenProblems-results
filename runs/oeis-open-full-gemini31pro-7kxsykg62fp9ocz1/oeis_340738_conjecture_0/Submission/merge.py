import re

files = [
    "Helper.lean",
    "Helper2.lean",
    "Helper_mono.lean",
    "Helper4.lean",
    "Helper5.lean",
    "Helper6.lean",
    "Helper7.lean",
    "Helper8.lean",
    "Helper9.lean",
    "Helper10.lean",
    "Helper11.lean",
    "Helper12.lean",
    "Helper13.lean",
    "Helper14.lean",
    "Proof.lean"
]

seen_lemmas = set()
out = []

for f in files:
    with open(f"Submission/{f}") as fp:
        content = fp.read()
    
    lines = content.split('\n')
    current_decl = []
    decl_name = None
    
    for line in lines:
        if line.startswith("import ") or line.startswith("open "):
            continue
        
        m = re.match(r'^(?:lemma|def|theorem|noncomputable def)\s+([a-zA-Z0-9_]+)', line)
        if m:
            if decl_name and decl_name not in seen_lemmas:
                out.append('\n'.join(current_decl))
                seen_lemmas.add(decl_name)
            
            decl_name = m.group(1)
            current_decl = [line]
        else:
            if decl_name is not None:
                current_decl.append(line)
    
    if decl_name and decl_name not in seen_lemmas:
        out.append('\n'.join(current_decl))
        seen_lemmas.add(decl_name)

with open("Submission/Spec.lean.orig") as fp:
    spec_content = fp.read()

spec_content = re.sub(r'#eval .*', '', spec_content)

idx = spec_content.find("/-- oeis_340738_conjecture_0")
if idx == -1:
    idx = spec_content.find("theorem oeis_340738_conjecture_0")

new_spec = spec_content[:idx] + "\nopen Polynomial intervalIntegral Filter Topology Set Metric Real Nat\n\n" + "\n\n".join(out) + "\n\n" + spec_content[idx:]

new_spec = new_spec.replace(
    "theorem oeis_340738_conjecture_0 :\n  Tendsto sequence_of_fractions atTop (nhds (Real.exp 1)) :=\nby sorry",
    "theorem oeis_340738_conjecture_0 :\n  Tendsto sequence_of_fractions atTop (nhds (Real.exp 1)) := by\n  exact sequence_of_fractions_converges\n"
)

with open("Submission/Spec.lean", "w") as fp:
    fp.write(new_spec)
