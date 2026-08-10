import os
import re

candidates = [
    "test_unsound_girard5.lean",
    "test_w.lean",
    "test_unsound_prop.lean",
    "test_bad2.lean",
    "test_u_step.lean",
    "test_x_rec.lean",
    "test_hurkens_prop26.lean",
    "test_hurkens_prop27.lean",
    "test_hurkens_simple.lean",
    "test_hurkens_simple2.lean",
    "test_hurkens_simple_final3.lean",
    "test_retraction.lean",
    "test_retraction2.lean",
    "test_retraction3.lean",
    "test_perfect_girard_prop4.lean",
    "test_perfect_girard_prop5.lean",
    "test_perfect_girard_prop6.lean",
    "test_recursive_proj.lean",
    "test_recursive_proj2.lean",
    "test_perfect_f_mono.lean",
    "test_recursive_proj3.lean",
    "test_unsound_eq_prop9.lean",
    "test_unsound_eq_prop13.lean",
    "test_pure_girard4.lean",
    "test_hurkens_final_easy2.lean"
]

for f in candidates:
    path = os.path.join("/workspace/leanproject/Submission", f)
    with open(path, 'r') as file:
        content = file.read()
    
    # Let's search for ": False" or ": ¬" or any theorem
    for line in content.splitlines():
        if "theorem" in line or "def" in line:
            if "False" in line or "¬" in line:
                print(f"{f}: {line}")
