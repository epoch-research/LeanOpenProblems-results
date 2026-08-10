import os
import subprocess

success_files = [
    "test_unsound_girard5.lean",
    "test_unsound_girard_prop_type.lean",
    "test_prop.lean",
    "test_unsound_2.lean",
    "test_unsound_5.lean",
    "test_unsound_6.lean",
    "test_loop.lean",
    "test_unsound_12.lean",
    "test_w.lean",
    "test_unsound_prop.lean",
    "test_bad2.lean",
    "test_unsound_eq.lean",
    "test_u_step.lean",
    "test_x_rec.lean",
    "test_mytype3.lean",
    "test_mytype4.lean",
    "test_mytype5.lean",
    "test_v.lean",
    "test_v_eq.lean",
    "test_unsound_decomp.lean",
    "test_set.lean",
    "test_bad_girard.lean",
    "test_cast_eq4.lean",
    "test_unsound_type0_distinct.lean",
    "test_hurkens_prop26.lean",
    "test_hurkens_prop27.lean",
    "test_x_partial.lean",
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
    "test_unsound_eq_prop.lean",
    "test_unsound_eq_prop6.lean",
    "test_unsound_eq_prop8.lean",
    "test_unsound_eq_prop9.lean",
    "test_unsound_eq_prop13.lean",
    "test_pure_girard3.lean",
    "test_pure_girard4.lean",
    "test_pure_girard11.lean",
    "test_hurkens_final_easy2.lean",
    "test_prop_retraction.lean"
]

for f in success_files:
    path = os.path.join("/workspace/leanproject/Submission", f)
    with open(path, 'r') as file:
        content = file.read()
    if "False" in content:
        # Check if there's any theorem or def proving False
        if "False" in content and "sorry" not in content:
            print(f"Candidate: {f}")
