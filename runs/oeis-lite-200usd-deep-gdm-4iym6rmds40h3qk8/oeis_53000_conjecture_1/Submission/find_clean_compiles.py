import subprocess
import os

files = [
    "/workspace/leanproject/Submission/test_unsound_girard5.lean",
    "/workspace/leanproject/Submission/test_unsound_girard_prop_type.lean",
    "/workspace/leanproject/Submission/test_prop.lean",
    "/workspace/leanproject/Submission/test_eval.lean",
    "/workspace/leanproject/Submission/test_print.lean",
    "/workspace/leanproject/Submission/test_unsound_2.lean",
    "/workspace/leanproject/Submission/test_unsound_5.lean",
    "/workspace/leanproject/Submission/test_unsound_6.lean",
    "/workspace/leanproject/Submission/test_print2.lean",
    "/workspace/leanproject/Submission/test_loop.lean",
    "/workspace/leanproject/Submission/test_type.lean",
    "/workspace/leanproject/Submission/test_unsound_12.lean",
    "/workspace/leanproject/Submission/test_loop_prop.lean",
    "/workspace/leanproject/Submission/test_w.lean",
    "/workspace/leanproject/Submission/test_unsound_eq.lean",
    "/workspace/leanproject/Submission/test_u_step.lean",
    "/workspace/leanproject/Submission/test_x_rec.lean",
    "/workspace/leanproject/Submission/test_mytype3.lean",
    "/workspace/leanproject/Submission/test_mytype4.lean",
    "/workspace/leanproject/Submission/test_mytype5.lean",
    "/workspace/leanproject/Submission/test_v.lean",
    "/workspace/leanproject/Submission/test_v_eq.lean",
    "/workspace/leanproject/Submission/test_unsound_decomp.lean",
    "/workspace/leanproject/Submission/test_set.lean",
    "/workspace/leanproject/Submission/test_type_plift.lean",
    "/workspace/leanproject/Submission/test_bad_girard.lean",
    "/workspace/leanproject/Submission/test_cast_eq4.lean",
    "/workspace/leanproject/Submission/test_unsound_type0_distinct.lean",
    "/workspace/leanproject/Submission/test_inj_perfect.lean",
    "/workspace/leanproject/Submission/test_hurkens_prop4.lean",
    "/workspace/leanproject/Submission/test_hurkens_prop8.lean",
    "/workspace/leanproject/Submission/test_hurkens_prop9.lean",
    "/workspace/leanproject/Submission/test_hurkens_prop10.lean",
    "/workspace/leanproject/Submission/test_hurkens_prop15.lean",
    "/workspace/leanproject/Submission/test_hurkens_prop16.lean",
    "/workspace/leanproject/Submission/test_hurkens_prop26.lean",
    "/workspace/leanproject/Submission/test_hurkens_prop27.lean",
    "/workspace/leanproject/Submission/test_x_partial.lean",
    "/workspace/leanproject/Submission/test_hurkens_simple.lean",
    "/workspace/leanproject/Submission/test_hurkens_simple2.lean",
    "/workspace/leanproject/Submission/test_hurkens_simple_final3.lean",
    "/workspace/leanproject/Submission/test_retraction.lean",
    "/workspace/leanproject/Submission/test_retraction2.lean",
    "/workspace/leanproject/Submission/test_retraction3.lean",
    "/workspace/leanproject/Submission/test_partial_test.lean",
    "/workspace/leanproject/Submission/test_perfect_girard_prop4.lean",
    "/workspace/leanproject/Submission/test_perfect_girard_prop5.lean",
    "/workspace/leanproject/Submission/test_perfect_girard_prop6.lean",
    "/workspace/leanproject/Submission/test_recursive_proj.lean",
    "/workspace/leanproject/Submission/test_recursive_proj2.lean",
    "/workspace/leanproject/Submission/test_perfect_f_mono.lean",
    "/workspace/leanproject/Submission/test_recursive_proj3.lean",
    "/workspace/leanproject/Submission/test_unsound_eq_prop.lean",
    "/workspace/leanproject/Submission/test_unsound_eq_prop6.lean",
    "/workspace/leanproject/Submission/test_unsound_eq_prop8.lean",
    "/workspace/leanproject/Submission/test_unsound_eq_prop9.lean",
    "/workspace/leanproject/Submission/test_unsound_eq_prop13.lean",
    "/workspace/leanproject/Submission/test_pure_girard3.lean",
    "/workspace/leanproject/Submission/test_pure_girard4.lean",
    "/workspace/leanproject/Submission/test_pure_girard6.lean",
    "/workspace/leanproject/Submission/test_pure_girard7.lean",
    "/workspace/leanproject/Submission/test_pure_girard10.lean",
    "/workspace/leanproject/Submission/test_pure_girard11.lean",
    "/workspace/leanproject/Submission/test_hurkens_final_easy2.lean",
    "/workspace/leanproject/Submission/test_prop_retraction.lean",
    "/workspace/leanproject/Submission/test_perfect_false8.lean",
    "/workspace/leanproject/Submission/test_perfect_false9.lean",
    "/workspace/leanproject/Submission/test_bad_pos2.lean",
    "/workspace/leanproject/Submission/test_unsound_eq_prop16.lean",
    "/workspace/leanproject/Submission/test_unsound_eq_prop18.lean",
    "/workspace/leanproject/Submission/test_girard_clean.lean",
    "/workspace/leanproject/Submission/test_girard_u0.lean",
    "/workspace/leanproject/Submission/test_girard_pure_prop.lean",
    "/workspace/leanproject/Submission/test_girard_prop_type_u_plift.lean",
    "/workspace/leanproject/Submission/test_girard_pure_prop_cast.lean",
    "/workspace/leanproject/Submission/test_girard_clean_complete_type1.lean",
    "/workspace/leanproject/Submission/test_hurkens_pure_prop.lean",
    "/workspace/leanproject/Submission/test_girard_prop_type_clean_perfect.lean",
    "/workspace/leanproject/Submission/test_girard_prop_type_u_perfect2.lean"
]

for f in files:
    if not os.path.exists(f): continue
    content = open(f).read()
    if "sorry" in content: continue
    
    # Check if there is an unsound or girard or false_proof theorem
    names = ["unsound", "girard", "false_proof"]
    has_target = any(name in content for name in names)
    if not has_target:
        continue
        
    res = subprocess.run(["lake", "env", "lean", f], capture_output=True, text=True)
    if res.returncode == 0:
        print(f"CLEAN COMPILE: {f}")
