import subprocess

candidates = [
    "/workspace/leanproject/Submission/test_unsound_girard5.lean",
    "/workspace/leanproject/Submission/test_w.lean",
    "/workspace/leanproject/Submission/test_unsound_prop.lean",
    "/workspace/leanproject/Submission/test_bad2.lean",
    "/workspace/leanproject/Submission/test_unsound_eq.lean",
    "/workspace/leanproject/Submission/test_u_step.lean",
    "/workspace/leanproject/Submission/test_x_rec.lean",
    "/workspace/leanproject/Submission/test_cast_eq4.lean",
    "/workspace/leanproject/Submission/test_inj_perfect.lean",
    "/workspace/leanproject/Submission/test_hurkens_prop4.lean",
    "/workspace/leanproject/Submission/test_hurkens_prop8.lean",
    "/workspace/leanproject/Submission/test_hurkens_prop9.lean",
    "/workspace/leanproject/Submission/test_hurkens_prop10.lean",
    "/workspace/leanproject/Submission/test_hurkens_prop15.lean",
    "/workspace/leanproject/Submission/test_hurkens_prop16.lean",
    "/workspace/leanproject/Submission/test_hurkens_prop26.lean",
    "/workspace/leanproject/Submission/test_hurkens_prop27.lean",
    "/workspace/leanproject/Submission/test_hurkens_simple.lean",
    "/workspace/leanproject/Submission/test_hurkens_simple2.lean",
    "/workspace/leanproject/Submission/test_hurkens_simple_final3.lean",
    "/workspace/leanproject/Submission/test_retraction.lean",
    "/workspace/leanproject/Submission/test_retraction2.lean",
    "/workspace/leanproject/Submission/test_retraction3.lean",
    "/workspace/leanproject/Submission/test_perfect_girard_prop4.lean",
    "/workspace/leanproject/Submission/test_perfect_girard_prop5.lean",
    "/workspace/leanproject/Submission/test_perfect_girard_prop6.lean",
    "/workspace/leanproject/Submission/test_recursive_proj.lean",
    "/workspace/leanproject/Submission/test_recursive_proj2.lean",
    "/workspace/leanproject/Submission/test_perfect_f_mono.lean",
]

for f in candidates:
    # Append #print to the file and run it
    content = open(f).read()
    # Check for theorems/defs in the file
    names = []
    if "theorem unsound" in content or "def unsound" in content:
        names.append("unsound")
    if "theorem girard" in content or "def girard" in content:
        names.append("girard")
    if "theorem false_proof" in content or "def false_proof" in content:
        names.append("false_proof")
        
    for name in names:
        test_content = content + f"\n#check {name}\n"
        res = subprocess.run(["lean", "-"], input=test_content, capture_output=True, text=True)
        if res.returncode == 0:
            print(f"FOUND PROOF OF FALSE IN: {f} with name: {name}")
            print(res.stdout)
