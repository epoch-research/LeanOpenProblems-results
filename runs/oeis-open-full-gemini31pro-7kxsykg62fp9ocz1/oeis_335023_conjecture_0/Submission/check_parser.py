A_lit = "1" * 100000
with open('/workspace/leanproject/Submission/TestParser.lean', 'w') as f:
    f.write(f'def A : ℕ := {A_lit}\n')
