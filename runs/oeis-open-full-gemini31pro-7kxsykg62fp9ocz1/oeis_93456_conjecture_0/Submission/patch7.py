with open('/workspace/leanproject/Submission/Spec.lean', 'r') as f:
    text = f.read()

text = text.replace("padicValNat_zero", "padicValNat.zero")
text = text.replace("refine ⟨Hn_gtB, ⟨Hn_gt1, H_not_dvd⟩⟩", "exact ⟨Hn_gtB, Hn_gt1, H_not_dvd⟩")

with open('/workspace/leanproject/Submission/Spec.lean', 'w') as f:
    f.write(text)
