with open('/workspace/leanproject/Submission/Spec.lean', 'r') as f:
    text = f.read()

text = text.replace("exact ⟨Hn_gtB, Hn_gt1, H_not_dvd⟩", "exact ⟨⟨Hn_gt1, H_not_dvd⟩, Hn_gtB⟩")

with open('/workspace/leanproject/Submission/Spec.lean', 'w') as f:
    f.write(text)
