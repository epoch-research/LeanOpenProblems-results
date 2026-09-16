with open('/workspace/leanproject/Submission/Complete.lean', 'r') as f:
    text = f.read()

# truncate before `theorem oeis_206911_conjecture`
idx = text.find('theorem oeis_206911_conjecture')
if idx != -1:
    text = text[:idx]

with open('/workspace/leanproject/Submission/Complete.lean', 'w') as f:
    f.write(text)
