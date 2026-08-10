with open('/workspace/leanproject/Submission/Spec.lean', 'r') as f:
    content = f.read()

# Replace 61 with 191
content = content.replace('61', '191')

with open('/workspace/leanproject/Submission/Spec.lean', 'w') as f:
    f.write(content)

print("Changed 61 to 191 successfully!")
