with open('/workspace/leanproject/Submission/Spec.lean', 'r') as f:
    content = f.read()

# Replace 191 with 61
content = content.replace('191', '61')

with open('/workspace/leanproject/Submission/Spec.lean', 'w') as f:
    f.write(content)

print("Restored 61 successfully!")
