import re

with open('/workspace/leanproject/Submission/Master.lean', 'r') as f:
    content = f.read()

content = content.replace('decide\n', 'rfl\n')

with open('/workspace/leanproject/Submission/Master.lean', 'w') as f:
    f.write(content)
