import subprocess

with open('/workspace/leanproject/Submission/Spec.lean', 'r') as f:
    lines = f.read().split('\n')

# We want to find the first line index 'mid' such that lines[:mid] causes a stack overflow
low = 1
high = len(lines)
ans = -1

while low <= high:
    mid = (low + high) // 2
    test_content = '\n'.join(lines[:mid])
    
    with open('/workspace/leanproject/Submission/TestTemp.lean', 'w') as f:
        f.write(test_content)
        
    res = subprocess.run(['lake', 'env', 'lean', '/workspace/leanproject/Submission/TestTemp.lean'], capture_output=True, text=True)
    if 'Stack overflow' in res.stderr or 'Stack overflow' in res.stdout or res.returncode == 134:
        ans = mid
        high = mid - 1
    else:
        low = mid + 1

if ans != -1:
    print(f'First line that causes stack overflow: {ans}')
    print('\n'.join(lines[max(0, ans-5):ans+1]))
else:
    print('No stack overflow found in any prefix!')
