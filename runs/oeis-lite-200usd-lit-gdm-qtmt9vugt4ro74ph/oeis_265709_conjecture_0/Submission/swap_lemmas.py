import re

with open('/workspace/leanproject/Submission/Spec.lean', 'r') as f:
    lines = f.readlines()

# Extract padicValRat_two_sum_divisors_pow_two_even block (lines 1545 to 1613, which are indices 1544 to 1612)
even_lines = lines[1544:1613]
# Extract padicValRat_two_sum_divisors_pow_two_odd block (lines 1506 to 1544, which are indices 1505 to 1543)
odd_lines = lines[1505:1544]

# In odd_lines, replace "padicValRat.one 2" with "padicValRat.one"
for i in range(len(odd_lines)):
    odd_lines[i] = odd_lines[i].replace("padicValRat.one 2", "padicValRat.one")

# Now reconstruct the file
new_lines = lines[:1505] + even_lines + odd_lines + lines[1613:]

with open('/workspace/leanproject/Submission/Spec.lean', 'w') as f:
    f.writelines(new_lines)

print("Swapped and replaced successfully!")
