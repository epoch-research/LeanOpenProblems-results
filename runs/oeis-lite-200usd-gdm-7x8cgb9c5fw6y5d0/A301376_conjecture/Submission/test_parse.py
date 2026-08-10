import re

# Read expand_out.txt
with open("/workspace/leanproject/Submission/expand_out.txt") as f:
    content = f.read()

# Find "Extra primes: [...]"
match = re.search(r"Extra primes:\s*(\[.*\])", content)
if not match:
    print("Could not find Extra primes in expand_out.txt!")
    exit(1)

extra_primes_str = match.group(1)
# Some tuples might be printed across lines or have missing commas? Let's check if eval works.
try:
    extra_primes = eval(extra_primes_str)
except Exception as e:
    print("Failed to eval extra_primes:", e)
    # Let's try to extract all pairs of numbers like (683, 420)
    pairs = re.findall(r"\((\d+),?\s*(\d+)\)", extra_primes_str)
    extra_primes = [(int(p), int(r)) for p, r in pairs]

print(f"Loaded {len(extra_primes)} extra primes.")

n = 126686524250410004736537312064293613795653657092983804510554503324715379258723493119883344012301288982405926046569374575432235100014312858069895494644651006289334684761526421296266808332923548185778355634967387614240536269449875614849275
n2 = n*n

used_primes = [(26, 11), (104, 19), (314, 31), (416, 23), (1256, 43), (1664, 59), (5024, 47), (6656, 67), (20096, 71), (26624, 79), (73274, 83), (80384, 107), (106496, 103), (293096, 127), (425984, 163), (1286144, 131), (1703936, 191), (4689536, 151), (6815744, 199), (18758144, 167), (75032576, 223), (82313216, 139), (109051904, 227), (300130304, 251), (436207616, 263), (1317011456, 179), (5268045824, 211), (6979321856, 307), (19208339456, 311), (21072183296, 239), (84288733184, 379), (111669149696, 331), (307333431296, 383), (446676598784, 367), (1348619730944, 431), (1786706395136, 439), (4917334900736, 419), (5394478923776, 443), (19669339602944, 463), (86311662780416, 487), (114349209288704, 499), (457396837154816, 503), (1380986604486656, 491), (1829587348619264, 587), (20141403753414656, 467), (22095785671786496, 563), (80565615013658624, 479), (88383142687145984, 631), (322262460054634496, 523), (5156199360874151936, 571), (20624797443496607744, 599)]

primes_check = [3, 7] + [p for _, p in used_primes] + [p for p, _ in extra_primes]

def get_V_all(limit):
    V = {1}
    for s in range(40):
        fs = (10 * 16**s + 16 * 4**s + 10) // 9
        if fs >= limit:
            break
        for i in range(160):
            val = fs * 4**i
            if val >= limit:
                break
            V.add(val)
    return sorted(list(V))

V_all = get_V_all(n2)
print(f"Total V_all size: {len(V_all)}")

# Check if every v is blocked
unblocked = []
for v in V_all:
    val = n2 - v
    found = False
    for p in primes_check:
        if val % p == 0 and val % (p*p) != 0:
            found = True
            break
    if not found:
        unblocked.append(v)

if unblocked:
    print(f"Error: {len(unblocked)} elements are not blocked!")
    print("First 10:", unblocked[:10])
else:
    print("SUCCESS! Every element in V_all is blocked by at least one prime.")
