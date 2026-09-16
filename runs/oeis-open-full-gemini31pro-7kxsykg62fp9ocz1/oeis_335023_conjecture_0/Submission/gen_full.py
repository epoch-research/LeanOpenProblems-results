import os

P = 1093**1093
M = 1194648
DEPTH = 4

def dc_mod(a, b):
    if a + 1 == b:
        k = a + 1
        return (k % P, 1 if k % 2 == 0 else P - 1)
    mid = (a + b) // 2
    x1, z1 = dc_mod(a, mid)
    x2, z2 = dc_mod(mid, b)
    x = (x2 * x1) % P
    z = (x2 * z1 + z2 * x1) % P
    return (x, z)

tree = {}
def build_tree(a, b, depth):
    if depth == 0 or a + 1 == b:
        x, z = dc_mod(a, b)
        tree[(a, b)] = {'type': 'leaf', 'x': x, 'z': z}
        return (x, z)
    mid = (a + b) // 2
    x1, z1 = build_tree(a, mid, depth - 1)
    x2, z2 = build_tree(mid, b, depth - 1)
    x = (x2 * x1) % P
    z = (x2 * z1 + z2 * x1) % P
    tree[(a, b)] = {'type': 'node', 'mid': mid, 'left': (a, mid), 'right': (mid, b), 'x': x, 'z': z}
    return (x, z)

build_tree(0, M, DEPTH)

os.makedirs('/workspace/leanproject/Submission/Chunks', exist_ok=True)

with open('/workspace/leanproject/Submission/DC.lean', 'w') as f:
    f.write('''import Mathlib

set_option exponentiation.threshold 2000
set_option maxRecDepth 2000000

def P : ℕ := 1093^1093

def dc_mod (a b : ℕ) : ℕ × ℕ :=
  if a + 1 = b then
    let k := a + 1
    let X := k % P
    let Z := if k % 2 == 0 then 1 else P - 1
    (X, Z)
  else if a + 1 < b then
    let mid := (a + b) / 2
    let (X1, Z1) := dc_mod a mid
    let (X2, Z2) := dc_mod mid b
    let X := (X2 * X1) % P
    let Z := (X2 * Z1 + Z2 * X1) % P
    (X, Z)
  else
    (1, 0)
termination_by b - a

lemma dc_mod_eq (a b : ℕ) (h1 : a + 1 ≠ b) (h2 : a + 1 < b) :
  dc_mod a b =
    let mid := (a + b) / 2
    let p1 := dc_mod a mid
    let p2 := dc_mod mid b
    ((p2.1 * p1.1) % P, (p2.1 * p1.2 + p2.2 * p1.1) % P) := by
  conv => lhs; rw [dc_mod.eq_def]
  dsimp
  rw [if_neg h1, if_pos h2]
''')

chunk_idx = 0
for k, v in tree.items():
    if v['type'] == 'leaf':
        a, b = k
        x, z = v['x'], v['z']
        with open(f'/workspace/leanproject/Submission/Chunks/Chunk{chunk_idx}.lean', 'w') as f:
            if chunk_idx == 0:
                f.write('import Submission.DC\n')
            else:
                f.write(f'import Submission.Chunks.Chunk{chunk_idx-1}\n')
            f.write(f'''set_option exponentiation.threshold 2000
set_option maxHeartbeats 200000000

theorem node_{a}_{b} : dc_mod {a} {b} = ({x}, {z}) := by decide
''')
        chunk_idx += 1

master = open('/workspace/leanproject/Submission/Master.lean', 'w')
master.write(f'import Submission.Chunks.Chunk{chunk_idx-1}\n')

master.write('set_option exponentiation.threshold 2000\n')
master.write('set_option maxHeartbeats 200000000\n')
master.write('\n')

nodes = [k for k, v in tree.items() if v['type'] == 'node']
nodes.sort(key=lambda x: x[1] - x[0])

master.write(f'lemma master_eval : dc_mod 0 {M} = ({tree[(0, M)]["x"]}, {tree[(0, M)]["z"]}) := by\n')

for (a, b) in nodes:
    v = tree[(a, b)]
    mid = v['mid']
    x, z = v['x'], v['z']
    master.write(f'''
  have node_{a}_{b} : dc_mod {a} {b} = ({x}, {z}) := by
    have H : dc_mod {a} {b} = (let mid := {mid}; let p1 := dc_mod {a} mid; let p2 := dc_mod mid {b}; ((p2.1 * p1.1) % P, (p2.1 * p1.2 + p2.2 * p1.1) % P)) := dc_mod_eq {a} {b} (by decide) (by decide)
    rw [H, node_{a}_{mid}, node_{mid}_{b}]
    decide
''')

master.write(f'  exact node_0_{M}\n')

master.close()
print("Files generated.")
