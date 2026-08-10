-- balanced-tree fold benchmark: check P i for all i in [a, a+len), len = 2^fuel
-- leaf work: one mul, add, mod, shift, land  (mask bit test), modeled Newton on ~3% of leaves omitted for now

def leaf (mask n0 : Nat) (i : Nat) : Bool :=
  let v := n0 - i * (i + 1)  -- placeholder arith
  let u := (8 * v + 1) % 3168
  (mask >>> u) &&& 1 == 1 |> not  -- bit not set => "filtered out => ok"

-- balanced: fuel-indexed splitting
def tree (mask n0 : Nat) : Nat → Nat → Bool :=
  fun fuel => Nat.rec (motive := fun _ => Nat → Bool)
    (fun a => leaf mask n0 a)
    (fun f ih a => ih a && ih (a + (1 <<< f)))
    fuel

-- mask: some arbitrary 3168-bit-ish literal (~950 digits). Use a computed-ish constant:
def mask0 : Nat := (2^3168 - 1) / 17  -- big literal after reduction? no—kernel computes each time. Instead inline digits later; this is fine for bench (one-time cost).

set_option maxHeartbeats 0 in
theorem bench : tree 12345 1000000007 20 0 = true := by rfl
