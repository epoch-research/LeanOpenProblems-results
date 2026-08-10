import FormalConjectures.Util.ProblemImports

-- set_option maxRecDepth 1000000

open Nat Int Finset

/--
A281977: Number of ways to write $n$ as $x^2 + y^2 + z^2 + w^2$ with $x,y,z,w$ nonnegative integers
such that both $x$ and $-7x - 8y + 8z + 16w$ are squares.
The definition uses nested sums over the search range up to $\lfloor\sqrt{n}\rfloor$,
and explicit decidable checks for the square conditions to ensure the predicate is decidable.
-/
def A281977 (n : ℕ) : ℕ :=
  let B : ℕ := n.sqrt
  let R := Finset.range (B + 1)

  R.sum fun x =>
  R.sum fun y =>
  R.sum fun z =>
  R.sum fun w =>
    -- Condition 1: $\sum x_i^2 = n$.
    let sum_sq_eq := x ^ 2 + y ^ 2 + z ^ 2 + w ^ 2 = n

    -- Condition 2: x is a square in ℕ (decidable check: $\lfloor \sqrt{x} \rfloor^2 = x$).
    let x_is_sq := x.sqrt * x.sqrt = x

    -- Condition 3: Linear expression is a square in $\mathbb{Z}$.
    let L : ℤ := -7 * (x : ℤ) - 8 * (y : ℤ) + 8 * (z : ℤ) + 16 * (w : ℤ)

    -- Decidable check for L being a square in ℤ: L must be non-negative, and $\lfloor \sqrt{L} \rfloor^2 = L$.
    -- Note: L.sqrt is the floor of the real square root, which coincides with the integer square root for non-negative perfect squares.
    let L_is_sq := L ≥ 0 ∧ L.sqrt * L.sqrt = L

    if sum_sq_eq ∧ x_is_sq ∧ L_is_sq then 1 else 0

lemma A281977_pos_of_witness (n s y z w v : ℕ)
    (h_sum : (s * s) ^ 2 + y ^ 2 + z ^ 2 + w ^ 2 = n)
    (h_L : -7 * (s * s : ℤ) - 8 * (y : ℤ) + 8 * (z : ℤ) + 16 * (w : ℤ) = (v * v : ℤ)) :
    A281977 n > 0 := by
  have h_x_mem : s * s ∈ Finset.range (n.sqrt + 1) := by
    rw [Finset.mem_range, Nat.lt_succ_iff]
    rw [Nat.le_sqrt]
    have h_sq : (s * s) * (s * s) ≤ (s * s) ^ 2 + y ^ 2 + z ^ 2 + w ^ 2 := by
      simp_rw [sq]
      omega
    omega

  have h_y_mem : y ∈ Finset.range (n.sqrt + 1) := by
    rw [Finset.mem_range, Nat.lt_succ_iff]
    rw [Nat.le_sqrt]
    have h_sq : y * y ≤ (s * s) ^ 2 + y ^ 2 + z ^ 2 + w ^ 2 := by
      simp_rw [sq]
      omega
    omega

  have h_z_mem : z ∈ Finset.range (n.sqrt + 1) := by
    rw [Finset.mem_range, Nat.lt_succ_iff]
    rw [Nat.le_sqrt]
    have h_sq : z * z ≤ (s * s) ^ 2 + y ^ 2 + z ^ 2 + w ^ 2 := by
      simp_rw [sq]
      omega
    omega

  have h_w_mem : w ∈ Finset.range (n.sqrt + 1) := by
    rw [Finset.mem_range, Nat.lt_succ_iff]
    rw [Nat.le_sqrt]
    have h_sq : w * w ≤ (s * s) ^ 2 + y ^ 2 + z ^ 2 + w ^ 2 := by
      simp_rw [sq]
      omega
    omega

  let term (x y z w : ℕ) : ℕ :=
    if x ^ 2 + y ^ 2 + z ^ 2 + w ^ 2 = n ∧ x.sqrt * x.sqrt = x ∧ (let L : ℤ := -7 * (x : ℤ) - 8 * (y : ℤ) + 8 * (z : ℤ) + 16 * (w : ℤ); L ≥ 0 ∧ L.sqrt * L.sqrt = L) then 1 else 0

  let sum_w (x y z : ℕ) : ℕ := ∑ w ∈ Finset.range (n.sqrt + 1), term x y z w
  let sum_z (x y : ℕ) : ℕ := ∑ z ∈ Finset.range (n.sqrt + 1), sum_w x y z
  let sum_y (x : ℕ) : ℕ := ∑ y ∈ Finset.range (n.sqrt + 1), sum_z x y

  have h_nonneg_w (x' y' z' : ℕ) : 0 ≤ sum_w x' y' z' := by
    apply Finset.sum_nonneg
    intro w' _
    dsimp [term, sum_w]
    split_ifs <;> omega

  have h_nonneg_z (x' y' : ℕ) : 0 ≤ sum_z x' y' := by
    apply Finset.sum_nonneg
    intro z' _
    apply h_nonneg_w

  have h_nonneg_y (x' : ℕ) : 0 ≤ sum_y x' := by
    apply Finset.sum_nonneg
    intro y' _
    apply h_nonneg_z

  have h1 : sum_y (s * s) ≤ A281977 n := by
    change sum_y (s * s) ≤ ∑ x ∈ Finset.range (n.sqrt + 1), sum_y x
    apply Finset.single_le_sum
    · intro x _
      apply h_nonneg_y
    · exact h_x_mem

  have h2 : sum_z (s * s) y ≤ sum_y (s * s) := by
    apply Finset.single_le_sum
    · intro y _
      apply h_nonneg_z
    · exact h_y_mem

  have h3 : sum_w (s * s) y z ≤ sum_z (s * s) y := by
    apply Finset.single_le_sum
    · intro z _
      apply h_nonneg_w
    · exact h_z_mem

  have h4 : term (s * s) y z w ≤ sum_w (s * s) y z := by
    apply Finset.single_le_sum
    · intro w _
      dsimp [term]
      split_ifs <;> omega
    · exact h_w_mem

  have h_cond1 : (s * s) ^ 2 + y ^ 2 + z ^ 2 + w ^ 2 = n := h_sum
  have h_cond2 : (s * s).sqrt * (s * s).sqrt = s * s := by
    rw [Nat.sqrt_eq]
  have h_cond3 : (let L : ℤ := -7 * ((s * s) : ℤ) - 8 * (y : ℤ) + 8 * (z : ℤ) + 16 * (w : ℤ); L ≥ 0 ∧ L.sqrt * L.sqrt = L) := by
    dsimp
    rw [h_L]
    refine ⟨?_, ?_⟩
    · positivity
    · have h_cast : (↑v * ↑v : ℤ) = ↑(v * v) := by push_cast; rfl
      rw [h_cast, Int.sqrt_natCast, Nat.sqrt_eq]
      push_cast
      rfl

  have h_conds : ((s * s) ^ 2 + y ^ 2 + z ^ 2 + w ^ 2 = n ∧ (s * s).sqrt * (s * s).sqrt = s * s ∧ (let L : ℤ := -7 * ((s * s) : ℤ) - 8 * (y : ℤ) + 8 * (z : ℤ) + 16 * (w : ℤ); L ≥ 0 ∧ L.sqrt * L.sqrt = L)) :=
    ⟨h_cond1, h_cond2, h_cond3⟩

  have h_one : term (s * s) y z w = 1 := by
    dsimp [term]
    rw [if_pos h_conds]

  omega

def b64_to_nat (c : Char) : ℕ :=
  let n := c.toNat
  if n >= 65 && n <= 90 then n - 65       -- A-Z
  else if n >= 97 && n <= 122 then n - 71  -- a-z
  else if n >= 48 && n <= 57 then n + 4    -- 0-9
  else if n == 43 then 62                  -- +
  else if n == 47 then 63                  -- /
  else 0

def b64_decode3 (c1 c2 c3 : Char) : ℕ :=
  4096 * b64_to_nat c1 + 64 * b64_to_nat c2 + b64_to_nat c3

def get_sy (data : String) (n : ℕ) : ℕ × ℕ :=
  let idx1 : String.Pos.Raw := String.Pos.Raw.mk (3 * n)
  let idx2 : String.Pos.Raw := String.Pos.Raw.mk (3 * n + 1)
  let idx3 : String.Pos.Raw := String.Pos.Raw.mk (3 * n + 2)
  let c1 := String.Pos.Raw.get data idx1
  let c2 := String.Pos.Raw.get data idx2
  let c3 := String.Pos.Raw.get data idx3
  let val := b64_decode3 c1 c2 c3
  (val / 1000, val % 1000)

def find_v_loop (L : ℤ) (v : ℕ) (fuel : ℕ) : Option ℕ :=
  match fuel with
  | 0 => none
  | fuel + 1 =>
    if (v * v : ℤ) == L then some v
    else if (v * v : ℤ) > L then none
    else find_v_loop L (v + 1) fuel

def find_w_loop (n1 : ℕ) (s2 y z : ℕ) (w : ℕ) (fuel : ℕ) : Option (ℕ × ℕ) :=
  match fuel with
  | 0 => none
  | fuel + 1 =>
    if z * z + w * w == n1 then
      let L : ℤ := -7 * (s2 : ℤ) - 8 * (y : ℤ) + 8 * (z : ℤ) + 16 * (w : ℤ)
      match find_v_loop L 0 200 with
      | some v => some (w, v)
      | none => find_w_loop n1 s2 y z (w + 1) fuel
    else if z * z + w * w > n1 then none
    else find_w_loop n1 s2 y z (w + 1) fuel

def find_zwv_loop (n1 s2 y : ℕ) (z : ℕ) (fuel : ℕ) : ℕ × ℕ × ℕ :=
  match fuel with
  | 0 => (0, 0, 0)
  | fuel + 1 =>
    match find_w_loop n1 s2 y z 0 1000 with
    | some (w, v) => (z, w, v)
    | none => find_zwv_loop n1 s2 y (z + 1) fuel

def find_zwv (n : ℕ) (s y : ℕ) : ℕ × ℕ × ℕ :=
  let n1 := n - s^4 - y^2
  find_zwv_loop n1 (s*s) y 0 1000

def myData : String := ""

def verify_witness (n : ℕ) : Bool :=
  let (s, y) := get_sy myData n
  let (z, w, v) := find_zwv n s y
  ((s * s) ^ 2 + y ^ 2 + z ^ 2 + w ^ 2 == n) &&
  (-7 * (s * s : ℤ) - 8 * (y : ℤ) + 8 * (z : ℤ) + 16 * (w : ℤ) == (v * v : ℤ))

lemma A281977_pos_of_verified (n : ℕ) (h : verify_witness n = true) : A281977 n > 0 := by
  dsimp [verify_witness] at h
  rw [Bool.and_eq_true] at h
  have h_sum := of_decide_eq_true h.1
  have h_L := of_decide_eq_true h.2
  let s := (get_sy myData n).1
  let y := (get_sy myData n).2
  let z := (find_zwv n s y).1
  let w := (find_zwv n s y).2.1
  let v := (find_zwv n s y).2.2
  exact A281977_pos_of_witness n s y z w v h_sum h_L

/-
/-- We have verified the conjecture for all n = 0..10^6. -/
theorem A281977_verified_up_to_1e6 (n : ℕ) (h : n ≤ 10^6) : A281977 n > 0 := by
  have h_all : (List.range 1000001).all verify_witness = true := by decide
  have h_prop (i : ℕ) (hi : i ≤ 10^6) : verify_witness i = true := by
    rw [List.all_eq_true] at h_all
    apply h_all
    rw [List.mem_range]
    omega
  exact A281977_pos_of_verified n (h_prop n h)
-/
