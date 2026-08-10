import FormalConjectures.Util.ProblemImports

open Nat Finset

/--
A275409: Number of ordered ways to write $n$ as $2w^2 + x^2 + y^2 + z^2$ with $w + x + 2y + 4z$ a square, where $w,x,y,z$ are nonnegative integers.
$$a(n) = \# \left\{(w, x, y, z) \in \mathbb{N}^4 \mid 2w^2 + x^2 + y^2 + z^2 = n, \quad w + x + 2y + 4z \text{ is a square} \right\}$$
-/
noncomputable def a (n : ℕ) : ℕ :=
  -- Define perfect square check using computable `Nat.sqrt`.
  let is_sq (k : ℕ) : Prop := k.sqrt * k.sqrt = k

  -- A safe upper bound for $w, x, y, z$ is $\lfloor\sqrt{n}\rfloor + 1$.
  let M : ℕ := n.sqrt + 1
  let R : Finset ℕ := range M

  -- The search space of ordered quadruples, structured as $w \times (x \times (y \times z))$.
  -- This allows for robust iteration over $w, x, y, z$.
  let search_space : Finset (ℕ × (ℕ × (ℕ × ℕ))) := R.product (R.product (R.product R))

  search_space.sum fun p : ℕ × (ℕ × (ℕ × ℕ)) =>
    let w := p.fst
    let x := p.snd.fst
    let y := p.snd.snd.fst
    let z := p.snd.snd.snd

    let sum_sq := 2 * w^2 + x^2 + y^2 + z^2
    let lin_comb := w + x + 2 * y + 4 * z

    -- The bounds chosen ensures that we will find all solutions (w,x,y,z) where w^2, x^2, y^2, z^2 <= n.
    -- If $2w^2 + x^2 + y^2 + z^2 = n$, then $w, x, y, z \le \sqrt{n}$, so this upper bound is sufficient.
    if sum_sq = n ∧ is_sq lin_comb
    then 1
    else 0

/-- A fully computable equivalent of the sequence $a(n)$ for numerical evaluation in Lean. -/
def a_computable (n : ℕ) : ℕ :=
  let is_sq (k : ℕ) : Bool := k.sqrt * k.sqrt == k
  let M : ℕ := n.sqrt + 1
  let R : Finset ℕ := range M
  let search_space : Finset (ℕ × (ℕ × (ℕ × ℕ))) := R.product (R.product (R.product R))
  search_space.sum fun p : ℕ × (ℕ × (ℕ × ℕ)) =>
    let w := p.fst
    let x := p.snd.fst
    let y := p.snd.snd.fst
    let z := p.snd.snd.snd
    let sum_sq := 2 * w^2 + x^2 + y^2 + z^2
    let lin_comb := w + x + 2 * y + 4 * z
    if sum_sq == n && is_sq lin_comb
    then 1
    else 0

lemma cond_equiv (n : ℕ) (p : ℕ × ℕ × ℕ × ℕ) :
  (2 * p.1 ^ 2 + p.2.1 ^ 2 + p.2.2.1 ^ 2 + p.2.2.2 ^ 2 = n ∧
   (p.1 + p.2.1 + 2 * p.2.2.1 + 4 * p.2.2.2).sqrt * (p.1 + p.2.1 + 2 * p.2.2.1 + 4 * p.2.2.2).sqrt = p.1 + p.2.1 + 2 * p.2.2.1 + 4 * p.2.2.2) ↔
  (2 * p.1 ^ 2 + p.2.1 ^ 2 + p.2.2.1 ^ 2 + p.2.2.2 ^ 2 == n &&
   ((p.1 + p.2.1 + 2 * p.2.2.1 + 4 * p.2.2.2).sqrt * (p.1 + p.2.1 + 2 * p.2.2.1 + 4 * p.2.2.2).sqrt == p.1 + p.2.1 + 2 * p.2.2.1 + 4 * p.2.2.2)) = true := by
  rw [Bool.and_eq_true, beq_iff_eq, beq_iff_eq]

/-- Proof of equivalence of the noncomputable `a` and the computable `a_computable`. -/
theorem a_eq_a_computable (n : ℕ) : a n = a_computable n := by
  unfold a a_computable
  dsimp
  congr 1
  ext p
  dsimp
  by_cases h : (2 * p.1 ^ 2 + p.2.1 ^ 2 + p.2.2.1 ^ 2 + p.2.2.2 ^ 2 = n ∧
   (p.1 + p.2.1 + 2 * p.2.2.1 + 4 * p.2.2.2).sqrt * (p.1 + p.2.1 + 2 * p.2.2.1 + 4 * p.2.2.2).sqrt = p.1 + p.2.1 + 2 * p.2.2.1 + 4 * p.2.2.2)
  · rw [if_pos h]
    have h2 : (2 * p.1 ^ 2 + p.2.1 ^ 2 + p.2.2.1 ^ 2 + p.2.2.2 ^ 2 == n &&
               ((p.1 + p.2.1 + 2 * p.2.2.1 + 4 * p.2.2.2).sqrt * (p.1 + p.2.1 + 2 * p.2.2.1 + 4 * p.2.2.2).sqrt == p.1 + p.2.1 + 2 * p.2.2.1 + 4 * p.2.2.2)) = true := (cond_equiv n p).mp h
    rw [if_pos h2]
  · rw [if_neg h]
    have h2 : ¬(2 * p.1 ^ 2 + p.2.1 ^ 2 + p.2.2.1 ^ 2 + p.2.2.2 ^ 2 == n &&
               ((p.1 + p.2.1 + 2 * p.2.2.1 + 4 * p.2.2.2).sqrt * (p.1 + p.2.1 + 2 * p.2.2.1 + 4 * p.2.2.2).sqrt == p.1 + p.2.1 + 2 * p.2.2.1 + 4 * p.2.2.2)) = true := (cond_equiv n p).not.mp h
    rw [if_neg h2]

/-- The set of natural numbers $n$ for which $a(n) = 0$ is conjectured to be $\{3, 10\}$. -/
def A275409_zero_set : Finset ℕ :=
  {3, 10}

/-- The set of natural numbers $n$ for which $a(n) = 1$ is conjectured to be a specific finite set. -/
def A275409_one_set : Finset ℕ :=
  {0, 2, 7, 8, 9, 12, 14, 15, 22, 23, 24, 25, 36, 39, 44, 45, 60, 87, 98, 106, 110, 111, 183}

/--
Conjecture (i) from A275409:
a(n) > 0 except for n = 3, 10, and a(n) = 1 only for
n = 0, 2, 7, 8, 9, 12, 14, 15, 22, 23, 24, 25, 36, 39, 44, 45, 60, 87, 98, 106, 110, 111, 183.
-/
theorem oeis_275409_conjecture_0 :
  (∀ n : ℕ, (a n > 0 ↔ n ∉ A275409_zero_set)) ∧
  (∀ n : ℕ, (a n = 1 ↔ n ∈ A275409_one_set)) := by
  sorry


set_option maxRecDepth 200000
set_option maxHeartbeats 0

def sqrt_struct (n : ℕ) : ℕ :=
  if n < 4 then (if n < 1 then 0 else 1)
  else if n < 9 then 2
  else if n < 16 then 3
  else if n < 25 then 4
  else if n < 36 then 5
  else if n < 49 then 6
  else if n < 64 then 7
  else if n < 81 then 8
  else if n < 100 then 9
  else if n < 121 then 10
  else if n < 144 then 11
  else if n < 169 then 12
  else if n < 196 then 13
  else 14

def is_square_struct (n : ℕ) : Bool :=
  let s := sqrt_struct n
  s * s == n

def a_struct (n : ℕ) : ℕ :=
  let rec loop_y (w x : ℕ) (y : ℕ) (acc : ℕ) : ℕ :=
    match y with
    | 0 =>
      let rem := n - 2 * w^2 - x^2
      let z := sqrt_struct rem
      if z * z == rem then
        let lin_comb := w + x + 2 * 0 + 4 * z
        if is_square_struct lin_comb then acc + 1 else acc
      else acc
    | y' + 1 =>
      let rem := n - 2 * w^2 - x^2 - y^2
      let new_acc :=
        let z := sqrt_struct rem
        if z * z == rem then
          let lin_comb := w + x + 2 * y + 4 * z
          if is_square_struct lin_comb then acc + 1 else acc
        else acc
      loop_y w x y' new_acc

  let rec loop_x (w : ℕ) (x : ℕ) (acc : ℕ) : ℕ :=
    match x with
    | 0 =>
      let limit_y := sqrt_struct (n - 2 * w^2)
      loop_y w 0 limit_y acc
    | x' + 1 =>
      let limit_y := sqrt_struct (n - 2 * w^2 - x^2)
      let new_acc := loop_y w x limit_y acc
      loop_x w x' new_acc

  let rec loop_w (w : ℕ) (acc : ℕ) : ℕ :=
    match w with
    | 0 =>
      let limit_x := sqrt_struct n
      loop_x 0 limit_x acc
    | w' + 1 =>
      let limit_x := sqrt_struct (n - 2 * w^2)
      let new_acc := loop_x w limit_x acc
      loop_w w' new_acc

  let limit_w := sqrt_struct (n / 2)
  loop_w limit_w 0

theorem proof_183_struct : ∀ n ≤ 183,
  (a_struct n > 0 ↔ n ∉ A275409_zero_set) ∧
  (a_struct n = 1 ↔ n ∈ A275409_one_set) := by
  decide

#print axioms proof_183_struct




