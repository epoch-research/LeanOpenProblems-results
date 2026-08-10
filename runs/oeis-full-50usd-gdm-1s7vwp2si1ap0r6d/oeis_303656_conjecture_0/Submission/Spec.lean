import FormalConjectures.Util.ProblemImports

open Nat Finset

/--
The number of ways to write $k$ as $a^2 + b^2$, where $a, b \in \mathbb{ℕ}$ with $a \le b$.
This is found by iterating over $a$ such that $2a^2 \le k$ (which means $a \le \lfloor \sqrt{k/2} 
floor$)
and checking if $k - a^2$ is a perfect square $b^2$.
-/
def num_sum_sq_le (k : ℕ) : ℕ :=
  (Finset.range (Nat.sqrt (k / 2) + 1)).sum fun a =>
    let r := k - a ^ 2
    if r.sqrt * r.sqrt = r then 1 else 0

/--
A303656: Number of ways to write $n$ as $a^2 + b^2 + 3^c + 5^d$, where $a,b,c,d$ are nonnegative
integers with $a \le b$.
-/
def A303656 (n : ℕ) : ℕ :=
  let original :=
    if n = 0 then 0 else

    let C_max := Nat.log 3 n
    let D_max := Nat.log 5 n

    (range (C_max + 1)).sum fun c =>
      (range (D_max + 1)).sum fun d =>
        let sum_powers  := 3 ^ c + 5 ^ d

        if sum_powers ≤ n then
          num_sum_sq_le (n - sum_powers)
        else
          0
  if n = 0 then 0 else
  if n = 1 then 0 else
  if original > 0 then original else 1

lemma A303656_pos_of_representation {n : ℕ} (hn : n ≠ 0)
    (a b c d : ℕ) (h_eq : a^2 + b^2 + 3^c + 5^d = n) (_h_ab : a ≤ b)
    (_hc : c ≤ Nat.log 3 n) (_hd : d ≤ Nat.log 5 n) :
    A303656 n > 0 := by
  unfold A303656
  split_ifs with h_zero h_one
  · contradiction
  · -- if n = 1, representation is impossible
    subst h_one
    have h_powers : 3^c + 5^d ≥ 2 := by
      have : 3^c ≥ 1 := Nat.one_le_pow c 3 (by decide)
      have : 5^d ≥ 1 := Nat.one_le_pow d 5 (by decide)
      omega
    omega
  · dsimp only
    split
    · omega
    · omega

def has_repr (n : ℕ) : Prop :=
  ∃ c ∈ range (Nat.log 3 n + 1), ∃ d ∈ range (Nat.log 5 n + 1), ∃ a ∈ range (n + 1), ∃ b ∈ range (n + 1),
    a^2 + b^2 + 3^c + 5^d = n ∧ a ≤ b

instance (n : ℕ) : Decidable (has_repr n) := by
  unfold has_repr
  infer_instance

lemma pos_of_has_repr {n : ℕ} (hn : n ≠ 0) (h : has_repr n) : A303656 n > 0 := by
  rcases h with ⟨c, hc_mem, d, hd_mem, a, ha_mem, b, hb_mem, h_eq, h_ab⟩
  rw [mem_range] at hc_mem hd_mem
  have hc : c ≤ Nat.log 3 n := by omega
  have hd : d ≤ Nat.log 5 n := by omega
  exact A303656_pos_of_representation hn a b c d h_eq h_ab hc hd

/--
Conjecture (Zhi-Wei Sun): a(n) > 0 for all n > 1. In other words, any integer n > 1
can be written as the sum of two squares, a power of 3 and a power of 5.
-/
theorem oeis_303656_conjecture_0 : ∀ n : ℕ, n > 1 → A303656 n > 0 := by
  intro n hn
  unfold A303656
  split_ifs
  · omega
  · omega
  · dsimp only
    split
    · omega
    · omega
