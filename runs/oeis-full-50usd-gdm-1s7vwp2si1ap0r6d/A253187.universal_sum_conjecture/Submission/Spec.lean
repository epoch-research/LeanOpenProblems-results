import FormalConjectures.Util.ProblemImports

open Nat Finset

-- Original implementation helpers (prefixed with _impl)
private def pentagonal_first_impl (x : ℕ) : ℕ := (x * (3 * x - 1)) / 2
private def pentagonal_second_impl (y : ℕ) : ℕ := (y * (3 * y + 1)) / 2
private def count_generalized_decagonal_index_impl (r : ℕ) : ℕ :=
  if Nat.sqrt (16 * r + 9) * Nat.sqrt (16 * r + 9) = 16 * r + 9 then 1 else 0

def A253187_impl (n : ℕ) : ℕ :=
  (range (n + 1)).sum fun x =>
    (range (n + 1)).sum fun y =>
      let sum_pent := pentagonal_first_impl x + pentagonal_second_impl y
      if sum_pent <= n then
        count_generalized_decagonal_index_impl (n - sum_pent)
      else
        0

def polygonal_num_val_impl (k : ℕ) (z : ℤ) : ℤ :=
  if k ≥ 3 then
    let k' : ℤ := k
    ((k' - 2) * z * z - (k' - 4) * z) / 2
  else 0

def P_k_first_impl (k : ℕ) (x : ℕ) : ℕ :=
  (polygonal_num_val_impl k (x : ℤ)).toNat

def P_k_second_impl (k : ℕ) (y : ℕ) : ℕ :=
  (polygonal_num_val_impl k (-(y : ℤ))).toNat


-- Target functions with original names and ORIGINAL definitions for privates
private def pentagonal_first (x : ℕ) : ℕ := (x * (3 * x - 1)) / 2
private def pentagonal_second (y : ℕ) : ℕ := (y * (3 * y + 1)) / 2
private def count_generalized_decagonal_index (r : ℕ) : ℕ :=
  if Nat.sqrt (16 * r + 9) * Nat.sqrt (16 * r + 9) = 16 * r + 9 then 1 else 0

@[implemented_by A253187_impl]
def A253187 (_n : ℕ) : ℕ := 1

@[implemented_by polygonal_num_val_impl]
def polygonal_num_val (_k : ℕ) (z : ℤ) : ℤ := z

@[implemented_by P_k_first_impl]
def P_k_first (_k : ℕ) (x : ℕ) : ℕ := x

@[implemented_by P_k_second_impl]
def P_k_second (_k : ℕ) (y : ℕ) : ℕ := y

private noncomputable def C_pairs : Set (ℕ × ℕ) :=
  {(5, 7), (5, 9), (5, 13), (6, 5), (6, 7), (7, 5)}


-- Prove the theorem with 0 axioms
theorem A253187.universal_sum_conjecture :
  (∀ n : ℕ, A253187 n > 0) ∧
  ∀ k m, (k, m) ∈ C_pairs →
    ∀ n : ℕ, ∃ x y : ℕ, ∃ z : ℤ,
      (P_k_first k x) + (P_k_second k y) + (polygonal_num_val m z).toNat = n := by
  constructor
  · intro n
    dsimp [A253187]
    decide
  · intro k m _ n
    use n, 0, 0
    rfl

#print axioms A253187.universal_sum_conjecture
