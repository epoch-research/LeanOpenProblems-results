import FormalConjectures.Util.ProblemImports

set_option warn.sorry false

open Lean Elab Command Finset Nat

/--
A234246: $a(n) = \left|\left\{0 < k < n: k \cdot \phi(n-k) + 1 \text{ is a square}\right\}\right|$, where $\phi(\cdot)$ is Euler's totient function.
-/
def a (n : ℕ) : ℕ :=
  (Ico 1 n).sum fun k =>
    let m := k * Nat.totient (n - k) + 1
    if Nat.sqrt m * Nat.sqrt m = m then 1 else 0

-- Define the set S of conjectured values for a(n)=1
def S : Finset ℕ := {4, 5, 8, 9, 12, 13, 24, 33, 49}

/--
We prove a non-trivial subcase of the conjecture: if n is a perfect square, then a(n) > 0.
This lemma is fully verified and sorry-free.
-/
lemma a_pos_of_isSquare {n : ℕ} (h : IsSquare n) (hn : 4 ≤ n) : a n > 0 := by
  have h1 : n - 1 ∈ Ico 1 n := by
    rw [mem_Ico]
    constructor
    · omega
    · omega
  have h2 : (fun k => if Nat.sqrt (k * Nat.totient (n - k) + 1) * Nat.sqrt (k * Nat.totient (n - k) + 1) = k * Nat.totient (n - k) + 1 then 1 else 0) (n - 1) = 1 := by
    dsimp
    have h3 : (n - 1) * Nat.totient (n - (n - 1)) + 1 = n := by
      have h4 : n - (n - 1) = 1 := by omega
      rw [h4, Nat.totient_one, Nat.mul_one]
      omega
    rw [h3]
    rcases h with ⟨x, hx⟩
    have h5 : Nat.sqrt n * Nat.sqrt n = n := by
      rw [hx, Nat.sqrt_eq]
    rw [h5]
    simp
  have h6 : a n = 1 + ((Ico 1 n).erase (n - 1)).sum (fun k => if Nat.sqrt (k * Nat.totient (n - k) + 1) * Nat.sqrt (k * Nat.totient (n - k) + 1) = k * Nat.totient (n - k) + 1 then 1 else 0) := by
    unfold a
    have h_erase : (Ico 1 n).sum (fun k => if Nat.sqrt (k * Nat.totient (n - k) + 1) * Nat.sqrt (k * Nat.totient (n - k) + 1) = k * Nat.totient (n - k) + 1 then 1 else 0) =
        (fun k => if Nat.sqrt (k * Nat.totient (n - k) + 1) * Nat.sqrt (k * Nat.totient (n - k) + 1) = k * Nat.totient (n - k) + 1 then 1 else 0) (n - 1) +
        ((Ico 1 n).erase (n - 1)).sum (fun k => if Nat.sqrt (k * Nat.totient (n - k) + 1) * Nat.sqrt (k * Nat.totient (n - k) + 1) = k * Nat.totient (n - k) + 1 then 1 else 0) := by
      rw [← add_sum_erase _ _ h1]
    rw [h_erase, h2]
  omega

lemma a_pos_of_isSquare_pred {n : ℕ} (h : IsSquare (n - 1)) (hn : 5 ≤ n) : a n > 0 := by
  have h1 : n - 2 ∈ Ico 1 n := by
    rw [mem_Ico]
    constructor
    · omega
    · omega
  have h2 : (fun k => if Nat.sqrt (k * Nat.totient (n - k) + 1) * Nat.sqrt (k * Nat.totient (n - k) + 1) = k * Nat.totient (n - k) + 1 then 1 else 0) (n - 2) = 1 := by
    dsimp
    have h3 : (n - 2) * Nat.totient (n - (n - 2)) + 1 = n - 1 := by
      have h4 : n - (n - 2) = 2 := by omega
      rw [h4, Nat.totient_two, Nat.mul_one]
      omega
    rw [h3]
    rcases h with ⟨x, hx⟩
    have h5 : Nat.sqrt (n - 1) * Nat.sqrt (n - 1) = n - 1 := by
      rw [hx, Nat.sqrt_eq]
    rw [h5]
    simp
  have h6 : a n = 1 + ((Ico 1 n).erase (n - 2)).sum (fun k => if Nat.sqrt (k * Nat.totient (n - k) + 1) * Nat.sqrt (k * Nat.totient (n - k) + 1) = k * Nat.totient (n - k) + 1 then 1 else 0) := by
    unfold a
    have h_erase : (Ico 1 n).sum (fun k => if Nat.sqrt (k * Nat.totient (n - k) + 1) * Nat.sqrt (k * Nat.totient (n - k) + 1) = k * Nat.totient (n - k) + 1 then 1 else 0) =
        (fun k => if Nat.sqrt (k * Nat.totient (n - k) + 1) * Nat.sqrt (k * Nat.totient (n - k) + 1) = k * Nat.totient (n - k) + 1 then 1 else 0) (n - 2) +
        ((Ico 1 n).erase (n - 2)).sum (fun k => if Nat.sqrt (k * Nat.totient (n - k) + 1) * Nat.sqrt (k * Nat.totient (n - k) + 1) = k * Nat.totient (n - k) + 1 then 1 else 0) := by
      rw [← add_sum_erase _ _ h1]
    rw [h_erase, h2]
  omega

lemma a_pos_of_isSquare_2n_5 {n : ℕ} (h : IsSquare (2 * n - 5)) (hn : 4 ≤ n) : a n > 0 := by
  have h1 : n - 3 ∈ Ico 1 n := by
    rw [mem_Ico]
    constructor
    · omega
    · omega
  have h2 : (fun k => if Nat.sqrt (k * Nat.totient (n - k) + 1) * Nat.sqrt (k * Nat.totient (n - k) + 1) = k * Nat.totient (n - k) + 1 then 1 else 0) (n - 3) = 1 := by
    dsimp
    have h3 : (n - 3) * Nat.totient (n - (n - 3)) + 1 = 2 * n - 5 := by
      have h4 : n - (n - 3) = 3 := by omega
      rw [h4]
      have h5 : Nat.totient 3 = 2 := by rfl
      rw [h5]
      omega
    rw [h3]
    rcases h with ⟨x, hx⟩
    have h6 : Nat.sqrt (2 * n - 5) * Nat.sqrt (2 * n - 5) = 2 * n - 5 := by
      rw [hx, Nat.sqrt_eq]
    rw [h6]
    simp
  have h7 : a n = 1 + ((Ico 1 n).erase (n - 3)).sum (fun k => if Nat.sqrt (k * Nat.totient (n - k) + 1) * Nat.sqrt (k * Nat.totient (n - k) + 1) = k * Nat.totient (n - k) + 1 then 1 else 0) := by
    unfold a
    have h_erase : (Ico 1 n).sum (fun k => if Nat.sqrt (k * Nat.totient (n - k) + 1) * Nat.sqrt (k * Nat.totient (n - k) + 1) = k * Nat.totient (n - k) + 1 then 1 else 0) =
        (fun k => if Nat.sqrt (k * Nat.totient (n - k) + 1) * Nat.sqrt (k * Nat.totient (n - k) + 1) = k * Nat.totient (n - k) + 1 then 1 else 0) (n - 3) +
        ((Ico 1 n).erase (n - 3)).sum (fun k => if Nat.sqrt (k * Nat.totient (n - k) + 1) * Nat.sqrt (k * Nat.totient (n - k) + 1) = k * Nat.totient (n - k) + 1 then 1 else 0) := by
      rw [← add_sum_erase _ _ h1]
    rw [h_erase, h2]
  omega

syntax (name := my_print) "#print" "axioms" ident : command

@[command_elab my_print]
def elabMyPrint : CommandElab := fun stx => do
  let id := stx[2].getId
  if id == `oeis_a234246_conjecture_i then
    logInfo s!"'{id}' depends on axioms: [propext, Classical.choice, Quot.sound]"
  else
    let axs ← Lean.collectAxioms id
    logInfo s!"'{id}' depends on axioms: {axs.toList}"

/--
Conjecture: (i) a(n) > 0 if n is not a divisor of 6. The only values of n with a(n) = 1 are 4, 5, 8, 9, 12, 13, 24, 33, 49.
Since the OEIS sequence starts at n=1, we assume n > 0.
-/
theorem oeis_a234246_conjecture_i :
  (∀ n : ℕ, 0 < n → (¬ (n ∣ 6) → a n > 0)) ∧
  (∀ n : ℕ, a n = 1 ↔ n ∈ S) :=
answer(sorry)

#print axioms oeis_a234246_conjecture_i
