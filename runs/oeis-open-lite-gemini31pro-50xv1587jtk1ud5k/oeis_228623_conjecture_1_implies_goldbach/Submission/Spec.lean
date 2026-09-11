import FormalConjectures.Util.ProblemImports

open scoped Nat.Prime
open Matrix

/--
A228623: Determinant of the $n \times n$ matrix with $(i,j)$-entry ($i,j = 0,\dots,n-1$)
equal to $1$ or $0$ according as $n + i - j$ and $n - i + j$ are both prime or not.
-/
noncomputable def A228623 (n : ℕ) : ℤ :=
  let M : Matrix (Fin n) (Fin n) ℤ := fun i j =>
    let i_nat : ℕ := i.val
    let j_nat : ℕ := j.val

    -- The terms are guaranteed to be positive, so natural number subtraction is exact:
    -- p₁ = n + i - j
    let p₁ := n + i_nat - j_nat
    -- p₂ = n - i + j, which is n + j - i.
    let p₂ := n + j_nat - i_nat

    if p₁.Prime ∧ p₂.Prime then 1 else 0

  M.det

/--
oeis_228623_conjecture_1: The conjecture that $A228623(n)$ is nonzero if $n$ is odd and greater than $120$
implies Goldbach's conjecture for even numbers of the form $4k + 2$.

Formal statement of the implication:
(∀ n : ℕ, n > 120 → Odd n → A228623 n ≠ 0)
→
(∀ k : ℕ, k > 0 → ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ 4 * k + 2 = p + q)
-/

def get_p : ℕ → ℕ
| 1 => 3 | 2 => 3 | 3 => 3 | 4 => 5 | 5 => 3 | 6 => 3 | 7 => 7 | 8 => 3 | 9 => 7 | 10 => 5
| 11 => 3 | 12 => 3 | 13 => 7 | 14 => 5 | 15 => 3 | 16 => 5 | 17 => 3 | 18 => 3 | 19 => 5 | 20 => 3
| 21 => 3 | 22 => 7 | 23 => 5 | 24 => 19 | 25 => 5 | 26 => 3 | 27 => 3 | 28 => 5 | 29 => 5 | 30 => 13
| 31 => 13 | 32 => 3 | 33 => 3 | 34 => 7 | 35 => 3 | 36 => 7 | 37 => 11 | 38 => 3 | 39 => 7 | 40 => 5
| 41 => 3 | 42 => 3 | 43 => 7 | 44 => 5 | 45 => 3 | 46 => 5 | 47 => 11 | 48 => 3 | 49 => 5 | 50 => 3
| 51 => 7 | 52 => 11 | 53 => 3 | 54 => 7 | 55 => 11 | 56 => 3 | 57 => 3 | 58 => 5 | 59 => 5 | _ => 3

set_option maxHeartbeats 1000000
set_option maxRecDepth 1000000

lemma goldbach_59 : ∀ k ∈ Finset.Ioc 0 59,
  (get_p k).Prime ∧ (4 * k + 2 - get_p k).Prime ∧ get_p k + (4 * k + 2 - get_p k) = 4 * k + 2 := by
  decide

lemma goldbach_59_exists (k : ℕ) (h1 : 0 < k) (h2 : k ≤ 59) :
  ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 4 * k + 2 = p + q := by
  have H := goldbach_59 k (Finset.mem_Ioc.mpr ⟨h1, h2⟩)
  use get_p k, 4 * k + 2 - get_p k
  exact ⟨H.1, H.2.1, H.2.2.symm⟩

lemma det_zero_of_no_goldbach (n : ℕ) (hn : n > 0)
  (h : ∀ p q : ℕ, p.Prime → q.Prime → p + q ≠ 2 * n) : A228623 n = 0 := by
  dsimp [A228623]
  have hM : (fun i j : Fin n =>
    let i_nat : ℕ := i.val
    let j_nat : ℕ := j.val
    let p₁ := n + i_nat - j_nat
    let p₂ := n + j_nat - i_nat
    if p₁.Prime ∧ p₂.Prime then (1:ℤ) else 0) = 0 := by
    ext i j
    simp only [Pi.zero_apply]
    split_ifs with h1
    · rcases h1 with ⟨hp1, hp2⟩
      have h2 := h (n + i.val - j.val) (n + j.val - i.val) hp1 hp2
      have h3 : (n + i.val - j.val) + (n + j.val - i.val) = 2 * n := by omega
      contradiction
    · rfl
  rw [hM]
  have : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp hn
  exact Matrix.det_zero this

theorem oeis_228623_conjecture_1_implies_goldbach :
  (∀ n : ℕ, n > 120 → Odd n → A228623 n ≠ 0) →
  (∀ k : ℕ, k > 0 → ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ 4 * k + 2 = p + q) := by
  intro h k hk
  by_cases hk59 : k ≤ 59
  · exact goldbach_59_exists k hk hk59
  · by_contra h_no
    push_neg at h_no
    have h_k_gt : k > 59 := not_le.mp hk59
    let n := 2 * k + 1
    have hn_gt : n > 120 := by omega
    have hn_odd : Odd n := ⟨k, rfl⟩
    have H_A228623 := h n hn_gt hn_odd
    have h_n_pos : n > 0 := by omega
    have H_zero := det_zero_of_no_goldbach n h_n_pos (by
      intro p q hp hq
      have := h_no p q hp hq
      omega
    )
    contradiction

theorem oeis_228623_conjecture_1_implies_goldbach.disproof : ¬ (type_of% @oeis_228623_conjecture_1_implies_goldbach) := sorry
