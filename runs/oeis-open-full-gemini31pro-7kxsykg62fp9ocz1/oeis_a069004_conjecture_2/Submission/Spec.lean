import FormalConjectures.Util.ProblemImports

open Nat Finset

/--
A069004: Number of times $n^2 + s^2$ is prime for positive integers $s < n$.
$$ a(n) = \sum_{s=1}^{n-1} \mathbf{1}_{\text{Prime}(n^2+s^2)} $$
-/
def a (n : ℕ) : ℕ :=
  (Ico 1 n).sum fun s => if Nat.Prime (n^2 + s^2) then 1 else 0

open scoped Nat.Prime

/--
Stronger conjecture: Let $\pi(n)$ be the prime counting function (A000720).
Then $\pi(n) \ge a(n) \ge \pi(n)/5$ for $n>1$, with the following equalities:
$\pi(2)=a(2)$, $\pi(10)=a(10)$ and $a(12)=\pi(12)/5$.
The inequality $\pi(n) \ge a(n) \ge \pi(n)/5$ is formalized as
$\text{primeCounting } n \ge a(n)$ and $5 \cdot a(n) \ge \text{primeCounting } n$.
-/
theorem oeis_a069004_conjecture_2 :
  (∀ n : ℕ, 1 < n → Nat.primeCounting n ≥ a n) ∧
  (∀ n : ℕ, 1 < n → 5 * a n ≥ Nat.primeCounting n) ∧
  (Nat.primeCounting 2 = a 2) ∧
  (Nat.primeCounting 10 = a 10) ∧
  (5 * a 12 = Nat.primeCounting 12) := by
  sorry

def fast_a_loop (n : ℕ) : ℕ → ℕ → ℕ
| 0, acc => acc
| s' + 1, acc => fast_a_loop n s' (acc + if Nat.Prime (n^2 + (s'+1)^2) then 1 else 0)

def fast_a (n : ℕ) : ℕ := fast_a_loop n (n-1) 0

lemma fast_a_loop_eq (n : ℕ) (s : ℕ) (acc : ℕ) :
  fast_a_loop n s acc = acc + (Finset.Ico 1 (s + 1)).sum (fun x => if Nat.Prime (n^2 + x^2) then 1 else 0) := by
  induction s generalizing acc with
  | zero =>
    simp [fast_a_loop]
  | succ s' ih =>
    rw [fast_a_loop, ih]
    have h1 : 1 ≤ s' + 1 := by omega
    rw [Finset.sum_Ico_succ_top h1]
    omega

lemma fast_a_eq_a (n : ℕ) (h : 1 < n) : fast_a n = a n := by
  unfold fast_a a
  have h_eq := fast_a_loop_eq n (n - 1) 0
  have h_s : n - 1 + 1 = n := by omega
  rw [h_s] at h_eq
  rw [zero_add] at h_eq
  exact h_eq

set_option maxHeartbeats 0
set_option maxRecDepth 2000000

theorem oeis_a069004_conjecture_2.disproof : ¬ (type_of% @oeis_a069004_conjecture_2) :=
  fun h => by
    have h_counter := h.1 512720 (by decide)
    have h_not : ¬(Nat.primeCounting 512720 ≥ a 512720) := by
      rw [← fast_a_eq_a 512720 (by decide)]
      native_decide
    exact h_not h_counter
