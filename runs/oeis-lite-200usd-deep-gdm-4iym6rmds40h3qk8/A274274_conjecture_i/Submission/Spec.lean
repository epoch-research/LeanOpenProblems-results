import FormalConjectures.Util.ProblemImports

def A274274 : Nat → Nat :=
fun n =>
  @Finset.sum Nat Nat Nat.instAddCommMonoid (Finset.range n.succ) fun x =>
    @Finset.sum Nat Nat Nat.instAddCommMonoid (Finset.range n.succ) fun y =>
      @Finset.sum Nat Nat Nat.instAddCommMonoid (Finset.range n.succ) fun z =>
        if x ^ 3 + y ^ 2 + z ^ 2 = n ∧ y ≤ z then 1 else 0

def has_form_two_pow_k_times_four_m_plus_one : Nat → Prop :=
fun n => ∃ k m, n = 2 ^ k * (4 * m + 1)

theorem A274274_conjecture_i : ∀ (n : Nat),
  (n ≥ 2 → A274274 n ≠ 0 ∨ A274274 (n - 2) ≠ 0) ∧
    (n ≥ 6 → A274274 n ≠ 0 ∨ A274274 (n - 6) ≠ 0) ∧
      (has_form_two_pow_k_times_four_m_plus_one n → n ≠ 813 ∧ n ≠ 4404 ∧ n ≠ 6420 ∧ n ≠ 28804 → A274274 n ≠ 0) := sorryAx _ _

