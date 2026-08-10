import FormalConjectures.Util.ProblemImports

open scoped Nat.Prime

noncomputable def A289827 (n : ℕ) : ℕ :=
  Nat.findGreatest (fun m => π (m + n) = π m + π n) n

lemma findGreatest_le_of_forall_not {P : ℕ → Prop} [DecidablePred P] {n : ℕ}
    (h : ∀ m, 10 < m → m ≤ n → ¬ P m) : Nat.findGreatest P n ≤ 10 := by
  by_contra h_gt
  push_neg at h_gt
  have h_eq : Nat.findGreatest P n = Nat.findGreatest P n := rfl
  have h_spec := (Nat.findGreatest_eq_iff.1 h_eq).2.1 (by omega)
  have h_le := (Nat.findGreatest_eq_iff.1 h_eq).1
  exact h _ h_gt h_le h_spec

def check_all_pairs (N : ℕ) : Bool :=
  (List.range (N + 1)).all fun n =>
    ((List.range (n + 1)).filter (fun m => 10 < m)).all fun m =>
      decide (π (m + n) ≠ π m + π n)

lemma check_all_pairs_true (N : ℕ) (h : check_all_pairs N = true) :
    ∀ n, n ≤ N → ∀ m, 10 < m → m ≤ n → π (m + n) ≠ π m + π n := by
  intro n hn m hm h_le
  have h_n_mem : n ∈ List.range (N + 1) := by
    rw [List.mem_range]
    omega
  have h_n_all := List.all_eq_true.1 h n h_n_mem
  have h_m_mem : m ∈ (List.range (n + 1)).filter (fun m => 10 < m) := by
    rw [List.mem_filter]
    refine ⟨?_, decide_eq_true hm⟩
    rw [List.mem_range]
    omega
  have h_all := List.all_eq_true.1 h_n_all m h_m_mem
  exact of_decide_eq_true h_all

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

lemma forall_not_up_to_200 :
    ∀ n, n ≤ 200 → ∀ m, 10 < m → m ≤ n → π (m + n) ≠ π m + π n := by
  intro n hn
  have h : check_all_pairs 200 = true := by decide
  exact check_all_pairs_true 200 h n hn

theorem A289827_conjecture_bounded_by_10 : ∀ (n : ℕ), A289827 n ≤ 10 := by
  intro n
  by_cases hn : n ≤ 200
  · by_cases h2 : n ≤ 10
    · have h3 : A289827 n ≤ n := Nat.findGreatest_le _
      omega
    · apply findGreatest_le_of_forall_not
      exact forall_not_up_to_200 n hn
  · sorry
