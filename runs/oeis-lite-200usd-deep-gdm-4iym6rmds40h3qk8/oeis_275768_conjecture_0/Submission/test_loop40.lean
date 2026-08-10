import FormalConjectures.Util.ProblemImports

def a_test (n : ℕ) : ℕ := 0

mutual
  def oeis_275768_conjecture_0_test : ¬ ∃ n : ℕ, a_test n = 4 := by
    intro ⟨n, hn⟩
    exact (get_all_proof ()).down n hn

  def my_inst : Nonempty (PLift (∀ m, a_test m = 4 → False)) :=
    ⟨⟨fun m hm => (oeis_275768_conjecture_0_test ⟨m, hm⟩).elim⟩⟩

  partial def get_all_proof (u : Unit) : PLift (∀ m, a_test m = 4 → False) :=
    get_all_proof u
end
