import Submission.CubePacking
#check List.forall_mem_append
example (L K J : List ℕ) (P : ℕ → Prop)
    (hL : ∀ n ∈ L, P n) (hK : ∀ n ∈ K, P n) (hJ : ∀ n ∈ J, P n) :
    ∀ n ∈ L ++ K ++ J, P n := by
  simp only [List.forall_mem_append]
  trace_state
  exact ⟨⟨hL,hK⟩,hJ⟩
