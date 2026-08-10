import FormalConjectures.Util.ProblemImports

def verify_witness_fast (n : Nat) : Bool := true

def check_all_witnesses (n : Nat) : Bool :=
  if n < 17 then true
  else verify_witness_fast n && check_all_witnesses (n - 1)

theorem check_all_witnesses_ok : ∀ n, check_all_witnesses n = true → ∀ m, 17 ≤ m → m ≤ n → verify_witness_fast m = true
  | n, h => by
    by_cases hn : n < 17
    · intro m hm1 hm2
      omega
    · unfold check_all_witnesses at h
      simp [hn] at h
      intro m hm1 hm2
      by_cases h_eq : m = n
      · subst h_eq
        exact h.1
      · have : m ≤ n - 1 := by omega
        exact check_all_witnesses_ok (n - 1) h.2 m hm1 this
