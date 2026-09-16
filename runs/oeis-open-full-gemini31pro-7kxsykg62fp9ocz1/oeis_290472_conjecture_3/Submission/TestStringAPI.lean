def test_get (s : String) (i : Nat) : Char :=
  s.get! ⟨i⟩

#eval test_get "ABC" 1
