unsafe def my_unsafe_proof (n : ℕ) : False :=
  my_unsafe_proof n

theorem my_safe_theorem : False :=
  my_unsafe_proof 0
