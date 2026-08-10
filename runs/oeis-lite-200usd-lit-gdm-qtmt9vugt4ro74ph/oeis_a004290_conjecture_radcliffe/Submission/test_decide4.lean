import FormalConjectures.Util.ProblemImports

def check_digits_01 : List Nat -> Bool
  | [] => true
  | d :: ds => (d == 0 || d == 1) && check_digits_01 ds

theorem check_digits_01_ok : ∀ (l : List Nat), check_digits_01 l = true -> ∀ d ∈ l, d = 0 ∨ d = 1
  | [], _ => by intro d hd; contradiction
  | d' :: ds, h => by
    simp [check_digits_01] at h
    intro d hd
    cases hd with
    | head => exact h.1
    | tail _ h_mem => exact check_digits_01_ok ds h.2 d h_mem
