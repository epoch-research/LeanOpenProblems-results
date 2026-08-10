import FormalConjectures.Util.ProblemImports
set_option maxRecDepth 200000
open Nat

def step1_check (r : ℕ) : Bool :=
  if (r * ((r + 1) % 80640)) % 80640 == 0 then
    r % 80640 == 0 || r % 80640 == 4095 || r % 80640 == 13824 || r % 80640 == 17919 ||
    r % 80640 == 28160 || r % 80640 == 30464 || r % 80640 == 32255 || r % 80640 == 34559 ||
    r % 80640 == 46080 || r % 80640 == 48384 || r % 80640 == 50175 || r % 80640 == 52479 ||
    r % 80640 == 62720 || r % 80640 == 66815 || r % 80640 == 76544 || r % 80640 == 80639
  else
    true

def step1_check_loop (n : ℕ) : Bool :=
  let rec loop (i : ℕ) : Bool :=
    if i < n then
      step1_check i && loop (i + 1)
    else
      true
  loop 0

lemma step1_check_loop_eq_true : step1_check_loop 80640 = true := by
  decide
