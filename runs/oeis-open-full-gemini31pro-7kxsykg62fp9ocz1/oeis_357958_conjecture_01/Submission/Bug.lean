inductive Bad : Type
| mk : (Bad → False) → Bad

def bad_to_false (b : Bad) : False :=
  match b with
  | Bad.mk f => f b

def false_of_bad : False :=
  let b := Bad.mk bad_to_false
  bad_to_false b
