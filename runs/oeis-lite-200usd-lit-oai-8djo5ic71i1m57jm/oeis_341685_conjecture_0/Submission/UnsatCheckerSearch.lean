import FormalConjectures.Util.ProblemImports
#eval show IO Unit from do
  let vals : List ℤ := [-5,-4,-3,-2,-1,0,1,2,3,4,5]
  for k in vals do
    for c in vals do
      let b := Int.Linear.Poly.isUnsatDvd k (.num c)
      if b && (decide (k ∣ c)) then
        IO.println s!"BUG dvd k={k} c={c}"
  for c in vals do
    let b := Int.Linear.Poly.isUnsatEq (.num c)
    if b && c == 0 then IO.println s!"BUG eq c={c}"
