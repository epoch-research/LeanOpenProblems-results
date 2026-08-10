import FormalConjectures.Util.ProblemImports
#eval show IO Unit from do
  let vals : List ℤ := [-4,-3,-2,-1,0,1,2,3,4]
  let mods : List ℤ := [-4,-3,-2,-1,0,1,2,3,4]
  for a in vals do
    for c in vals do
      let p : Int.Linear.Poly := .add a 0 (.num c)
      for x in vals do
        let ctx : Int.Linear.Context := Lean.RArray.ofFn (fun _ : Fin 1 => x) (by decide)
        let den := Int.Linear.Poly.denote' ctx p
        if Int.Linear.Poly.isUnsatEq p && den = 0 then
          IO.println s!"BUG eq a={a} c={c} x={x} den={den}"
        for m in mods do
          if Int.Linear.Poly.isUnsatDvd m p && (decide (m ∣ den)) then
            IO.println s!"BUG dvd m={m} a={a} c={c} x={x} den={den}"
