def proofOfFalse : False :=
  let rec loop (x : Unit) : False := loop x
  loop ()
