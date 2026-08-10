import FormalConjectures.Util.ProblemImports

#check not_nat_primrec_ack_self
#check Nat.Primrec
#check ack
example : Nat.Primrec (fun n => ack n n) := by
  try infer_instance
  try fun_prop
  try simp
  try exact Nat.Primrec.id

#check ZMod.not_isCyclic_units_eight
example : IsCyclic (ZMod 8)ˣ := by
  try infer_instance
  try constructor

#check CartanMatrix.not_isSimplyLaced_G₂
example : Matrix.IsSimplyLaced CartanMatrix.G₂ := by
  try decide
  try simp [Matrix.IsSimplyLaced]
