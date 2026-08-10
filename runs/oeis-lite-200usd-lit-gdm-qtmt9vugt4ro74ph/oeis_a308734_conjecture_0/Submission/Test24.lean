import FormalConjectures.Util.ProblemImports

mutual
  def f : Nat → False
    | 0 => g 0
    | n + 1 => f n
  def g : Nat → False
    | 0 => f 0
    | n + 1 => g n
end
