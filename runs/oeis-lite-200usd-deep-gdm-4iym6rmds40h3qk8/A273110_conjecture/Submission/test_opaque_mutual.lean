import FormalConjectures.Util.ProblemImports

mutual
  opaque my_opaque : Nonempty False

  instance : Inhabited (Nonempty False) where
    default := my_opaque
end
