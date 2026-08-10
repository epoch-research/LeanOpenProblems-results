import FormalConjectures.Util.ProblemImports

-- direct self reference in theorem
-- theorem t1 : False := t1

-- opaque self reference
-- opaque t2 : False := t2

mutual
  theorem mt1 : False := mt2
  theorem mt2 : False := mt1
end

#print axioms mt1
#print axioms mt2
