import FormalConjectures.Util.ProblemImports
open Int.Linear
#reduce (Poly.num (0:ℤ)).isUnsatEq
#reduce (Poly.num (1:ℤ)).isUnsatEq
#reduce (Poly.num (0:ℤ)).isUnsatDiseq_k
#reduce (Poly.num (1:ℤ)).isUnsatDiseq_k
#reduce (Poly.num (0:ℤ)).isUnsatLe
#reduce (Poly.num (1:ℤ)).isUnsatLe
#reduce (Poly.num (-1:ℤ)).isUnsatLe
#reduce eq_unsat_coeff_cert (Poly.num (0:ℤ)) 1
#reduce eq_unsat_coeff_cert (Poly.num (1:ℤ)) 1
