import FormalConjectures.Util.ProblemImports

unsafe instance fakeDecFalse : Decidable False := isTrue lcProof

-- direct decide should be unsafe-invalid if it unfolds proof
-- theorem t1 : False := by decide

-- native_decide may erase proof field; test kernel/axioms
set_option maxHeartbeats 2000000
theorem t2 : False := by
  native_decide
#print axioms t2
#print t2
