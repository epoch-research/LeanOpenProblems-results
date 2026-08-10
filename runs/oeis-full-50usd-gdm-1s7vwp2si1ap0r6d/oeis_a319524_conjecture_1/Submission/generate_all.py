import sympy

def generate_proofs():
    primes = list(sympy.primerange(2, 100000))
    
    # We want y > 7.
    # index of prime(y) is y in 0-indexed mathlib list, since prime(1) = 2 (index 0).
    # Wait! Let's verify the indexing in Spec.lean:
    # let Pn := p (n-1), Pnp1 := p n, Pnp2 := p (n+1)
    # Inside Spec.lean, for y, we have:
    # P1 = p (y-1)
    # P2 = p y
    # P3 = p (y+1)
    # P4 = p (y+2)
    # So P1 = primes[y-1], P2 = primes[y], P3 = primes[y+1], P4 = primes[y+2]
    # Let's check:
    # for y = 9:
    # P1 = primes[8] = 23
    # P2 = primes[9] = 29
    # P3 = primes[10] = 31
    # P4 = primes[11] = 37
    # This matches no_sol_y_9 in Spec.lean:
    # h1 : 23 + m * 29 = 29 + m' * 31
    # h2 : 29 + m' * 31 = 31 + k' * 37
    # Matches perfectly!
    
    solutions = []
    for y in range(8, len(primes)-3):
        P1 = primes[y-1]
        P2 = primes[y]
        P3 = primes[y+1]
        P4 = primes[y+2]
        d0 = P2 - P1
        d1 = P3 - P2
        d2 = P4 - P3
        lhs = 2 * P2
        rhs = d2 * d0 + d1 * (d2 - 2) * (d1 + d2) - d1*d1
        if lhs <= rhs:
            solutions.append((y, P1, P2, P3, P4, d0, d1, d2))
            
    print(f"Found {len(solutions)} solutions > 7.")
    
    out = []
    for y, P1, P2, P3, P4, d0, d1, d2 in solutions:
        # Find D_sol: unique D in 1..d1 such that (D * P2 - d0) % d1 == 0
        D_sol = None
        for D in range(1, d1 + 1):
            if (D * P2 - d0) % d1 == 0:
                D_sol = D
                break
        assert D_sol is not None, f"No D_sol found for y={y}"
        m_prime_sol = (D_sol * P2 - d0) // d1
        
        cases_str = " ∨ ".join(f"D = {i}" for i in range(1, d1 + 1))
        
        rcases_branches = []
        for i in range(1, d1 + 1):
            if i == D_sol:
                rcases_branches.append("    · rfl")
            else:
                rcases_branches.append("    · revert h_alg; omega")
        rcases_str = "\n".join(rcases_branches)
        
        proof = f"""theorem no_sol_y_{y} (m m' k' : ℕ)
  (h1 : {P1} + m * {P2} = {P2} + m' * {P3})
  (h2 : {P2} + m' * {P3} = {P3} + k' * {P4})
  (hm' : m' < {P2}) : False := by
  have h_m_gt : m > m' := by
    by_contra h_le
    push_neg at h_le
    have h_le_mul : m * {P2} ≤ m' * {P2} := Nat.mul_le_mul_right {P2} h_le
    have h_le_mul2 : m' * {P2} ≤ m' * {P3} := Nat.mul_le_mul_left m' (by decide)
    have h_step1 : {P1} + m * {P2} ≤ {P1} + m' * {P2} := Nat.add_le_add_left h_le_mul {P1}
    have h_step2 : {P1} + m' * {P2} ≤ {P1} + m' * {P3} := Nat.add_le_add_left h_le_mul2 {P1}
    have h_step3 : {P1} + m' * {P3} < {P2} + m' * {P3} := Nat.add_lt_add_right (by decide : {P1} < {P2}) _
    have h_lt : {P1} + m * {P2} < {P2} + m' * {P3} := h_step1.trans_lt (h_step2.trans_lt h_step3)
    exact (h_lt.ne h1).elim
  generalize h_D : m - m' = D
  have h_alg : D * {P2} = {d1} * m' + {d0} := by
    have h_eq : m * {P2} = m' * {P2} + D * {P2} := by
      rw [← h_D]
      rw [← Nat.add_mul, Nat.add_comm, Nat.sub_add_cancel (Nat.le_of_lt h_m_gt)]
    have h1' := h1
    rw [h_eq] at h1'
    have h_dist : m' * {P3} = m' * {P2} + {d1} * m' := by
      rw [show {P3} = {P2} + {d1} by decide, Nat.mul_add, Nat.mul_comm m' {d1}]
    rw [h_dist] at h1'
    have h1_assoc : ({P1} + D * {P2}) + m' * {P2} = ({P2} + {d1} * m') + m' * {P2} := by
      calc ({P1} + D * {P2}) + m' * {P2} = {P1} + (D * {P2} + m' * {P2}) := by rw [Nat.add_assoc]
      _ = {P1} + (m' * {P2} + D * {P2}) := by rw [Nat.add_comm (D * {P2})]
      _ = {P2} + (m' * {P2} + {d1} * m') := h1'
      _ = {P2} + ({d1} * m' + m' * {P2}) := by rw [Nat.add_comm (m' * {P2})]
      _ = ({P2} + {d1} * m') + m' * {P2} := by rw [Nat.add_assoc]
    have h1_sub := Nat.add_right_cancel h1_assoc
    have h1_sub_eq : {P1} + D * {P2} = {P1} + ({d1} * m' + {d0}) := by
      calc {P1} + D * {P2} = ({P1} + D * {P2}) := rfl
      _ = {P2} + {d1} * m' := h1_sub
      _ = {P1} + {d0} + {d1} * m' := rfl
      _ = {P1} + ({d0} + {d1} * m') := by rw [Nat.add_assoc]
      _ = {P1} + ({d1} * m' + {d0}) := by rw [Nat.add_comm {d0}]
    exact Nat.add_left_cancel h1_sub_eq
  have hD_le : D ≤ {d1} := by
    by_contra h_gt
    push_neg at h_gt
    have h1 : D * {P2} ≥ {d1 + 1} * {P2} := Nat.mul_le_mul_right {P2} h_gt
    have h2 : {d1} * m' + {d0} < {d1 + 1} * {P2} := by
      have : {d1} * m' < {d1} * {P2} := Nat.mul_lt_mul_of_pos_left hm' (by decide)
      have : {d1} * m' + {d0} < {d1} * {P2} + {d0} := Nat.add_lt_add_right this {d0}
      calc {d1} * m' + {d0} < {d1} * {P2} + {d0} := this
      _ ≤ {d1 + 1} * {P2} := by decide
    have h_lt : {d1 + 1} * {P2} < {d1 + 1} * {P2} := by
      calc {d1 + 1} * {P2} ≤ D * {P2} := h1
      _ = {d1} * m' + {d0} := h_alg
      _ < {d1 + 1} * {P2} := h2
    exact h_lt.ne rfl
  have hD_pos : 1 ≤ D := by
    rw [← h_D]
    exact Nat.sub_pos_of_lt h_m_gt
  have h_cases : {cases_str} := by
    clear h1 h2 hm' h_m_gt h_D h_alg
    omega
  have h_D_eq : D = {D_sol} := by
    clear h1 h2 hm' h_m_gt h_D
    rcases h_cases with {" | ".join(["rfl"] * d1)}
{rcases_str}
  have hm'_eq : m' = {m_prime_sol} := by
    have h_alg_sol : {D_sol} * {P2} = {d1} * m' + {d0} := h_D_eq ▸ h_alg
    have h_eval : {D_sol} * {P2} = {D_sol * P2} := by decide
    rw [h_eval] at h_alg_sol
    have h_sub : {D_sol * P2 - d0} = {d1} * m' := by
      calc {D_sol * P2 - d0} = {D_sol * P2} - {d0} := rfl
      _ = {d1} * m' + {d0} - {d0} := by rw [h_alg_sol]
      _ = {d1} * m' := rfl
    have h_div : {D_sol * P2 - d0} / {d1} = ({d1} * m') / {d1} := by rw [h_sub]
    rw [Nat.mul_div_cancel_left m' (by decide : 0 < {d1})] at h_div
    have h_div_eval : {D_sol * P2 - d0} / {d1} = {m_prime_sol} := by decide
    exact h_div.symm.trans h_div_eval
  rw [hm'_eq] at h2
  revert h2
  intro h2'
  omega"""
        out.append(proof)
    
    with open("/workspace/leanproject/Submission/all_proofs.lean", "w") as f:
        f.write("import FormalConjectures.Util.ProblemImports\nopen Nat\n\n")
        f.write("\n\n".join(out))
        f.write("\n")

if __name__ == '__main__':
    generate_proofs()
