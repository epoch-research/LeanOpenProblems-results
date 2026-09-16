import Submission.DivIneqInt
import Mathlib

lemma int_div_bound (A M : ℤ) (hM : 0 < M) : (A / M) * M ≤ A ∧ A < (A / M) * M + M := by
  have h1 : A % M ≥ 0 := Int.emod_nonneg A hM.ne'
  have h2 : A % M < M := Int.emod_lt_of_pos A hM
  have h3 : A = (A / M) * M + A % M := by
    calc A = M * (A / M) + A % M := (Int.mul_ediv_add_emod A M).symm
         _ = (A / M) * M + A % M := by ring
  omega

lemma div_ineq_nat (n r M : ℕ) (hM : 0 < M) (hr : r ≤ 4 * n) :
    (4 * n - r) / M + (3 * n) / M + (2 * n) / M ≤ (8 * n - 2 * r) / M + (8 * r) / M + n / M := by
  have hr8 : 2 * r ≤ 8 * n := by omega
  have hM_int : 0 < (M : ℤ) := by omega
  have hn_int : 0 ≤ (n : ℤ) := by omega
  have hr_int : 0 ≤ (r : ℤ) := by omega
  zify [hr, hr8]
  generalize (n : ℤ) = n' at *
  generalize (r : ℤ) = r' at *
  generalize (M : ℤ) = M' at *

  let q1 := (4 * n' - r') / M'
  let q2 := (3 * n') / M'
  let q3 := (2 * n') / M'
  let p1 := (8 * n' - 2 * r') / M'
  let p2 := (8 * r') / M'
  let nq := n' / M'
  let rq := r' / M'

  have hrq_pos : 0 ≤ rq := Int.ediv_nonneg hr_int (by omega)
  
  have hnq : nq * M' ≤ n' ∧ n' < nq * M' + M' := int_div_bound n' M' hM_int
  have hrq : rq * M' ≤ r' ∧ r' < rq * M' + M' := int_div_bound r' M' hM_int

  let un := n' - nq * M'
  let ur := r' - rq * M'

  let q1' := q1 - (4 * nq - rq)
  let q2' := q2 - 3 * nq
  let q3' := q3 - 2 * nq
  let p1' := p1 - (8 * nq - 2 * rq)
  let p2' := p2 - 8 * rq

  have h_un : 0 ≤ un ∧ un < M' := by
    dsimp [un]
    omega
  have h_ur : 0 ≤ ur ∧ ur < M' := by
    dsimp [ur]
    omega

  have hq1 : q1 * M' ≤ 4 * n' - r' ∧ 4 * n' - r' < q1 * M' + M' := int_div_bound (4 * n' - r') M' hM_int
  have h_q1'_le : q1' * M' ≤ 4 * un - ur := by
    dsimp [q1', un, ur]
    calc q1' * M' = q1 * M' - 4 * (nq * M') + (rq * M') := by ring
    _ ≤ (4 * n' - r') - 4 * (nq * M') + (rq * M') := by omega
    _ = 4 * (n' - nq * M') - (r' - rq * M') := by ring
    
  have h_q1'_lt : 4 * un - ur < q1' * M' + M' := by
    dsimp [q1', un, ur]
    calc 4 * (n' - nq * M') - (r' - rq * M') = (4 * n' - r') - 4 * (nq * M') + (rq * M') := by ring
    _ < (q1 * M' + M') - 4 * (nq * M') + (rq * M') := by omega
    _ = (q1 - (4 * nq - rq)) * M' + M' := by ring

  have hq2 : q2 * M' ≤ 3 * n' ∧ 3 * n' < q2 * M' + M' := int_div_bound (3 * n') M' hM_int
  have h_q2'_le : q2' * M' ≤ 3 * un := by
    dsimp [q2', un]
    calc q2' * M' = q2 * M' - 3 * (nq * M') := by ring
    _ ≤ 3 * n' - 3 * (nq * M') := by omega
    _ = 3 * (n' - nq * M') := by ring
  have h_q2'_lt : 3 * un < q2' * M' + M' := by
    dsimp [q2', un]
    calc 3 * (n' - nq * M') = 3 * n' - 3 * (nq * M') := by ring
    _ < (q2 * M' + M') - 3 * (nq * M') := by omega
    _ = (q2 - 3 * nq) * M' + M' := by ring

  have hq3 : q3 * M' ≤ 2 * n' ∧ 2 * n' < q3 * M' + M' := int_div_bound (2 * n') M' hM_int
  have h_q3'_le : q3' * M' ≤ 2 * un := by
    dsimp [q3', un]
    calc q3' * M' = q3 * M' - 2 * (nq * M') := by ring
    _ ≤ 2 * n' - 2 * (nq * M') := by omega
    _ = 2 * (n' - nq * M') := by ring
  have h_q3'_lt : 2 * un < q3' * M' + M' := by
    dsimp [q3', un]
    calc 2 * (n' - nq * M') = 2 * n' - 2 * (nq * M') := by ring
    _ < (q3 * M' + M') - 2 * (nq * M') := by omega
    _ = (q3 - 2 * nq) * M' + M' := by ring

  have hp1 : p1 * M' ≤ 8 * n' - 2 * r' ∧ 8 * n' - 2 * r' < p1 * M' + M' := int_div_bound (8 * n' - 2 * r') M' hM_int
  have h_p1'_le : p1' * M' ≤ 8 * un - 2 * ur := by
    dsimp [p1', un, ur]
    calc p1' * M' = p1 * M' - 8 * (nq * M') + 2 * (rq * M') := by ring
    _ ≤ (8 * n' - 2 * r') - 8 * (nq * M') + 2 * (rq * M') := by omega
    _ = 8 * (n' - nq * M') - 2 * (r' - rq * M') := by ring
  have h_p1'_lt : 8 * un - 2 * ur < p1' * M' + M' := by
    dsimp [p1', un, ur]
    calc 8 * (n' - nq * M') - 2 * (r' - rq * M') = (8 * n' - 2 * r') - 8 * (nq * M') + 2 * (rq * M') := by ring
    _ < (p1 * M' + M') - 8 * (nq * M') + 2 * (rq * M') := by omega
    _ = (p1 - (8 * nq - 2 * rq)) * M' + M' := by ring

  have hp2 : p2 * M' ≤ 8 * r' ∧ 8 * r' < p2 * M' + M' := int_div_bound (8 * r') M' hM_int
  have h_p2'_le : p2' * M' ≤ 8 * ur := by
    dsimp [p2', ur]
    calc p2' * M' = p2 * M' - 8 * (rq * M') := by ring
    _ ≤ 8 * r' - 8 * (rq * M') := by omega
    _ = 8 * (r' - rq * M') := by ring
  have h_p2'_lt : 8 * ur < p2' * M' + M' := by
    dsimp [p2', ur]
    calc 8 * (r' - rq * M') = 8 * r' - 8 * (rq * M') := by ring
    _ < (p2 * M' + M') - 8 * (rq * M') := by omega
    _ = (p2 - 8 * rq) * M' + M' := by ring

  have H := div_ineq_int un ur M' hM_int h_un.1 h_un.2 h_ur.1 h_ur.2 q1' ⟨h_q1'_le, h_q1'_lt⟩ q2' ⟨h_q2'_le, h_q2'_lt⟩ q3' ⟨h_q3'_le, h_q3'_lt⟩ p1' ⟨h_p1'_le, h_p1'_lt⟩ p2' ⟨h_p2'_le, h_p2'_lt⟩

  revert H
  dsimp [q1', q2', q3', p1', p2']
  intro H
  omega
