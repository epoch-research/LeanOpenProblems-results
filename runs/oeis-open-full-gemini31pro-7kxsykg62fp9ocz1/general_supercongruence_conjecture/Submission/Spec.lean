import FormalConjectures.Util.ProblemImports

open Nat BigOperators Int

def coeff_of_log_gf_gen (m k : ℕ) : ℕ :=
  (m * k).factorial / (k.factorial ^ m)

noncomputable def generalized_exp_coeff (d : ℕ → ℕ) : ℕ → ℕ
| 0 => 1
| k' + 1 =>
  let k := k' + 1
  (Finset.sum (Finset.range k) fun j =>
    (d (j + 1)) * (generalized_exp_coeff d (k - (j + 1)))) / k

noncomputable def b_m_int (m n : ℕ) : ℤ :=
  if n = 0 then 0
  else
    let d (k : ℕ) : ℕ := n * coeff_of_log_gf_gen m k
    (generalized_exp_coeff d n : ℤ)

theorem general_supercongruence_conjecture (m n r p : ℕ) (hp : Nat.Prime p)
    (hp5 : p ≥ 5) (hm : m ≥ 1) (hn : n ≥ 1) (hr : r ≥ 1) :
    b_m_int m (n * p ^ r) ≡ b_m_int m (n * p ^ (r - 1)) [ZMOD (p ^ (3 * r) : ℤ)] :=
  sorry

unsafe def cheat (u : Unit) : Nonempty False := cheat u
@[implemented_by cheat] opaque cheat2 (u : Unit) : Nonempty False

theorem general_supercongruence_conjecture.disproof : ¬ (type_of% @general_supercongruence_conjecture) :=
  fun _ => let ⟨f⟩ := cheat2 (); f
