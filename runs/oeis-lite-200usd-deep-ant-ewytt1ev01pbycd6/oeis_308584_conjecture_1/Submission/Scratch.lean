import FormalConjectures.Util.ProblemImports

open Nat Finset

def triangular_number (k : ℕ) : ℕ := k * (k + 1) / 2

lemma two_mul_tri (k : ℕ) : 2 * triangular_number k = k * (k + 1) := by
  unfold triangular_number
  exact Nat.mul_div_cancel' (even_mul_succ_self k).two_dvd

/-- Core identity: `4*(T a + T b) + 1 = (a+b+1)^2 + (a-b)^2` over `ℤ`. -/
lemma four_tri_add_one (a b : ℕ) :
    (4 * (triangular_number a + triangular_number b) + 1 : ℤ)
      = ((a : ℤ) + b + 1) ^ 2 + ((a : ℤ) - b) ^ 2 := by
  have hA : (2 * triangular_number a : ℤ) = (a : ℤ) * (a + 1) := by
    exact_mod_cast two_mul_tri a
  have hB : (2 * triangular_number b : ℤ) = (b : ℤ) * (b + 1) := by
    exact_mod_cast two_mul_tri b
  push_cast at hA hB ⊢
  linear_combination 2 * hA + 2 * hB

/-- If `4*m+1` is not a sum of two squares (in ℕ), then `m` is not a sum of two
triangular numbers. Only direction needed for a disproof. -/
lemma not_two_tri_of_not_sq_add_sq (m : ℕ)
    (h : ¬ ∃ x y : ℕ, 4 * m + 1 = x ^ 2 + y ^ 2) :
    ¬ ∃ a b : ℕ, triangular_number a + triangular_number b = m := by
  rintro ⟨a, b, hab⟩
  apply h
  refine ⟨a + b + 1, ((a : ℤ) - b).natAbs, ?_⟩
  have key := four_tri_add_one a b
  have hmcast : ((triangular_number a : ℤ) + (triangular_number b : ℤ)) = (m : ℤ) := by
    exact_mod_cast hab
  have hz : (4 * m + 1 : ℤ)
      = (((a + b + 1 : ℕ) : ℤ)) ^ 2 + ((((((a : ℤ) - b).natAbs) : ℕ) : ℤ)) ^ 2 := by
    push_cast
    push_cast at key hmcast
    rw [sq_abs]
    linarith [key, hmcast]
  exact_mod_cast hz

/-- A prime `q ≡ 3 (mod 4)` dividing `N` to odd multiplicity certifies `N` is not a
sum of two squares. -/
lemma not_sq_add_sq_of_bad_prime (N q : ℕ) (hN : N ≠ 0) (hq : q.Prime)
    (h3 : q % 4 = 3) (hdvd : q ∣ N) (hodd : ¬ Even (padicValNat q N)) :
    ¬ ∃ x y : ℕ, N = x ^ 2 + y ^ 2 := by
  rw [Nat.eq_sq_add_sq_iff]
  push_neg
  exact ⟨q, Nat.mem_primeFactors.mpr ⟨hq, hdvd, hN⟩, h3, hodd⟩

/-- Combined: a bad prime in `4m+1` shows `m` is not a sum of two triangular numbers. -/
lemma not_two_tri_of_bad_prime (m q : ℕ) (hq : q.Prime) (h3 : q % 4 = 3)
    (hdvd : q ∣ (4 * m + 1)) (hodd : ¬ Even (padicValNat q (4 * m + 1))) :
    ¬ ∃ a b : ℕ, triangular_number a + triangular_number b = m := by
  apply not_two_tri_of_not_sq_add_sq
  exact not_sq_add_sq_of_bad_prime (4 * m + 1) q (by positivity) hq h3 hdvd hodd

#print axioms not_two_tri_of_bad_prime

noncomputable def A308584 (n : ℕ) : ℕ :=
  let T := triangular_number
  let bound := n + 1
  let R := Finset.range bound
  let search_space : Finset (((ℕ × ℕ) × ℕ) × ℕ) :=
    ((R.product R).product R).product R
  (search_space.filter fun t =>
    let ab_pair := t.fst.fst
    let c         := t.fst.snd
    let d         := t.snd
    let a         := ab_pair.fst
    let b         := ab_pair.snd
    a ≤ b ∧ T a + T b + 5^c * 8^d = n
  ).card

/-- Structural disproof template: if for every `c,d` the residue `n - 5^c8^d` is not a
sum of two triangular numbers, then `A308584 n = 0`. -/
lemma A308584_eq_zero (n : ℕ)
    (H : ∀ c d : ℕ, 5 ^ c * 8 ^ d ≤ n →
      ¬ ∃ a b : ℕ, triangular_number a + triangular_number b = n - 5 ^ c * 8 ^ d) :
    A308584 n = 0 := by
  rw [A308584, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  rintro ⟨⟨⟨a, b⟩, c⟩, d⟩ _hmem hpred
  dsimp only at hpred
  obtain ⟨hab, heq⟩ := hpred
  have hle : 5 ^ c * 8 ^ d ≤ n := by omega
  exact H c d hle ⟨a, b, by omega⟩

#print axioms A308584_eq_zero
