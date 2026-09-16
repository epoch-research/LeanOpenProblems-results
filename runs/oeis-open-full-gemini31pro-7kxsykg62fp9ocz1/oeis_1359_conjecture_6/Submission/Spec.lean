import FormalConjectures.Util.ProblemImports
import Submission.PrimeProof
import Submission.AD

open Nat Finset Nat.ModEq ZMod

/--
A001359 Lesser of twin primes.
-/
noncomputable def a (n : ℕ) : ℕ :=
  if h : n > 0 then
    (n - 1).nth (fun p => Nat.Prime p ∧ Nat.Prime (p + 2))
  else
    0

lemma logic_helper {A B K C D : Prop} (h1 : C ↔ ¬ B) (h2 : B → A) (h3 : B → D) (h4 : C → (A ↔ D)) (h5 : K → A) :
  A ↔ B ∨ K ∨ (C ∧ D) := by
  tauto

lemma B_to_gap {k : ℕ} (hk : k > 1) :
  let Pk := Nat.nth Nat.Prime (k - 1);
  let Pk_succ := Nat.nth Nat.Prime k;
  Nat.Prime (Pk + 2) → Pk_succ - Pk = 2 := by
  intro Pk Pk_succ hB
  have hp : Nat.Prime Pk := Nat.nth_mem_of_infinite Nat.infinite_setOf_prime (k - 1)
  have hq : Nat.Prime Pk_succ := Nat.nth_mem_of_infinite Nat.infinite_setOf_prime k
  have hp_lt_q : Pk < Pk_succ := (Nat.nth_lt_nth Nat.infinite_setOf_prime).mpr (by omega)
  have h_next : ∀ x, Pk < x → x < Pk_succ → ¬ Nat.Prime x := by
    intro x hx1 hx2 hx_prime
    have hm : Nat.nth Nat.Prime (count Nat.Prime x) = x := Nat.nth_count hx_prime
    have hm1 : Pk < Nat.nth Nat.Prime (count Nat.Prime x) := by omega
    have hm2 : Nat.nth Nat.Prime (count Nat.Prime x) < Pk_succ := by omega
    have hm1' : k - 1 < count Nat.Prime x := (Nat.nth_lt_nth Nat.infinite_setOf_prime).mp hm1
    have hm2' : count Nat.Prime x < k := (Nat.nth_lt_nth Nat.infinite_setOf_prime).mp hm2
    omega
  have h_q_le : Pk_succ ≤ Pk + 2 := by
    by_contra! hc
    have h1 : Pk < Pk + 2 := by omega
    have h2 : Pk + 2 < Pk_succ := hc
    exact h_next (Pk + 2) h1 h2 hB
  have h_not_P_plus_1 : ¬ Nat.Prime (Pk + 1) := by
    intro hc
    have h_pk_ge_3 : Pk ≥ 3 := by
      have h_k_ge : k - 1 ≥ 1 := by omega
      have h1 : Nat.nth Nat.Prime 1 = 3 := by norm_num
      have h3 : Nat.nth Nat.Prime 1 ≤ Nat.nth Nat.Prime (k - 1) := (Nat.nth_le_nth Nat.infinite_setOf_prime).mpr h_k_ge
      omega
    have h_odd : Pk % 2 = 1 := (Nat.Prime.eq_two_or_odd hp).resolve_left (by omega)
    have hc_odd : (Pk + 1) % 2 = 1 := (Nat.Prime.eq_two_or_odd hc).resolve_left (by omega)
    omega
  have h_eq : Pk_succ = Pk + 2 := by
    have h1 : Pk_succ = Pk + 1 ∨ Pk_succ = Pk + 2 := by omega
    rcases h1 with eq1 | eq2
    · rw [eq1] at hq; exact False.elim (h_not_P_plus_1 hq)
    · exact eq2
  omega

/--
Conjecture: A001359 Primes `prime(k)` such that `prime(k)! == 1 (mod prime(k+1))` with the exception of
`prime(991) = 7841` and other unknown primes `prime(k)` for which
`(prime(k)+1)*(prime(k)+2)*...*(prime(k+1)-2) == 1 (mod prime(k+1))` where `prime(k+1) - prime(k) > 2`.
Here, `prime(k)` denotes the k-th prime number (1-indexed, so prime(k) = Nat.nth Nat.Prime (k-1) for k > 0).
-/
theorem oeis_1359_conjecture_6 :
  -- k is the 1-based index. We start with k > 1, corresponding to the first twin prime 3 (P_2).
  ∀ (k : ℕ), k > 1 →
  let Pk      := Nat.nth Nat.Prime (k - 1); -- Pk is the k-th prime
  let Pk_succ := Nat.nth Nat.Prime k;       -- Pk_succ is the (k+1)-th prime
  let Congruence := Nat.factorial Pk ≡ 1 [MOD Pk_succ];
  let IsLesserTwinPrime := Nat.Prime (Pk + 2);

  -- The product Wk_prod is $\prod_{i=P_k+1}^{P_{k+1}-2} i$. This defines the value W_k in the OEIS comment.
  let Wk_prod : ℕ := Finset.prod (Finset.Icc (Pk + 1) (Pk_succ - 2)) id;

  -- The set of primes satisfying the congruence is the set of lesser twin primes
  -- union the set of exceptional indices C \ T.
  Iff Congruence (
    IsLesserTwinPrime ∨
    (k = 991) ∨
    (Pk_succ - Pk > 2 ∧ Wk_prod ≡ 1 [MOD Pk_succ])
  )
:= by
  intro k hk
  -- abbreviations for readability
  let Pk := Nat.nth Nat.Prime (k - 1)
  let Pk_succ := Nat.nth Nat.Prime k
  let Cong := Pk.factorial ≡ 1 [MOD Pk_succ]
  let B := Nat.Prime (Pk + 2)
  let K := k = 991
  let W := Finset.prod (Finset.Icc (Pk + 1) (Pk_succ - 2)) id
  let C := Pk_succ - Pk > 2
  let D := W ≡ 1 [MOD Pk_succ]
  change Cong ↔ B ∨ K ∨ (C ∧ D)

  have hp : Nat.Prime Pk := Nat.nth_mem_of_infinite Nat.infinite_setOf_prime (k - 1)
  have hq : Nat.Prime Pk_succ := Nat.nth_mem_of_infinite Nat.infinite_setOf_prime k
  have hp_lt_q : Pk < Pk_succ := (Nat.nth_lt_nth Nat.infinite_setOf_prime).mpr (by omega)
  
  have h_C_iff_not_B : C ↔ ¬ B := by
    constructor
    · intro hC hB
      have gap : Pk_succ - Pk = 2 := B_to_gap hk hB
      change Pk_succ - Pk > 2 at hC
      omega
    · intro hnB
      have gap_gt_1 : Pk_succ - Pk > 1 := by
        have h_not_P_plus_1 : ¬ Nat.Prime (Pk + 1) := by
          intro hc
          have h_pk_ge_3 : Pk ≥ 3 := by
            have h_k_ge : k - 1 ≥ 1 := by omega
            have h1 : Nat.nth Nat.Prime 1 = 3 := by norm_num
            have h3 : Nat.nth Nat.Prime 1 ≤ Nat.nth Nat.Prime (k - 1) := (Nat.nth_le_nth Nat.infinite_setOf_prime).mpr h_k_ge
            omega
          have h_odd : Pk % 2 = 1 := (Nat.Prime.eq_two_or_odd hp).resolve_left (by omega)
          have hc_odd : (Pk + 1) % 2 = 1 := (Nat.Prime.eq_two_or_odd hc).resolve_left (by omega)
          omega
        by_contra! hc
        have : Pk_succ = Pk + 1 := by omega
        rw [this] at hq
        exact h_not_P_plus_1 hq
      change Pk_succ - Pk > 2
      by_contra! hc
      have : Pk_succ - Pk = 2 := by omega
      have hB_true : B := by
        change Nat.Prime (Pk + 2)
        have : Pk + 2 = Pk_succ := by omega
        rw [this]
        exact hq
      exact hnB hB_true

  have h_B_to_A : B → Cong := by
    intro hB
    have gap : Pk_succ - Pk = 2 := B_to_gap hk hB
    exact B_implies_A Pk Pk_succ hp hq gap

  have h_B_to_D : B → D := by
    intro hB
    have gap : Pk_succ - Pk = 2 := B_to_gap hk hB
    exact B_implies_D Pk Pk_succ gap

  have h_C_to_equiv : C → (Cong ↔ D) := by
    intro hC
    exact AD_equiv Pk Pk_succ hp hq hC

  have h_K_to_A : K → Cong := by
    intro hK
    have h_k_eq : k = 991 := hK
    have h_Pk : Pk = 7841 := by
      subst h_k_eq
      change Nat.nth Nat.Prime 990 = 7841
      exact p991
    have h_Pk_succ : Pk_succ = 7853 := by
      subst h_k_eq
      change Nat.nth Nat.Prime 991 = 7853
      exact p992
    change Pk.factorial ≡ 1 [MOD Pk_succ]
    rw [h_Pk, h_Pk_succ]
    have fact_mod : 7841! ≡ 1 [MOD 7853] := by norm_num
    exact fact_mod

  exact logic_helper h_C_iff_not_B h_B_to_A h_B_to_D h_C_to_equiv h_K_to_A

theorem oeis_1359_conjecture_6.disproof : ¬ (type_of% @oeis_1359_conjecture_6) := sorry
