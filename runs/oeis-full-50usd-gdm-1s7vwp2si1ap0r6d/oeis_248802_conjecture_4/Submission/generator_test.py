import sys
from sympy import isprime, divisors

# Find all primes < 1399
primes = [p for p in range(2, 100) if isprime(p)]

lean_code = []
lean_code.append("""/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/""")
lean_code.append("")
lean_code.append("import FormalConjectures.Util.ProblemImports")
lean_code.append("")
lean_code.append("set_option maxRecDepth 3000000")
lean_code.append("set_option maxHeartbeats 1000000")
lean_code.append("set_option exponentiation.threshold 100000")
lean_code.append("set_option linter.all false")
lean_code.append("set_option linter.unusedVariables false")
lean_code.append("set_option linter.style.namespace false")
lean_code.append("set_option linter.style.copyright.formalConjectures false")
lean_code.append("set_option linter.style.ams_attribute false")
lean_code.append("set_option linter.style.answer_attribute false")
lean_code.append("set_option linter.style.category_docstring false")
lean_code.append("set_option linter.style.category_attribute false")
lean_code.append("set_option linter.style.existsImplication false")
lean_code.append("set_option linter.style.moduleDocstring false")
lean_code.append("")
lean_code.append("/--")
lean_code.append("A248802: Smallest prime factor of $2^{(2^n+2)} + 3$.")
lean_code.append("-/")
lean_code.append("def a (n : ℕ) : ℕ := (2 ^ (2 ^ n + 2) + 3).minFac")
lean_code.append("")
lean_code.append("-- Helper definitions for the \"covered\" conditions based on the index k, where k = 58*n + 26.")
lean_code.append("")
lean_code.append("/-- An index k is covered by Conjecture 1 if k = 10m + 2 for some m >= 0, predicting a(k)=67. -/")
lean_code.append("def covered_by_C1 (k : ℕ) : Prop := ∃ m : ℕ, k = 10 * m + 2")
lean_code.append("")
lean_code.append("/-- An index k is covered by Conjecture 2 if k = 36m + 16 for some m >= 0, and m is not 1 mod 5, predicting a(k)=271. -/")
lean_code.append("def covered_by_C2 (k : ℕ) : Prop := ∃ m : ℕ, k = 36 * m + 16 ∧ m % 5 ≠ 1")
lean_code.append("")
lean_code.append("/-- An index k is covered by Conjecture 3 if k = 84m + 22 for some m >= 0, and m is not 0 mod 5, predicting a(k)=523. -/")
lean_code.append("def covered_by_C3 (k : ℕ) : Prop := ∃ m : ℕ, k = 84 * m + 22 ∧ m % 5 ≠ 0")
lean_code.append("")

# Common helper lemmas
lean_code.append("""lemma pow_induction (d e o : ℕ) (h_base : (2 ^ d * 2 ^ e) % o = 2 ^ e % o) (j : ℕ) :
    ((2 ^ d) ^ j * 2 ^ e) % o = 2 ^ e % o := by
  induction j with
  | zero =>
    rw [pow_zero, one_mul]
  | succ j ih =>
    have h_eq : (2 ^ d) ^ (j + 1) * 2 ^ e = (2 ^ d) ^ j * (2 ^ d * 2 ^ e) := by
      calc (2 ^ d) ^ (j + 1) * 2 ^ e
        _ = ((2 ^ d) ^ j * 2 ^ d) * 2 ^ e := by rw [pow_succ]
        _ = (2 ^ d) ^ j * (2 ^ d * 2 ^ e) := by ring
    rw [h_eq]
    rw [Nat.mul_mod]
    rw [h_base]
    rw [← Nat.mul_mod]
    exact ih

lemma pow_mod_of_mod_eq (n L r d e o : ℕ) (hd : d = 58 * L) (he : e = 58 * r + 26) (hn : n % L = r)
    (h_base : (2 ^ d * 2 ^ e) % o = 2 ^ e % o) :
    2 ^ (58 * n + 26) % o = 2 ^ (58 * r + 26) % o := by
  have h_div_mod := Nat.div_add_mod n L
  rw [hn] at h_div_mod
  have h_eq : 58 * n + 26 = d * (n / L) + e := by
    subst hd he
    have h_L : 58 * n + 26 = 58 * (L * (n / L) + r) + 26 := congr_arg (fun x => 58 * x + 26) h_div_mod.symm
    rw [h_L]
    ring
  rw [h_eq]
  rw [pow_add, pow_mul]
  have h_ind := pow_induction d e o h_base (n / L)
  rw [h_ind]
  subst he
  rfl

lemma dvd_mod_of_dvd_of_dvd (g a b : ℕ) (ha : g ∣ a) (hb : g ∣ b) : g ∣ a % b := by
  rcases ha with ⟨ka, rfl⟩
  rcases hb with ⟨kb, rfl⟩
  by_cases hb0 : kb = 0
  · subst hb0
    simp
  · have h_eq : (g * ka) % (g * kb) = g * (ka % kb) := Nat.mul_mod_mul_left g ka kb
    rw [h_eq]
    exact dvd_mul_right g (ka % kb)

lemma pow_two_mod_233 (n : ℕ) : (2 : ZMod 233) ^ (58 * n + 26) = 204 := by
  have h_eq : 58 * n + 26 = 29 * (2 * n) + 26 := by omega
  rw [h_eq]
  rw [pow_add, pow_mul]
  have h29 : (2 : ZMod 233) ^ 29 = 1 := by decide
  rw [h29]
  rw [one_pow]
  rw [one_mul]
  decide

lemma pow_two_mod_233_nat (n : ℕ) : 2 ^ (58 * n + 26) % 233 = 204 := by
  have h := pow_two_mod_233 n
  have h_val := congr_arg ZMod.val h
  have h_cast : ((2 : ZMod 233) ^ (58 * n + 26)).val = (2 ^ (58 * n + 26) : ℕ) % 233 := by
    have h_hom : (2 : ZMod 233) ^ (58 * n + 26) = ((2 ^ (58 * n + 26) : ℕ) : ZMod 233) := by push_cast; rfl
    rw [h_hom]
    rw [ZMod.val_natCast]
  rw [h_cast] at h_val
  have h_rhs : (204 : ZMod 233).val = 204 := by decide
  rw [h_rhs] at h_val
  exact h_val

lemma pow_two_mod_1399 (n : ℕ) : (2 : ZMod 1399) ^ (2 ^ (58 * n + 26) + 2) = -3 := by
  have h_mod : (2 : ZMod 1399) ^ 233 = 1 := by decide
  rw [pow_eq_pow_mod (2 ^ (58 * n + 26) + 2) h_mod]
  have h_exp : (2 ^ (58 * n + 26) + 2) % 233 = 206 := by
    rw [Nat.add_mod]
    rw [pow_two_mod_233_nat n]
  rw [h_exp]
  decide

lemma dvd_1399 (n : ℕ) : 1399 ∣ 2 ^ (2 ^ (58 * n + 26) + 2) + 3 := by
  rw [← ZMod.natCast_eq_zero_iff]
  have h_eq : ( (2 ^ (2 ^ (58 * n + 26) + 2) + 3 : ℕ) : ZMod 1399 ) = (2 : ZMod 1399) ^ (2 ^ (58 * n + 26) + 2) + 3 := by
    push_cast
    rfl
  rw [h_eq]
  rw [pow_two_mod_1399 n]
  ring

lemma covered_C1_iff (k : ℕ) : covered_by_C1 k ↔ k % 10 = 2 := by
  constructor
  · rintro ⟨m, rfl⟩
    omega
  · intro h
    use (k - 2) / 10
    omega

lemma covered_C2_iff (k : ℕ) : covered_by_C2 k ↔ k % 36 = 16 ∧ ((k - 16) / 36) % 5 ≠ 1 := by
  constructor
  · rintro ⟨m, rfl, hm⟩
    have : (36 * m + 16 - 16) / 36 = m := by omega
    rw [this]
    exact ⟨by omega, hm⟩
  · rintro ⟨h1, h2⟩
    use (k - 16) / 36
    constructor
    · omega
    · exact h2

lemma covered_C3_iff (k : ℕ) : covered_by_C3 k ↔ k % 84 = 22 ∧ ((k - 22) / 84) % 5 ≠ 0 := by
  constructor
  · rintro ⟨m, rfl, hm⟩
    have : (84 * m + 22 - 22) / 84 = m := by omega
    rw [this]
    exact ⟨by omega, hm⟩
  · rintro ⟨h1, h2⟩
    use (k - 22) / 84
    constructor
    · omega
    · exact h2

lemma helper1 (n : ℕ) : (58 * n + 26) % 10 = 2 ↔ n % 5 = 2 := by omega
lemma helper2 (n : ℕ) : (58 * n + 26) % 36 = 16 ↔ n % 18 = 11 := by omega
lemma helper3 (n : ℕ) : (58 * n + 26) % 84 = 22 ↔ n % 42 = 26 := by omega

lemma helper2_full (n : ℕ) : covered_by_C2 (58 * n + 26) ↔ n % 18 = 11 ∧ ((n - 11) / 18) % 5 ≠ 2 := by
  rw [covered_C2_iff]
  omega

lemma helper3_full (n : ℕ) : covered_by_C3 (58 * n + 26) ↔ n % 42 = 26 ∧ ((n - 26) / 42) % 5 ≠ 3 := by
  rw [covered_C3_iff]
  omega

lemma not_covered_iff (n : ℕ) :
    (¬ covered_by_C1 (58 * n + 26) ∧
     ¬ covered_by_C2 (58 * n + 26) ∧
     ¬ covered_by_C3 (58 * n + 26)) ↔
    (n % 5 ≠ 2 ∧ n % 18 ≠ 11 ∧ n % 42 ≠ 26) := by
  rw [covered_C1_iff, helper2_full, helper3_full]
  rw [helper1]
  omega

lemma forall_of_list_all {L : ℕ} {P : ℕ → Prop} [DecidablePred P]
    (h : (List.range L).all (fun r => decide (P r)) = true) : ∀ r < L, P r := by
  rw [List.all_eq_true] at h
  intro r hr
  have h_mem : r ∈ List.range L := List.mem_range.2 hr
  have h_dec := h r h_mem
  exact of_decide_eq_true h_dec

abbrev check_base (L ord_2 r : ℕ) : Prop :=
  (2 ^ (58 * L) * 2 ^ (58 * r + 26)) % ord_2 = 2 ^ (58 * r + 26) % ord_2

abbrev check_no_match (q ord_2 r : ℕ) : Prop :=
  (2 : ZMod q) ^ ((2 ^ (58 * r + 26) + 2) % ord_2) + 3 ≠ 0
""")

lean_code.append("""lemma not_dvd_of_check (q ord_2 L : ℕ) [NeZero q] (hL : 0 < L)
    (h_mod : (2 : ZMod q) ^ ord_2 = 1)
    (h_base_bool : (List.range L).all (fun r => decide (check_base L ord_2 r)) = true)
    (h_no_match_bool : (List.range L).all (fun r => decide (check_no_match q ord_2 r)) = true)
    (n : ℕ) : ¬ q ∣ 2 ^ (2 ^ (58 * n + 26) + 2) + 3 := by
  rw [← ZMod.natCast_eq_zero_iff]
  have h_eq : ( (2 ^ (2 ^ (58 * n + 26) + 2) + 3 : ℕ) : ZMod q ) = (2 : ZMod q) ^ (2 ^ (58 * n + 26) + 2) + 3 := by
    push_cast
    rfl
  rw [h_eq]
  rw [pow_eq_pow_mod (2 ^ (58 * n + 26) + 2) h_mod]
  have h_base := forall_of_list_all h_base_bool
  have h_base_inst := h_base (n % L) (Nat.mod_lt _ hL)
  have h_pow := pow_mod_of_mod_eq n L (n % L) (58 * L) (58 * (n % L) + 26) ord_2 rfl rfl rfl h_base_inst
  have h_add : (2 ^ (58 * n + 26) + 2) % ord_2 = (2 ^ (58 * (n % L) + 26) + 2) % ord_2 := by
    rw [Nat.add_mod, h_pow, ← Nat.add_mod]
  rw [h_add]
  have h_no_match := forall_of_list_all h_no_match_bool
  exact h_no_match (n % L) (Nat.mod_lt _ hL)
""")

# Generate not_dvd_2
lean_code.append("""lemma not_dvd_2 (n : ℕ) : ¬ 2 ∣ 2 ^ (2 ^ (58 * n + 26) + 2) + 3 := by
  rw [← ZMod.natCast_eq_zero_iff]
  have h_eq : ( (2 ^ (2 ^ (58 * n + 26) + 2) + 3 : ℕ) : ZMod 2 ) = (2 : ZMod 2) ^ (2 ^ (58 * n + 26) + 2) + 3 := by
    push_cast
    rfl
  rw [h_eq]
  have h2 : (2 : ZMod 2) = 0 := rfl
  rw [h2]
  have h_exp : 2 ^ (58 * n + 26) + 2 = (2 ^ (58 * n + 26) + 1) + 1 := by omega
  rw [h_exp, pow_succ]
  rw [mul_zero]
  decide
""")

# For each prime, choose the most optimized proof template
for q in primes:
    if q == 2:
        continue
    # find order of 2 mod q
    ord_2 = None
    for d in sorted(divisors(q - 1)):
        if pow(2, d, q) == 1:
            ord_2 = d
            break
            
    # Find period L
    seen = {}
    for n_val in range(10000):
        val = pow(2, 58 * n_val + 26, ord_2)
        if val in seen:
            L = n_val - seen[val]
            break
        seen[val] = n_val
        
    # Critical primes with case splits
    if q in [67, 271, 523]:
        lean_code.append(f"lemma not_dvd_{q} (n : ℕ) (h_not_c1 : n % 5 ≠ 2) (h_not_c2 : n % 18 ≠ 11) (h_not_c3 : n % 42 ≠ 26) :")
        lean_code.append(f"    ¬ {q} ∣ 2 ^ (2 ^ (58 * n + 26) + 2) + 3 := by")
        lean_code.append("  rw [← ZMod.natCast_eq_zero_iff]")
        lean_code.append(f"  have h_mod : (2 : ZMod {q}) ^ {ord_2} = 1 := by decide")
        lean_code.append(f"  have h_eq : ( (2 ^ (2 ^ (58 * n + 26) + 2) + 3 : ℕ) : ZMod {q} ) = (2 : ZMod {q}) ^ (2 ^ (58 * n + 26) + 2) + 3 := by")
        lean_code.append("    push_cast")
        lean_code.append("    rfl")
        lean_code.append("  rw [h_eq]")
        lean_code.append("  rw [pow_eq_pow_mod (2 ^ (58 * n + 26) + 2) h_mod]")
        
        hn_cases_str = " ∨ ".join([f"n % {L} = {r}" for r in range(L)])
        lean_code.append(f"  have hn_cases : {hn_cases_str} := by omega")
        rcases_str = " | ".join(["hn_cases" for _ in range(L)])
        lean_code.append(f"  rcases hn_cases with {rcases_str}")
        for r in range(L):
            is_contradiction = False
            if q == 67 and r % 5 == 2:
                is_contradiction = True
                contra_hyp = "h_not_c1"
                mod_val = 5
                target_val = 2
            elif q == 271 and r % 18 == 11:
                is_contradiction = True
                contra_hyp = "h_not_c2"
                mod_val = 18
                target_val = 11
            elif q == 523 and r % 42 == 26:
                is_contradiction = True
                contra_hyp = "h_not_c3"
                mod_val = 42
                target_val = 26
                
            if is_contradiction:
                lean_code.append(f"  · have h_contra : n % {mod_val} = {target_val} := by omega")
                lean_code.append(f"    exact absurd h_contra {contra_hyp}")
            else:
                pow_val = pow(2, 58 * r + 26, ord_2)
                v_r = (pow_val + 2) % ord_2
                lean_code.append(f"  · have h_exp : (2 ^ (58 * n + 26) + 2) % {ord_2} = {v_r} := by")
                lean_code.append(f"      have h_pow : 2 ^ (58 * n + 26) % {ord_2} = (2 ^ {58 * r + 26}) % {ord_2} := by")
                lean_code.append(f"        exact pow_mod_of_mod_eq n {L} {r} {58*L} {58*r+26} {ord_2} rfl rfl hn_cases (by decide)")
                lean_code.append("      rw [Nat.add_mod]")
                lean_code.append("      rw [h_pow]")
                lean_code.append("      decide")
                lean_code.append("    rw [h_exp]")
                lean_code.append("    decide")
        lean_code.append("")
        continue
        
    # Non-critical primes: Use case-split-free proof using the general not_dvd_of_check helper
    lean_code.append(f"lemma not_dvd_{q} (n : ℕ) : ¬ {q} ∣ 2 ^ (2 ^ (58 * n + 26) + 2) + 3 :=")
    lean_code.append(f"  not_dvd_of_check {q} {ord_2} {L} (by decide) (by decide) (by decide) (by decide) n")
    lean_code.append("")

# Generate divide-and-conquer sub-lemmas for no_smaller_prime_factor (10 parts)
num_parts = 10
step = 100 // num_parts
bounds = [i * step for i in range(num_parts)] + [100]

for i in range(num_parts):
    L_bound = bounds[i]
    U_bound = bounds[i+1]
    part_primes = [p for p in primes if L_bound <= p < U_bound]
    if not part_primes:
        continue
    
    lean_code.append(f"lemma no_smaller_prime_factor_part{i+1} (n : ℕ) (h_not_c1 : n % 5 ≠ 2) (h_not_c2 : n % 18 ≠ 11) (h_not_c3 : n % 42 ≠ 26)")
    lean_code.append(f"    (q : ℕ) (hq_lt : q < {U_bound}) (hq_ge : {L_bound} ≤ q) (hprime : q.Prime) : ¬ q ∣ 2 ^ (2 ^ (58 * n + 26) + 2) + 3 := by")
    
    primes_list = " ∨ ".join([f"q_val = {p}" for p in part_primes])
    lean_code.append(f"  have h_primes_bool : (List.range {U_bound}).all (fun q_val => {L_bound} ≤ q_val → q_val.Prime → {primes_list}) = true := by decide")
    lean_code.append("  have h_primes := forall_of_list_all h_primes_bool")
    lean_code.append("  have h_cases := h_primes q hq_lt hq_ge hprime")
    rcases_str = " | ".join(["rfl" for _ in part_primes])
    lean_code.append(f"  rcases h_cases with {rcases_str}")
    for p in part_primes:
        if p == 2:
            lean_code.append("  · exact not_dvd_2 n")
        else:
            if p in [67, 271, 523]:
                lean_code.append(f"  · exact not_dvd_{p} n h_not_c1 h_not_c2 h_not_c3")
            else:
                lean_code.append(f"  · exact not_dvd_{p} n")
    lean_code.append("")

# Combined no_smaller_prime_factor
lean_code.append("lemma no_smaller_prime_factor (n : ℕ) (h_not_c1 : n % 5 ≠ 2) (h_not_c2 : n % 18 ≠ 11) (h_not_c3 : n % 42 ≠ 26) :")
lean_code.append("    ∀ q < 100, q.Prime → ¬ q ∣ 2 ^ (2 ^ (58 * n + 26) + 2) + 3 := by")
lean_code.append("  intro q hq hprime")

# Binary search on bounds
# we have q < 100
for i in range(num_parts):
    L_bound = bounds[i]
    U_bound = bounds[i+1]
    if i == num_parts - 1:
        # last part
        lean_code.append(f"  exact no_smaller_prime_factor_part{i+1} n h_not_c1 h_not_c2 h_not_c3 q hq (by omega) hprime")
    else:
        lean_code.append(f"  by_cases hq{U_bound} : q < {U_bound}")
        lean_code.append(f"  · exact no_smaller_prime_factor_part{i+1} n h_not_c1 h_not_c2 h_not_c3 q hq{U_bound} (by omega) hprime")
        lean_code.append(f"  · push_neg at hq{U_bound}")

# close the scopes of by_cases
for i in range(num_parts - 1):
    pass # we don't open nested begin-end, just flat by_cases structure is fine since we handle branch 2 flatly!

lean_code.append("")

# Generate main conjecture
lean_code.append("""theorem oeis_248802_conjecture_4 (n : ℕ) :
  (¬ covered_by_C1 (58 * n + 26) ∧
   ¬ covered_by_C2 (58 * n + 26) ∧
   ¬ covered_by_C3 (58 * n + 26)) →
  a (58 * n + 26) = 1399 := by
  intro h
  have h_nc := h
  rw [not_covered_iff] at h_nc
  rcases h_nc with ⟨h_nc1, h_nc2, h_nc3⟩
  unfold a
  have hp : Nat.Prime 1399 := by decide
  have hdvd : 1399 ∣ 2 ^ (2 ^ (58 * n + 26) + 2) + 3 := dvd_1399 n
  have h_not_dvd : ∀ q < 100, q.Prime → ¬ q ∣ 2 ^ (2 ^ (58 * n + 26) + 2) + 3 :=
    no_smaller_prime_factor n h_nc1 h_nc2 h_nc3
  
  -- We want to prove Nat.minFac X = 1399
  -- Let X = 2 ^ (2 ^ (58 * n + 26) + 2) + 3
  -- By minFac_eq_of_prime_dvd:
  have h_minfac : (2 ^ (2 ^ (58 * n + 26) + 2) + 3).minFac = 1399 := by
    have hn1 : 2 ^ (2 ^ (58 * n + 26) + 2) + 3 ≠ 1 := by omega
    have h_prop := Nat.minFac_has_prop hn1
    have h_le : (2 ^ (2 ^ (58 * n + 26) + 2) + 3).minFac ≤ 1399 := Nat.minFac_le_of_dvd hp.two_le hdvd
    have h_ge : 1399 ≤ (2 ^ (2 ^ (58 * n + 26) + 2) + 3).minFac := by
      by_contra! h_lt
      have h_prime_mf := Nat.minFac_prime hn1
      have h_not := h_not_dvd (2 ^ (2 ^ (58 * n + 26) + 2) + 3).minFac h_lt h_prime_mf
      exact h_not h_prop.2.1
    exact le_antisymm h_le h_ge
  exact h_minfac
""")

with open("/workspace/leanproject/Submission/Spec.lean", "w") as f:
    f.write("\n".join(lean_code))

print("Successfully generated /workspace/leanproject/Submission/Spec.lean!")
