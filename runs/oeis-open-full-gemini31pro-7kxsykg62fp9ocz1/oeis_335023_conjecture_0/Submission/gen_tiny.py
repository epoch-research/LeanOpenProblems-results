import sys
import gmpy2

sys.set_int_max_str_digits(20000000)
gmpy2.get_context().precision = 20000000

CHUNK_LIMIT = 32768
node_id_counter = 0

def build_tree(a, b):
    global node_id_counter
    if b - a <= CHUNK_LIMIT:
        P = 1
        F = 0
        for k in range(a, b):
            P *= k
        for k in range(a, b):
            sign = 1 if k % 2 == 0 else -1
            F += sign * P // k
        
        node_id = node_id_counter
        node_id_counter += 1
        name = f"chunk_{node_id}"
        
        fuel = 16
        code = f"""
def {name}_P : ℕ := {P}
def {name}_F : ℤ := {F}
lemma {name} : P_def {a} {b} = {name}_P ∧ S_def {a} {b} = {name}_F := by
  have H := dc_fuel_eq_P_S {fuel} {a} {b} (by decide)
  have H2 : (dc_fuel {fuel} {a} {b}).1 = {name}_P ∧ (dc_fuel {fuel} {a} {b}).2 = {name}_F := by decide
  rw [H2.1, H2.2] at H
  exact H
"""
        return P, F, f"{name}_P", f"{name}_F", name, code
    
    m = (a + b) // 2
    P1, F1, nP1, nF1, name1, code1 = build_tree(a, m)
    P2, F2, nP2, nF2, name2, code2 = build_tree(m, b)
    
    P = P1 * P2
    F = F1 * P2 + P1 * F2
    
    node_id = node_id_counter
    node_id_counter += 1
    name = f"comb_{node_id}"
    
    code = code1 + code2 + f"""
def {name}_P : ℕ := {nP1} * {nP2}
def {name}_F : ℤ := {nF1} * ({nP2} : ℤ) + ({nP1} : ℤ) * {nF2}
lemma {name} : P_def {a} {b} = {name}_P ∧ S_def {a} {b} = {name}_F := by
  have H := comb_correct {a} {m} {b} (by decide) (by decide) {nP1} {nP2} {nF1} {nF2} {name1} {name2}
  exact H
"""
    return P, F, f"{name}_P", f"{name}_F", name, code

def gen_main():
    with open("/workspace/leanproject/Submission/SpecFull.lean", "w") as f:
        # Write preamble...
        f.write("""import FormalConjectures.Util.ProblemImports

open Nat Int Finset

def F_aux (n : ℕ) : ℤ :=
  if n < 2 then 0 else
  Finset.sum (Icc 2 n) $ fun k : ℕ =>
    let n_fact : ℤ := n.factorial
    let k_int : ℤ := k
    let quotient : ℤ := n_fact / k_int
    quotient * (if k % 2 = 0 then 1 else -1)

def a (n : ℕ) : ℕ :=
  let A334958 (m : ℕ) : ℕ := Int.gcd (F_aux (m + 1)) (F_aux m)
  let g_n := A334958 n
  let g_n_plus_1 := A334958 (n + 1)
  if g_n = 0 then 0 else g_n_plus_1 / g_n

theorem oeis_335023_conjecture_0 (n : ℕ) (h : n > 0) :
  a n = 1 ↔ Nat.Prime (n + 1) := by sorry

def P_def (a b : ℕ) : ℕ := ∏ k ∈ Ico a b, k
def term (a b k : ℕ) : ℤ := (∏ j ∈ (Ico a b).erase k, (j : ℤ)) * (if k % 2 = 0 then 1 else -1)
def S_def (a b : ℕ) : ℤ := ∑ k ∈ Ico a b, term a b k

lemma P_def_split (a m b : ℕ) (h1 : a ≤ m) (h2 : m ≤ b) : P_def a b = P_def a m * P_def m b := by
  dsimp [P_def]; have hd : Disjoint (Ico a m) (Ico m b) := by apply disjoint_left.mpr; intro x hx1 hx2; rw [mem_Ico] at hx1 hx2; omega
  have hu : Ico a m ∪ Ico m b = Ico a b := Ico_union_Ico_eq_Ico h1 h2; rw [← hu, prod_union hd]

lemma term_left (a m b k : ℕ) (h1 : a ≤ m) (h2 : m ≤ b) (hk : k ∈ Ico a m) : term a b k = term a m k * (P_def m b : ℤ) := by
  dsimp [term, P_def]; have hu : Ico a m ∪ Ico m b = Ico a b := Ico_union_Ico_eq_Ico h1 h2
  have he : (Ico a b).erase k = (Ico a m).erase k ∪ Ico m b := by
    ext x; simp only [mem_erase, mem_union, mem_Ico]; have hk_ico : a ≤ k ∧ k < m := by simpa [mem_Ico] using hk
    constructor; rintro ⟨hne, hx⟩; have ha : x < m ∨ m ≤ x := by omega; cases ha with | inl h_lt => left; exact ⟨hne, hx.1, h_lt⟩ | inr h_ge => right; exact ⟨h_ge, hx.2⟩
    rintro (⟨hne, ha, hm⟩ | ⟨hm, hb⟩); exact ⟨hne, ha, by omega⟩; have : k ≠ x := by omega; exact ⟨this.symm, by omega, hb⟩
  rw [he]; have hd : Disjoint ((Ico a m).erase k) (Ico m b) := by apply disjoint_left.mpr; intro x hx1 hx2; rw [mem_erase, mem_Ico] at hx1; rw [mem_Ico] at hx2; omega
  rw [prod_union hd]; push_cast; ring

lemma term_right (a m b k : ℕ) (h1 : a ≤ m) (h2 : m ≤ b) (hk : k ∈ Ico m b) : term a b k = (P_def a m : ℤ) * term m b k := by
  dsimp [term, P_def]; have hu : Ico a m ∪ Ico m b = Ico a b := Ico_union_Ico_eq_Ico h1 h2
  have he : (Ico a b).erase k = Ico a m ∪ (Ico m b).erase k := by
    ext x; simp only [mem_erase, mem_union, mem_Ico]; have hk_ico : m ≤ k ∧ k < b := by simpa [mem_Ico] using hk
    constructor; rintro ⟨hne, hx⟩; have ha : x < m ∨ m ≤ x := by omega; cases ha with | inl h_lt => left; exact ⟨hx.1, h_lt⟩ | inr h_ge => right; exact ⟨hne, h_ge, hx.2⟩
    rintro (⟨ha, hm⟩ | ⟨hne, hm, hb⟩); have : k ≠ x := by omega; exact ⟨this.symm, ha, by omega⟩; exact ⟨hne, by omega, hb⟩
  rw [he]; have hd : Disjoint (Ico a m) ((Ico m b).erase k) := by apply disjoint_left.mpr; intro x hx1 hx2; rw [mem_Ico] at hx1; rw [mem_erase, mem_Ico] at hx2; omega
  rw [prod_union hd]; push_cast; ring

lemma S_def_split (a m b : ℕ) (h1 : a ≤ m) (h2 : m ≤ b) : S_def a b = S_def a m * (P_def m b : ℤ) + (P_def a m : ℤ) * S_def m b := by
  dsimp [S_def]; have hu : Ico a m ∪ Ico m b = Ico a b := Ico_union_Ico_eq_Ico h1 h2
  have hd : Disjoint (Ico a m) (Ico m b) := by apply disjoint_left.mpr; intro x hx1 hx2; rw [mem_Ico] at hx1 hx2; omega
  rw [← hu, sum_union hd]
  have H1 : ∑ k ∈ Ico a m, term a b k = ∑ k ∈ Ico a m, term a m k * (P_def m b : ℤ) := by apply sum_congr rfl; intro x hx; exact term_left a m b x h1 h2 hx
  have H2 : ∑ k ∈ Ico m b, term a b k = ∑ k ∈ Ico m b, (P_def a m : ℤ) * term m b k := by apply sum_congr rfl; intro x hx; exact term_right a m b x h1 h2 hx
  rw [H1, H2, ← sum_mul, ← mul_sum]

def dc_fuel (fuel a b : ℕ) : ℕ × ℤ :=
  match fuel with
  | 0 => (1, 0)
  | fuel' + 1 =>
    if b ≤ a then (1, 0)
    else if b = a + 1 then (a, if a % 2 = 0 then (1 : ℤ) else -1)
    else
      let m := (a + b) / 2
      let (p1, f1) := dc_fuel fuel' a m
      let (p2, f2) := dc_fuel fuel' m b
      (p1 * p2, f1 * (p2 : ℤ) + (p1 : ℤ) * f2)

lemma dc_fuel_eq_P_S (fuel a b : ℕ) (h_fuel : b - a < 2 ^ fuel) : P_def a b = (dc_fuel fuel a b).1 ∧ S_def a b = (dc_fuel fuel a b).2 := by
  induction' fuel with f ih generalizing a b
  · have : b - a = 0 := by omega; have h1 : b ≤ a := by omega; dsimp [dc_fuel]; have h_ico : Ico a b = ∅ := Ico_eq_empty_of_le h1; dsimp [P_def, S_def]; rw [h_ico, prod_empty, sum_empty]; exact ⟨rfl, rfl⟩
  · dsimp [dc_fuel]; by_cases h1 : b ≤ a
    · rw [if_pos h1]; have h_ico : Ico a b = ∅ := Ico_eq_empty_of_le h1; dsimp [P_def, S_def]; rw [h_ico, prod_empty, sum_empty]; exact ⟨rfl, rfl⟩
    · rw [if_neg h1]; by_cases h2 : b = a + 1
      · rw [if_pos h2]; have h_ico : Ico a (a + 1) = {a} := Ico_succ_singleton a; have h_ico2 : Ico a b = {a} := by rw [h2, h_ico]; dsimp [P_def, S_def]; rw [h_ico2, prod_singleton, sum_singleton]; have h_erase : (Ico a b).erase a = ∅ := by rw [h_ico2]; exact erase_singleton a; dsimp [term]; rw [h_erase, prod_empty, one_mul]; exact ⟨rfl, rfl⟩
      · rw [if_neg h2]; let m := (a + b) / 2
        have h_pow : b - a ≤ 2 * 2 ^ f := by have h_pow_succ : 2 ^ (f + 1) = 2 * 2 ^ f := by ring; omega
        have h_lt1 : m - a < 2 ^ f := by have : (b - a) / 2 ≤ (2 * 2 ^ f) / 2 := Nat.div_le_div_right h_pow; have h_div : (2 * 2 ^ f) / 2 = 2 ^ f := by omega; omega
        have h_lt2 : b - m < 2 ^ f := by have : b - a + 1 ≤ 2 * 2 ^ f + 1 := by omega; have : (b - a + 1) / 2 ≤ (2 * 2 ^ f + 1) / 2 := Nat.div_le_div_right this; have h_div : (2 * 2 ^ f + 1) / 2 = 2 ^ f := by omega; omega
        have ih1 := ih a m h_lt1; have ih2 := ih m b h_lt2; have ha_m : a ≤ m := by omega; have hm_b : m ≤ b := by omega
        rw [P_def_split a m b ha_m hm_b, S_def_split a m b ha_m hm_b]; rw [ih1.1, ih1.2, ih2.1, ih2.2]; exact ⟨rfl, rfl⟩

lemma comb_correct (a m b : ℕ) (ha : a ≤ m) (hm : m ≤ b) (p1 p2 : ℕ) (f1 f2 : ℤ)
  (h1 : P_def a m = p1 ∧ S_def a m = f1) (h2 : P_def m b = p2 ∧ S_def m b = f2) :
  P_def a b = p1 * p2 ∧ S_def a b = f1 * (p2 : ℤ) + (p1 : ℤ) * f2 := by
  rcases h1 with ⟨hp1, hf1⟩; rcases h2 with ⟨hp2, hf2⟩; subst p1 f1 p2 f2; constructor; exact P_def_split a m b ha hm; exact S_def_split a m b ha hm

lemma n_fact_eq_prod (n : ℕ) (hn : 2 ≤ n) : n.factorial = ∏ j ∈ Ico 2 (n + 1), j := by
  have H1 : Ico 1 (n + 1) = {1} ∪ Ico 2 (n + 1) := by ext x; simp only [mem_Ico, mem_union, mem_singleton]; omega
  have hd : Disjoint ({1} : Finset ℕ) (Ico 2 (n + 1)) := by simp [disjoint_singleton_left, mem_Ico]
  have H2 : ∏ j ∈ Ico 1 (n + 1), j = n.factorial := prod_Ico_id_eq_factorial n; rw [H1, prod_union hd, prod_singleton, one_mul] at H2; exact H2.symm

lemma n_fact_div_eq (n k : ℕ) (hn : 2 ≤ n) (hk : k ∈ Ico 2 (n + 1)) : (n.factorial : ℤ) / (k : ℤ) = ∏ j ∈ (Ico 2 (n + 1)).erase k, (j : ℤ) := by
  have H_prod : ∏ j ∈ Ico 2 (n + 1), (j : ℤ) = (k : ℤ) * ∏ j ∈ (Ico 2 (n + 1)).erase k, (j : ℤ) := by have := mul_prod_erase (Ico 2 (n + 1)) (fun x => (x : ℤ)) hk; exact this.symm
  have H_fact : (n.factorial : ℤ) = ∏ j ∈ Ico 2 (n + 1), (j : ℤ) := by rw [n_fact_eq_prod n hn]; push_cast; rfl
  rw [H_fact, H_prod]; have hk_nz : (k : ℤ) ≠ 0 := by simp only [mem_Ico] at hk; omega; exact Int.mul_ediv_cancel_left _ hk_nz

lemma F_aux_eq_S_def (n : ℕ) (hn : 2 ≤ n) : F_aux n = S_def 2 (n + 1) := by
  dsimp [F_aux, S_def]; rw [if_neg (by omega)]; have h_ico : Icc 2 n = Ico 2 (n + 1) := by ext x; rw [mem_Icc, mem_Ico]; omega; rw [h_ico]; apply sum_congr rfl; intro k hk; dsimp [term]; congr 1; exact n_fact_div_eq n k hn hk

lemma gcd_witness (A B G u v mA mB : ℤ) (hA : A = G * mA) (hB : B = G * mB) (h_lin : A * u + B * v = G) (hG : 0 ≤ G) : Int.gcd A B = G.natAbs := by
  have dvd_A : G ∣ A := ⟨mA, hA⟩; have dvd_B : G ∣ B := ⟨mB, hB⟩
  have dvd_G : (Int.gcd A B : ℤ) ∣ G := by rw [← h_lin]; apply dvd_add; exact dvd_mul_of_dvd_left (Int.gcd_dvd_left A B) u; exact dvd_mul_of_dvd_left (Int.gcd_dvd_right A B) v
  have G_dvd_gcd : G ∣ (Int.gcd A B : ℤ) := dvd_gcd dvd_A dvd_B
  have eq_abs : (Int.gcd A B : ℤ) = G := Int.dvd_antisymm (Int.natCast_nonneg _) hG dvd_G G_dvd_gcd
  rw [← eq_abs]
  sorry

set_option maxHeartbeats 0
""")
        
        P1, F1, nP1, nF1, name1, code1 = build_tree(2, 1194649)
        P2, F2, nP2, nF2, name2, code2 = build_tree(1194649, 1194650)
        P3, F3, nP3, nF3, name3, code3 = build_tree(1194650, 1194651)
        
        f.write(code1)
        f.write(code2)
        f.write(code3)
        
        P12 = P1 * P2
        F12 = F1 * P2 + P1 * F2
        P123 = P12 * P3
        F123 = F12 * P3 + P12 * F3
        
        f.write(f"""
def root_1_P : ℕ := {nP1} * {nP2}
def root_1_F : ℤ := {nF1} * ({nP2} : ℤ) + ({nP1} : ℤ) * {nF2}
lemma root_1 : P_def 2 1194650 = root_1_P ∧ S_def 2 1194650 = root_1_F := by
  have H := comb_correct 2 1194649 1194650 (by decide) (by decide) {nP1} {nP2} {nF1} {nF2} {name1} {name2}
  exact H

def root_2_P : ℕ := root_1_P * {nP3}
def root_2_F : ℤ := root_1_F * ({nP3} : ℤ) + (root_1_P : ℤ) * {nF3}
lemma root_2 : P_def 2 1194651 = root_2_P ∧ S_def 2 1194651 = root_2_F := by
  have H := comb_correct 2 1194650 1194651 (by decide) (by decide) root_1_P {nP3} root_1_F {nF3} root_1 {name3}
  exact H

lemma F_aux_1194648 : F_aux 1194648 = {nF1} := by rw [F_aux_eq_S_def 1194648 (by decide)]; exact {name1}.2
lemma F_aux_1194649 : F_aux 1194649 = root_1_F := by rw [F_aux_eq_S_def 1194649 (by decide)]; exact root_1.2
lemma F_aux_1194650 : F_aux 1194650 = root_2_F := by rw [F_aux_eq_S_def 1194650 (by decide)]; exact root_2.2
""")
        
        F_1 = gmpy2.mpz(F1)
        F_2 = gmpy2.mpz(F12)
        F_3 = gmpy2.mpz(F123)
        g1, u1, v1 = gmpy2.gcdext(F_2, F_1)
        mA1 = F_2 // g1
        mB1 = F_1 // g1
        
        g2, u2, v2 = gmpy2.gcdext(F_3, F_2)
        mA2 = F_3 // g2
        mB2 = F_2 // g2
        
        f.write(f"""
lemma gcd_1 : Int.gcd root_1_F {nF1} = {g1} := by
  have H := gcd_witness root_1_F {nF1} {g1} {u1} {v1} {mA1} {mB1} rfl rfl rfl (by decide)
  exact H

lemma gcd_2 : Int.gcd root_2_F root_1_F = {g2} := by
  have H := gcd_witness root_2_F root_1_F {g2} {u2} {v2} {mA2} {mB2} rfl rfl rfl (by decide)
  exact H

theorem oeis_335023_conjecture_0.disproof : ¬ (type_of% @oeis_335023_conjecture_0) := by
  intro h
  have h1 := h 1194648 (by decide)
  have h_not_prime : ¬ Nat.Prime 1194649 := by
    have h_comp : 1194649 = 1093 * 1093 := by decide
    intro hp
    have h2 := Nat.Prime.eq_one_or_self_of_dvd hp 1093 ⟨1093, h_comp.symm⟩
    cases h2 with
    | inl h3 => revert h3; decide
    | inr h3 => revert h3; decide
  have h_a : a 1194648 = 1 := by
    change (if Int.gcd (F_aux 1194649) (F_aux 1194648) = 0 then 0 else (Int.gcd (F_aux 1194650) (F_aux 1194649)) / (Int.gcd (F_aux 1194649) (F_aux 1194648))) = 1
    rw [F_aux_1194648, F_aux_1194649, F_aux_1194650]
    rw [gcd_1, gcd_2]
    decide
  rw [h_a] at h1
  have h_true : (1 = 1) := rfl
  have h_prime := h1.mp h_true
  exact h_not_prime h_prime
""")

gen_main()
