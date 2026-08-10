import sys
from sympy import isprime

N = 1048576
N2 = N * N

# Generate all 200 values of v and their representations
v_vals = {}
v_reps = {}
for i in range(20):
    for s in range(10):
        fs = (10 * 16**s + 16 * 4**s + 10) // 9
        v = fs * 4**i
        idx = i * 10 + s
        v_vals[idx] = v
        v_to_rep_v = (s, i)

# 1 is at index 199
V_all_raw = sorted(list(set(v_vals.values())))
V_all = [v for v in V_all_raw if v != 1] + [1]

blocking_primes_raw = {1: 3, 4: 3, 16: 7, 26: 4398046511, 64: 3, 104: 5507, 256: 3, 314: 14923, 416: 14906611, 1024: 7, 1256: 59, 1664: 4483, 4096: 3, 4666: 3, 5024: 1184818559, 6656: 11, 16384: 3, 18664: 7, 20096: 1717986887, 26624: 23, 65536: 7, 73274: 59999, 74656: 3, 80384: 31, 106496: 26843543, 262144: 3, 293096: 11, 298624: 3, 321536: 971, 425984: 170327, 1048576: 3, 1166906: 896323, 1172384: 71, 1194496: 7, 1286144: 47, 1703936: 19, 4194304: 7, 4667624: 37951, 4689536: 1384351, 4777984: 3, 5144576: 211, 6815744: 11, 16777216: 3, 18648634: 3, 18670496: 169003, 18758144: 2147447011, 19111936: 3, 20578304: 8388451, 27262976: 67, 67108864: 3, 74594536: 7, 74681984: 1627, 75032576: 3967, 76447744: 7, 82313216: 31, 109051904: 131059, 268435456: 7, 298290746: 109921333703, 298378144: 3, 298727936: 11, 300130304: 11, 305790976: 3, 329252864: 131, 436207616: 6551, 1073741824: 3, 1193162984: 71, 1193512576: 3, 1194911744: 347, 1200521216: 394327, 1223163904: 3, 1317011456: 26183, 1744830464: 8179, 4294967296: 3, 4772302394: 2316487, 4772651936: 1979207, 4774050304: 7, 4779646976: 5345371, 4802084864: 9931, 4892655616: 7, 5268045824: 32611, 6979321856: 11, 17179869184: 7, 19089209576: 19, 19090607744: 8440789219, 19096201216: 3, 19118587904: 339907, 19208339456: 103, 19570622464: 3, 21072183296: 1607, 27917287424: 499, 68719476736: 3, 76355440186: 3, 76356838304: 9203, 76362430976: 31, 76384804864: 3, 76474351616: 1423, 76833357824: 487651, 78282489856: 3, 84288733184: 31, 111669149696: 23, 274877906944: 3, 305421760744: 7, 305427353216: 31, 305449723904: 43, 305539219456: 7, 305897406464: 11, 307333431296: 11, 313129959424: 7, 337154932736: 71, 446676598784: 19}

with open("/workspace/leanproject/Submission/Spec.lean", "w") as out:
    out.write("""/-
Copyright 2026 The Formal Conjectures Authors.
-/
import FormalConjectures.Util.ProblemImports

set_option linter.style.namespace false

open Nat Finset Int
set_option maxRecDepth 10000

def a (n : ℕ) : ℕ :=
  let R := Finset.range (n + 1)
  let domain : Finset ((ℕ × ℕ) × (ℕ × ℕ)) := (R.product R).product (R.product R)

  Finset.card $ domain.filter (λ p : (ℕ × ℕ) × (ℕ × ℕ) =>
    let x := p.fst.fst; let y := p.fst.snd;
    let z := p.snd.fst; let w := p.snd.snd;

    x^2 + y^2 + z^2 + w^2 = n^2 ∧
    z ≤ w ∧
    (∃ k ∈ Finset.range (n + 1), (x^2 : ℤ) - (3 * y : ℤ)^2 = (4^k : ℤ))
  )

lemma not_sq_add_sq (m : ℕ) (p : ℕ) [hp : Fact p.Prime] (hp3 : p % 4 = 3) (h1 : p ∣ m) (h2 : ¬ p^2 ∣ m) :
    ¬ ∃ z w : ℕ, z^2 + w^2 = m := by
  intro ⟨z, w, hzw⟩
  have hm0 : m ≠ 0 := by
    rintro rfl
    apply h2
    exact dvd_zero (p^2)
  have h_padic : padicValNat p m = 1 := by
    have h_le : 1 ≤ padicValNat p m := one_le_padicValNat_of_dvd hm0 h1
    have h_lt : padicValNat p m < 2 := by
      by_contra h_ge
      push_neg at h_ge
      have h_pow_dvd : p^2 ∣ m := (padicValNat_dvd_iff_le hm0).mpr h_ge
      contradiction
    omega
  have h_eq : (∃ x y, m = x ^ 2 + y ^ 2) := ⟨z, w, hzw.symm⟩
  rw [Nat.eq_sq_add_sq_iff] at h_eq
  have hp_mem : p ∈ m.primeFactors := Nat.mem_primeFactors.mpr ⟨hp.out, h1, hm0⟩
  have h_even : Even (padicValNat p m) := h_eq p hp_mem hp3
  rw [h_padic] at h_even
  contradiction

lemma classification_step (x y k : ℕ) (h_eq : (x^2 : ℤ) - (3 * y : ℤ)^2 = (4^k : ℤ)) :
    ∃ u v : ℕ, u + v = 2 * k ∧ u ≤ v ∧ 36 * (x^2 + y^2) = 10 * 2^(2*v) + 16 * 2^(2*k) + 10 * 2^(2*u) := by
  have h_4k : (4^k : ℤ) ≥ 0 := by positivity
  have h_ge_int : (x^2 : ℤ) ≥ (3 * y : ℤ)^2 := by
    omega
  have h_ge_nat : (3 * y)^2 ≤ x^2 := by
    exact_mod_cast h_ge_int
  have h_ge : 3 * y ≤ x := by
    rwa [Nat.pow_le_pow_iff_left (by decide : 2 ≠ 0)] at h_ge_nat
  have h_sub_cast : ((x - 3 * y : ℕ) : ℤ) = (x : ℤ) - (3 * y : ℤ) := Int.ofNat_sub h_ge
  have h_add_cast : ((x + 3 * y : ℕ) : ℤ) = (x : ℤ) + (3 * y : ℤ) := by push_cast; rfl
  have h_ge' : (x^2 : ℕ) ≥ (3 * y)^2 := h_ge_nat
  have h_prod_int : ((x - 3 * y : ℕ) : ℤ) * ((x + 3 * y : ℕ) : ℤ) = (x^2 : ℤ) - (3 * y : ℤ)^2 := by
    rw [h_sub_cast, h_add_cast]
    ring
  have h_4k_eq : 4^k = 2^(2 * k) := by
    rw [show 4 = 2^2 by rfl, ← Nat.pow_mul]
  have h_prod_nat : (x - 3 * y) * (x + 3 * y) = 2^(2 * k) := by
    have h_prod_cast : (((x - 3 * y) * (x + 3 * y) : ℕ) : ℤ) = ((2^(2 * k) : ℕ) : ℤ) := by
      rw [Nat.cast_mul]
      rw [h_prod_int, h_eq]
      rw [show (4^k : ℤ) = ((4^k : ℕ) : ℤ) by rfl]
      rw [show ((4^k : ℕ) : ℤ) = ((2^(2 * k) : ℕ) : ℤ) by rw [h_4k_eq]]
    exact_mod_cast h_prod_cast
  have h_dvd_left : (x - 3 * y) ∣ 2^(2 * k) := ⟨x + 3 * y, h_prod_nat.symm⟩
  have h_dvd_right : (x + 3 * y) ∣ 2^(2 * k) := by
    use (x - 3 * y)
    rw [mul_comm (x + 3 * y)]
    exact h_prod_nat.symm
  obtain ⟨u, hu_le, hu_eq⟩ := (dvd_prime_pow Nat.prime_two).mp h_dvd_left
  obtain ⟨v, hv_le, hv_eq⟩ := (dvd_prime_pow Nat.prime_two).mp h_dvd_right
  have h_pow_sum : 2^(u + v) = 2^(2 * k) := by
    rw [pow_add, ← hu_eq, ← hv_eq, h_prod_nat]
  have h_uv : u + v = 2 * k := Nat.pow_right_injective (by decide) h_pow_sum
  have h_uv_le : u ≤ v := by
    have h_pow_le : 2^u ≤ 2^v := by
      rw [← hu_eq, ← hv_eq]
      omega
    rwa [Nat.pow_le_pow_iff_right (by decide : 1 < 2)] at h_pow_le
  use u, v
  refine ⟨h_uv, h_uv_le, ?_⟩
  have h_id_int : (36 * (x^2 + y^2) : ℤ) = 10 * 2^(2*v) + 16 * 2^(2*k) + 10 * 2^(2*u) := by
    have hA : (2^u : ℤ) = (x : ℤ) - (3 * y : ℤ) := by
      exact_mod_cast hu_eq.symm
    have hB : (2^v : ℤ) = (x : ℤ) + (3 * y : ℤ) := by
      exact_mod_cast hv_eq.symm
    have h_v2 : (2^(2*v) : ℤ) = (2^v : ℤ)^2 := by
      rw [← pow_mul, mul_comm]
    have h_u2 : (2^(2*u) : ℤ) = (2^u : ℤ)^2 := by
      rw [← pow_mul, mul_comm]
    have h_2k : (2^(2*k) : ℤ) = (2^u : ℤ) * (2^v : ℤ) := by
      rw [← pow_add, ← h_uv]
    rw [h_v2, h_u2, h_2k, hA, hB]
    ring
  exact_mod_cast h_id_int

def N : ℕ := 1048576

def idx_to_i (idx : ℕ) : ℕ :=
  idx / 10

def idx_to_s (idx : ℕ) : ℕ :=
  idx % 10

def blocking_prime_by_idx (idx : ℕ) : ℕ :=
  match idx with
""")

    for idx in range(200):
        v = v_vals[idx]
        p = blocking_primes_raw.get(v, 3) # default dummy is 3
        out.write(f"  | {idx} => {p}\n")
    out.write("  | _ => 3\n\n")

    out.write("lemma blocking_prime_by_idx_prime (idx : ℕ) : Nat.Prime (blocking_prime_by_idx idx) := by\n  match idx with\n")
    for idx in range(200):
        out.write(f"  | {idx} => decide\n")
    out.write("  | _ => decide\n\n")

    out.write("lemma blocking_prime_by_idx_3mod4 (idx : ℕ) : blocking_prime_by_idx idx % 4 = 3 := by\n  match idx with\n")
    for idx in range(200):
        out.write(f"  | {idx} => decide\n")
    out.write("  | _ => decide\n\n")

    out_end = """def is_blocked_by_idx (idx : ℕ) : Bool :=
  let i := idx_to_i idx
  let s := idx_to_s idx
  let v := if idx = 199 then 1 else 4^i * (10 * 16^s + 16 * 4^s + 10) / 9
  if v ≥ N^2 then true
  else
    let p := blocking_prime_by_idx idx
    (N^2 - v) % p == 0 && (N^2 - v) % (p^2) != 0

theorem is_blocked_all : ∀ idx < 200, is_blocked_by_idx idx = true := by decide

lemma h_id_int_lemma (p : (ℕ × ℕ) × ℕ × ℕ) (k u v_pow : ℕ) (h_uv : u + v_pow = 2 * k) (h_eq_class : 36 * (p.1.1^2 + p.1.2^2) = 10 * 2^(2*v_pow) + 16 * 2^(2*k) + 10 * 2^(2*u)) (hu_ge : u ≥ 1) (h_u_le_k : u ≤ k) : 9 * (p.1.1^2 + p.1.2^2) = 4^(u - 1) * (10 * 16^(k - u) + 16 * 4^(k - u) + 10) := by
  let i := u - 1
  let s := k - u
  have h_id_int' : (36 * (p.1.1^2 + p.1.2^2) : ℤ) = (4 * (4^i * (10 * 16^s + 16 * 4^s + 10)) : ℤ) := by
    have h_eq_class_cast : (36 * (p.1.1^2 + p.1.2^2) : ℤ) = (10 * 2^(2*v_pow) + 16 * 2^(2*k) + 10 * 2^(2*u) : ℤ) := by exact_mod_cast h_eq_class
    rw [h_eq_class_cast]
    have h_16 : (16^s : ℤ) = 2^(4 * s) := by
      have : (16^s : ℕ) = 2^(4 * s) := by rw [show 16 = 2^4 by rfl, ← pow_mul]
      exact_mod_cast this
    have h_4s : (4^s : ℤ) = 2^(2 * s) := by
      have : (4^s : ℕ) = 2^(2 * s) := by rw [show 4 = 2^2 by rfl, ← pow_mul]
      exact_mod_cast this
    have h_4i : (4^i : ℤ) = 2^(2 * i) := by
      have : (4^i : ℕ) = 2^(2 * i) := by rw [show 4 = 2^2 by rfl, ← pow_mul]
      exact_mod_cast this
    rw [h_16, h_4s, h_4i]
    have h1 : (2^(2 * v_pow) : ℤ) = 2^(2 * i + 2 + 4 * s) := by
      have : 2 * v_pow = 2 * i + 2 + 4 * s := by omega
      rw [this]
    have h2 : (2^(2 * k) : ℤ) = 2^(2 * i + 2 + 2 * s) := by
      have : 2 * k = 2 * i + 2 + 2 * s := by omega
      rw [this]
    have h3 : (2^(2 * u) : ℤ) = 2^(2 * i + 2) := by
      have : 2 * u = 2 * i + 2 := by omega
      rw [this]
    rw [h1, h2, h3]
    repeat rw [pow_add]
    ring
  have h_id_nat : 36 * (p.1.1^2 + p.1.2^2) = 4 * (4^i * (10 * 16^s + 16 * 4^s + 10)) := by
    exact_mod_cast h_id_int'
  omega

theorem A301376_conjecture.disproof : ¬ ∀ (n : ℕ), n > 0 → a n > 0 := by
  intro h
  have h_pos : N > 0 := by decide
  have h_a := h N h_pos
  have h_a' : 0 < a N := h_a
  unfold a at h_a'
  dsimp only at h_a'
  rw [Finset.card_pos, Finset.filter_nonempty_iff] at h_a'
  obtain ⟨p, hp⟩ := h_a'
  rcases hp with ⟨h_dom, h_sum, h_zw, k, hk_mem, hk_eq⟩
  obtain ⟨u, v_pow, h_uv, h_le_v, h_eq_class⟩ := classification_step p.1.1 p.1.2 k hk_eq
  have h_cases : u = 0 ∨ u ≥ 1 := by omega
  rcases h_cases with rfl | hu_ge
  · -- Case u = 0
    have h_k_cases : k = 0 ∨ k ≥ 1 := by omega
    rcases h_k_cases with rfl | hk_ge
    · -- Subcase k = 0
      have h_v0 : v_pow = 0 := by omega
      subst h_v0
      have h_sum_class : 36 * (p.1.1^2 + p.1.2^2) = 36 := by
        rw [h_eq_class]
        rfl
      have h_v_one : p.1.1^2 + p.1.2^2 = 1 := by omega
      have h_two_sq : ∃ z w, z^2 + w^2 = N^2 - 1 := by
        use p.2.1, p.2.2
        omega
      have h_blocked : is_blocked_by_idx 199 = true := is_blocked_all 199 (by decide)
      unfold is_blocked_by_idx at h_blocked
      dsimp only at h_blocked
      have h_p_prop : (N^2 - 1) % (blocking_prime_by_idx 199) = 0 ∧ (N^2 - 1) % (blocking_prime_by_idx 199)^2 ≠ 0 := by
        rw [Bool.and_eq_true] at h_blocked
        exact ⟨beq_iff_eq.mp h_blocked.1, bne_iff_ne.mp h_blocked.2⟩
      let p' := blocking_prime_by_idx 199
      have h_prime_fact : Fact (Nat.Prime p') := ⟨blocking_prime_by_idx_prime 199⟩
      have h_prime_3mod4 : p' % 4 = 3 := blocking_prime_by_idx_3mod4 199
      have h_dvd : p' ∣ N^2 - 1 := Nat.dvd_of_mod_eq_zero h_p_prop.1
      have h_not_dvd : ¬ p'^2 ∣ N^2 - 1 := by
        intro hd
        have h_mod : (N^2 - 1) % p'^2 = 0 := Nat.mod_eq_zero_of_dvd hd
        exact h_p_prop.2 h_mod
      have h_no_rep := not_sq_add_sq (N^2 - 1) p' h_prime_3mod4 h_dvd h_not_dvd
      exact h_no_rep h_two_sq
    · -- Subcase k >= 1
      have h_v_eq : v_pow = 2 * k := by omega
      rw [h_v_eq] at h_eq_class
      have h_rhs_mod : (10 * 2^(2 * (2 * k)) + 16 * 2^(2 * k) + 10 * 2^(2 * 0)) % 4 = 2 := by
        have h_k_ge : 2 * k ≥ 2 := by omega
        have h_pow1 : 4 ∣ 2^(2 * (2 * k)) := by
          have : 2^(2 * (2 * k)) = 4^(2 * k) := by
            rw [show 2^(2 * (2 * k)) = (2^2)^(2 * k) by rw [← pow_mul, mul_comm]]
            rfl
          rw [this]
          use 4^(2 * k - 1)
          have : 2 * k = (2 * k - 1) + 1 := by omega
          nth_rw 1 [this]
          rw [pow_add]
          ring
        have h_pow2 : 4 ∣ 2^(2 * k) := by
          have : 2^(2 * k) = 4^k := by
            rw [show 2^(2 * k) = (2^2)^k by rw [← pow_mul, mul_comm]]
            rfl
          rw [this]
          use 4^(k - 1)
          have : k = (k - 1) + 1 := by omega
          nth_rw 1 [this]
          rw [pow_add]
          ring
        omega
      have h_lhs_mod : (36 * (p.1.1^2 + p.1.2^2)) % 4 = 0 := by omega
      omega
  · -- Case u >= 1
    let i := u - 1
    let s := k - u
    have h_s_bounds : s < 10 := by
      by_contra hc
      push_neg at hc
      have h_pow16 : 16^s ≥ 16^10 := Nat.pow_le_pow_right (by decide) hc
      have h_term_ge : 10 * 16^s + 16 * 4^s + 10 ≥ 10 * 16^10 := by
        calc 10 * 16^s + 16 * 4^s + 10 ≥ 10 * 16^s := by omega
        _ ≥ 10 * 16^10 := Nat.mul_le_mul_left 10 h_pow16
      have h_pow4 : 4^i ≥ 1 := by
        have : 4^i > 0 := by positivity
        omega
      have h_prod_ge : 4^i * (10 * 16^s + 16 * 4^s + 10) ≥ 10 * 16^10 := by
        calc 4^i * (10 * 16^s + 16 * 4^s + 10) ≥ 1 * (10 * 16^10) := Nat.mul_le_mul h_pow4 h_term_ge
        _ = 10 * 16^10 := by ring
      have h_div_ge : 4^i * (10 * 16^s + 16 * 4^s + 10) / 9 ≥ (10 * 16^10) / 9 := Nat.div_le_div_right h_prod_ge
      have h_v_bound : p.1.1^2 + p.1.2^2 ≥ N^2 := by
        have h_u_le_k : u ≤ k := by omega
        have h_eq_class' : 9 * (p.1.1^2 + p.1.2^2) = 4^i * (10 * 16^s + 16 * 4^s + 10) := h_id_int_lemma p k u v_pow h_uv h_eq_class hu_ge h_u_le_k
        have h_div : p.1.1^2 + p.1.2^2 = 4^i * (10 * 16^s + 16 * 4^s + 10) / 9 := by
          rw [← h_eq_class']
          rw [Nat.mul_div_cancel_left]
          decide
        rw [h_div]
        calc 4^i * (10 * 16^s + 16 * 4^s + 10) / 9 ≥ (10 * 16^10) / 9 := h_div_ge
        _ ≥ N^2 := by decide
      omega
    have h_i_bounds : i < 20 := by
      by_contra hc
      push_neg at hc
      have h_pow4 : 4^i ≥ 4^20 := Nat.pow_le_pow_right (by decide) hc
      have h_term_ge : 10 * 16^s + 16 * 4^s + 10 ≥ 10 := by omega
      have h_prod_ge : 4^i * (10 * 16^s + 16 * 4^s + 10) ≥ 10 * 4^20 := by
        calc 4^i * (10 * 16^s + 16 * 4^s + 10) ≥ 4^20 * 10 := Nat.mul_le_mul h_pow4 h_term_ge
        _ = 10 * 4^20 := by ring
      have h_div_ge : 4^i * (10 * 16^s + 16 * 4^s + 10) / 9 ≥ (10 * 4^20) / 9 := Nat.div_le_div_right h_prod_ge
      have h_v_bound : p.1.1^2 + p.1.2^2 ≥ N^2 := by
        have h_u_le_k : u ≤ k := by omega
        have h_eq_class' : 9 * (p.1.1^2 + p.1.2^2) = 4^i * (10 * 16^s + 16 * 4^s + 10) := h_id_int_lemma p k u v_pow h_uv h_eq_class hu_ge h_u_le_k
        have h_div : p.1.1^2 + p.1.2^2 = 4^i * (10 * 16^s + 16 * 4^s + 10) / 9 := by
          rw [← h_eq_class']
          rw [Nat.mul_div_cancel_left]
          decide
        rw [h_div]
        calc 4^i * (10 * 16^s + 16 * 4^s + 10) / 9 ≥ (10 * 4^20) / 9 := h_div_ge
        _ ≥ N^2 := by decide
      omega
    have h_u_le_k : u ≤ k := by omega
    have h_eq_class' : 9 * (p.1.1^2 + p.1.2^2) = 4^i * (10 * 16^s + 16 * 4^s + 10) := h_id_int_lemma p k u v_pow h_uv h_eq_class hu_ge h_u_le_k
    have h_v_div : p.1.1^2 + p.1.2^2 = 4^i * (10 * 16^s + 16 * 4^s + 10) / 9 := by
      rw [← h_eq_class']
      rw [Nat.mul_div_cancel_left]
      decide
    have h_two_sq : ∃ z w, z^2 + w^2 = N^2 - (p.1.1^2 + p.1.2^2) := by
      use p.2.1, p.2.2
      omega
    let idx := i * 10 + s
    have h_idx_lt : idx < 200 := by omega
    have h_div_idx : idx / 10 = i := by omega
    have h_mod_idx : idx % 10 = s := by omega
    have h_blocked : is_blocked_by_idx idx = true := is_blocked_all idx h_idx_lt
    unfold is_blocked_by_idx at h_blocked
    have h_not_199 : idx ≠ 199 := by
      -- since idx = i * 10 + s, if idx = 199, then i = 19 and s = 9.
      -- but then v = 4^19 * (10 * 16^9 + 16 * 4^9 + 10) / 9.
      -- Let's check if v >= N^2:
      -- Since s = 9, fs = (10 * 16^9 + ...) / 9 >= 10 * 16^9 / 9.
      -- v = 4^19 * fs >= 4^19 * 10 * 16^9 / 9 = 2^38 * 10 * 2^36 / 9 = 10 * 2^74 / 9.
      -- But N^2 = 2^40.
      -- Since 10 * 2^74 / 9 > 2^40, v >= N^2 is true!
      -- If v >= N^2, then by definition of is_blocked_by_idx,
      -- we have if v >= N^2 then true, which is true.
      -- But wait!
      -- If v >= N^2, we also have p.1.1^2 + p.1.2^2 >= N^2 (since v = p.1.1^2 + p.1.2^2).
      -- But p.1.1^2 + p.1.2^2 + p.2.1^2 + p.2.2^2 = N^2, so p.1.1^2 + p.1.2^2 <= N^2.
      -- So v <= N^2.
      -- Thus we have v <= N^2 and v >= N^2, which implies v = N^2.
      -- But we proved earlier that v = N^2 is impossible (due to factor of 5).
      -- So we have a contradiction!
      -- So this case is impossible anyway.
      -- But to avoid all of this, we can just prove h_not_199 directly or let split_ifs handle it.
      -- Actually, let's look at how h_blocked is simplified:
      have h_v_lt : 4^i * (10 * 16^s + 16 * 4^s + 10) / 9 < N^2 := by
        rw [← h_v_div]
        have : p.1.1^2 + p.1.2^2 ≤ N^2 := by omega
        -- Since v != N^2 (proven earlier), we must have v < N^2.
        -- Wait, how can we prove v < N^2 easily in Lean?
        -- Actually, we have:
        have h_v_eq_lhs : 4^i * (10 * 16^s + 16 * 4^s + 10) / 9 = p.1.1^2 + p.1.2^2 := h_v_div.symm
        have h_sum_le : p.1.1^2 + p.1.2^2 ≤ N^2 := by omega
        have h_v_ne : 4^i * (10 * 16^s + 16 * 4^s + 10) / 9 ≠ N^2 := by
          intro h_eq_v
          have h_eq_v' : 4^i * (10 * 16^s + 16 * 4^s + 10) = 9 * N^2 := by
            omega
          -- Since 5 ∣ 4^i * (10 * 16^s + 16 * 4^s + 10), we must have 5 ∣ 9 * N^2.
          -- Since N = 2^20, 9 * N^2 has no factor of 5. Contradiction!
          -- Let's prove 5 ∣ ...
          have h_5_dvd : 5 ∣ 4^i * (10 * 16^s + 16 * 4^s + 10) := by
            use 4^i * (2 * 16^s + 3 * 4^s + 2) -- wait, 10 * 16^s + 16 * 4^s + 10 = 5 * (2 * 16^s + 3 * 4^s + 2) + 4^s... no, 16 is not divisible by 5.
            -- 16 * 4^s is not divisible by 5.
            -- Actually, we don't need a complex divisibility proof!
            -- Since N = 1048576, N^2 = 1099511627776.
            -- Since v = 4^i * (10 * 16^s + 16 * 4^s + 10) / 9.
            -- Could we just show that v < N^2?
            -- Wait!
            -- If v ≥ N^2, then:
            -- either s ≥ 10 or i ≥ 20 (which is contradiction to h_s_bounds and h_i_bounds!)
            -- Yes!
            -- If v ≥ N^2, then we must have s ≥ 10 or i ≥ 20!
            -- Let's prove this by contradiction:
            by_cases h_v_ge : 4^i * (10 * 16^s + 16 * 4^s + 10) / 9 ≥ N^2
            · -- If v >= N^2, then:
              -- Since s < 10 and i < 20, we can prove v < N^2 by bounding:
              -- s <= 9 and i <= 19.
              -- Then v <= 4^19 * (10 * 16^9 + 16 * 4^9 + 10) / 9 < N^2.
              -- Let's prove this!
              have h_s_le : s ≤ 9 := by omega
              have h_i_le : i ≤ 19 := by omega
              have h_pow16_le : 16^s ≤ 16^9 := Nat.pow_le_pow_right (by decide) h_s_le
              have h_pow4_le : 4^s ≤ 4^9 := Nat.pow_le_pow_right (by decide) h_s_le
              have h_term_le : 10 * 16^s + 16 * 4^s + 10 ≤ 10 * 16^9 + 16 * 4^9 + 10 := by
                omega
              have h_pow4_i_le : 4^i ≤ 4^19 := Nat.pow_le_pow_right (by decide) h_i_le
              have h_prod_le : 4^i * (10 * 16^s + 16 * 4^s + 10) ≤ 4^19 * (10 * 16^9 + 16 * 4^9 + 10) := Nat.mul_le_mul h_pow4_i_le h_term_le
              have h_div_le : 4^i * (10 * 16^s + 16 * 4^s + 10) / 9 ≤ (4^19 * (10 * 16^9 + 16 * 4^9 + 10)) / 9 := Nat.div_le_div_right h_prod_le
              have h_strict : (4^19 * (10 * 16^9 + 16 * 4^9 + 10)) / 9 < N^2 := by decide
              omega
            · push_neg at h_v_ge
              exact h_v_ge
        exact h_v_lt
      have h_not_199 : idx ≠ 199 := by
        intro h_eq_199
        have h_i_eq : i = 19 := by omega
        have h_s_eq : s = 9 := by omega
        -- but then v >= N^2, contradiction!
        have h_v_ge : 4^i * (10 * 16^s + 16 * 4^s + 10) / 9 ≥ N^2 := by
          rw [h_i_eq, h_s_eq]
          decide
        omega
      rw [h_div_idx, h_mod_idx] at h_blocked
      -- since we have h_v_lt, the "if v >= N^2" branch evaluates to false.
      -- And since idx != 199, the "if idx = 199" branch evaluates to false.
      -- So we can simplify h_blocked to:
      have h_v_lt' : ¬ (if idx = 199 then 1 else 4^i * (10 * 16^s + 16 * 4^s + 10) / 9) ≥ N^2 := by
        split_ifs
        · decide
        · omega
      have h_not_199_prop : (if idx = 199 then 1 else 4^i * (10 * 16^s + 16 * 4^s + 10) / 9) = 4^i * (10 * 16^s + 16 * 4^s + 10) / 9 := by
        split_ifs
        · contradiction
        · rfl
      rw [h_not_199_prop] at h_blocked
      split_ifs at h_blocked
      · contradiction
      · rw [← h_v_div] at h_blocked
        let p' := blocking_prime_by_idx idx
        have h_p_prop : (N^2 - (p.1.1^2 + p.1.2^2)) % p' = 0 ∧ (N^2 - (p.1.1^2 + p.1.2^2)) % p'^2 ≠ 0 := by
          rw [Bool.and_eq_true] at h_blocked
          exact ⟨beq_iff_eq.mp h_blocked.1, bne_iff_ne.mp h_blocked.2⟩
        have h_prime_fact : Fact (Nat.Prime p') := ⟨blocking_prime_by_idx_prime idx⟩
        have h_prime_3mod4 : p' % 4 = 3 := blocking_prime_by_idx_3mod4 idx
        have h_dvd : p' ∣ N^2 - (p.1.1^2 + p.1.2^2) := Nat.dvd_of_mod_eq_zero h_p_prop.1
        have h_not_dvd : ¬ p'^2 ∣ N^2 - (p.1.1^2 + p.1.2^2) := by
          intro hd
          have h_mod : (N^2 - (p.1.1^2 + p.1.2^2)) % p'^2 = 0 := Nat.mod_eq_zero_of_dvd hd
          exact h_p_prop.2 h_mod
        have h_no_rep := not_sq_add_sq (N^2 - (p.1.1^2 + p.1.2^2)) p' h_prime_3mod4 h_dvd h_not_dvd
        exact h_no_rep h_two_sq
"""

    out.write(out_end)
print("SUCCESSFULLY GENERATED SPEC.LEAN!")
