import FormalConjectures.Util.ProblemImports

open Finset ZMod Nat Set Classical

/--
The predicate that $\{2^k - k: k = 1,\dots,m\}$ contains a complete system of residues modulo $n$.
This is equivalent to the image of $k \mapsto 2^k - k \pmod n$ for $k \in \{1, \dots, m\}$ being the entire $\mathbb{Z}_n$.
-/
def A232616_prop (n m : ℕ) [NeZero n] : Prop :=
  (univ : Finset (ZMod n)) = (Finset.Icc 1 m).image fun k ↦ (Nat.cast (2 ^ k - k) : ZMod n)

/--
A232616: Least positive integer $m$ such that $\{2^k - k: k = 1,\dots,m\}$
contains a complete system of residues modulo $n$.
-/
noncomputable def A232616 (n : ℕ) : ℕ :=
  if h : n = 0 then 0
  else
    -- Since n is non-zero, the NeZero n instance is available for ZMod n operations.
    have hn : NeZero n := NeZero.mk h

    -- The set $S$ of all $m$ which satisfy the complete residue system condition.
    -- The set $S$ is non-empty based on the external theorem $a(n) \le n^2$.
    let S : Set ℕ := { m : ℕ | A232616_prop n m }

    -- The least element of a non-empty set of natural numbers is its infimum, sInf.
    sInf S

set_option maxHeartbeats 0
set_option maxRecDepth 2000000
set_option exponentiation.threshold 200000

def fast_mod_pow_go (base exp mod_val : Nat) (d : Nat) : Nat :=
  match d with
  | 0 => 1
  | d' + 1 =>
    if exp = 0 then 1
    else if exp = 1 then base % mod_val
    else
      let half := fast_mod_pow_go base (exp / 2) mod_val d'
      let half_sq := (half * half) % mod_val
      if exp % 2 = 0 then half_sq
      else (half_sq * base) % mod_val

def fast_mod_pow (base exp mod_val : Nat) : Nat :=
  fast_mod_pow_go base exp mod_val 30

def check_q (q : Nat) (r : Nat) : Bool :=
  let k := 4116 * q + r
  (fast_mod_pow 2 k 1604 == (k + 741) % 1604)

def check_q_loop (q : Nat) (limit : Nat) (r : Nat) : Bool :=
  match limit with
  | 0 => true
  | d + 1 =>
    if check_q q r then
      false
    else
      check_q_loop (q + 1) d r

theorem check_1003 : check_q_loop 0 3968 1003 = true := by decide
theorem check_3123 : check_q_loop 0 3968 3123 = true := by decide
theorem check_3371 : check_q_loop 0 3968 3371 = true := by decide

def check_r (r : Nat) : Bool :=
  if r % 4 == 3 then
    (2^r % 343 == (r + 196) % 343)
  else
    false

def find_sols_loop (r : Nat) (limit : Nat) (acc : List Nat) : List Nat :=
  match limit with
  | 0 => acc
  | d + 1 =>
    if check_r r then
      find_sols_loop (r + 1) d (r :: acc)
    else
      find_sols_loop (r + 1) d acc

theorem sols_eq : find_sols_loop 0 4116 [] = [3371, 3123, 1003] := by
  decide

theorem prop_mono {n m M : ℕ} [NeZero n] (h : m ≤ M) (hp : A232616_prop n m) : A232616_prop n M := by
  rw [A232616_prop] at hp ⊢
  have h_sub : Finset.Icc 1 m ⊆ Finset.Icc 1 M := Finset.Icc_subset_Icc le_rfl h
  have h_img : (Finset.Icc 1 m).image (fun k => (Nat.cast (2^k - k) : ZMod n)) ⊆ (Finset.Icc 1 M).image (fun k => (Nat.cast (2^k - k) : ZMod n)) := Finset.image_subset_image h_sub
  rw [← hp] at h_img
  exact Eq.symm (univ_subset_iff.mp h_img)

theorem test_power_period (q : ℕ) (r : ℕ) : (2^(4116 * q + r)) ≡ 2^r [MOD 343] := by
  rw [pow_add, pow_mul]
  have h1 : 2^4116 ≡ 1 [MOD 343] := by decide
  have h2 : (2^4116)^q ≡ 1^q [MOD 343] := Nat.ModEq.pow q h1
  rw [one_pow] at h2
  have h3 : (2^4116)^q * 2^r ≡ 1 * 2^r [MOD 343] := Nat.ModEq.mul h2 (Nat.ModEq.refl _)
  rw [one_mul] at h3
  exact h3

theorem mod_of_mod_eq {a b N d : ℕ} (h : a % N = b % N) (hd : d ∣ N) : a % d = b % d := by
  have h1 : a % N % d = b % N % d := by rw [h]
  rw [Nat.mod_mod_of_dvd a hd, Nat.mod_mod_of_dvd b hd] at h1
  exact h1

def r_table : List ℕ := [36, 143, 2, 349, 308, 3, 26, 225, 332, 191, 50, 81, 4, 31, 58, 85, 48, 139, 98, 193, 220, 15, 122, 237, 328, 287, 146, 5, 204, 311, 170, 29, 60, 171, 10, 37, 64, 27, 118, 77, 172, 199, 226, 101, 216, 307, 266, 125, 72, 183, 290, 149, 8, 39, 150, 173, 16, 43, 6, 97, 56, 151, 178, 205, 80, 195, 286, 245, 104, 51, 162, 269, 128, 475, 18, 129, 152, 11, 22, 49, 76, 35, 130, 157, 184, 59, 174, 265, 224, 83, 30, 141, 248, 107, 454, 413, 108, 131, 330, 437, 28, 55, 14, 109, 136, 163, 38, 153, 244, 203, 62, 9, 120, 227, 86, 433, 392, 87, 110, 309, 416, 7, 34, 61, 88, 115, 142, 17, 132, 223, 182, 41, 304, 99, 206, 65, 412, 371, 66, 89, 288, 395, 254, 13, 40, 67, 94, 121, 148, 111, 202, 161, 20, 283, 78, 185, 44, 391, 350, 45, 68, 267, 374, 233, 12, 19, 46, 73, 100, 127, 90, 181, 140, 235, 262, 57, 164, 23, 370, 329, 24, 47, 246, 353, 212, 71, 102, 25, 52, 79, 106, 69, 160, 119, 214, 241]

lemma r_table_elem : ∀ X : Fin 196, (r_table.getD X.val 2) % 4 = (196 - X.val) % 4 := by
  decide

lemma r_table_bounds : ∀ X : Fin 196, 2 ≤ r_table.getD X.val 2 ∧ r_table.getD X.val 2 < 476 := by
  decide

lemma num_mod_49 : ∀ X : Fin 196,
    let r := r_table.getD X.val 2
    let val_2_r := fast_mod_pow 2 r 137543
    let val_r_X := (r + X.val) % 137543
    let num := (val_2_r + 137543 - val_r_X) % 137543
    num % 49 = 0 := by
  decide

lemma k_le_two_pow (k : ℕ) : k ≤ 2^k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ]
    have h_pos : 1 ≤ 2^k := Nat.one_le_pow k 2 (by decide)
    omega

lemma cast_mod_of_dvd (A N d : ℕ) (hd : d ∣ N) : (Nat.cast (A % N) : ZMod d) = (Nat.cast A : ZMod d) := by
  exact (ZMod.natCast_eq_natCast_iff (A % N) A d).mpr (mod_of_mod_eq (Nat.mod_mod A N) hd)

lemma modeq_mul_modulus (A B n d : ℕ) (h : A ≡ B [MOD n]) : A * d ≡ B * d [MOD (n * d)] := by
  unfold Nat.ModEq at h ⊢
  rw [Nat.mul_mod_mul_right, Nat.mul_mod_mul_right, h]

lemma mod4_proof_zmod (X : ℕ) (q : ℕ) :
    let r := r_table.getD (X % 196) 2
    let k := q * 117600 + r
    (Nat.cast (2^k - k) : ZMod 4) = (Nat.cast X : ZMod 4) := by
  intro r k
  have h_k_le : k ≤ 2^k := k_le_two_pow k
  rw [Nat.cast_sub h_k_le]
  have h_r_bounds := r_table_bounds ⟨X % 196, Nat.mod_lt X (by decide : 0 < 196)⟩
  have h_r_ge2 : 2 ≤ r := h_r_bounds.1
  have h_k_ge : 2 ≤ k := by omega
  have h_pow4 : (Nat.cast (2^k) : ZMod 4) = 0 := by
    obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le h_k_ge
    rw [hd, pow_add]
    have : (Nat.cast (2^2 * 2^d) : ZMod 4) = (4 : ZMod 4) * (Nat.cast (2^d) : ZMod 4) := by push_cast; rfl
    rw [this]
    have h4 : (4 : ZMod 4) = 0 := rfl
    rw [h4, zero_mul]
  have h_elem := r_table_elem ⟨X % 196, Nat.mod_lt X (by decide : 0 < 196)⟩
  have h_k_eq : (Nat.cast k : ZMod 4) = (Nat.cast r : ZMod 4) := by
    have : k = 4 * (29400 * q) + r := by ring
    rw [this]
    push_cast
    have h4 : (4 : ZMod 4) = 0 := rfl
    rw [h4, zero_mul, zero_add]
  have h_r_eq : (Nat.cast r : ZMod 4) = - (Nat.cast X : ZMod 4) := by
    have h_r_mod : r ≡ (196 - X % 196) [MOD 4] := h_elem
    have h_r_cast : (Nat.cast r : ZMod 4) = (Nat.cast (196 - X % 196) : ZMod 4) := by
      exact (ZMod.natCast_eq_natCast_iff r (196 - X % 196) 4).mpr h_r_mod
    rw [h_r_cast]
    have h_sub : X % 196 ≤ 196 := by
      have := Nat.mod_lt X (by decide : 0 < 196)
      omega
    have h_cast_sub : (Nat.cast (196 - X % 196) : ZMod 4) = (Nat.cast 196 : ZMod 4) - (Nat.cast (X % 196) : ZMod 4) := by
      exact Nat.cast_sub h_sub
    have h_196 : (Nat.cast 196 : ZMod 4) = 0 := rfl
    have h_mod_196 : (Nat.cast (X % 196) : ZMod 4) = (Nat.cast X : ZMod 4) := by
      have h_div_eq : X = 196 * (X / 196) + X % 196 := (Nat.div_add_mod X 196).symm
      conv_rhs => rw [h_div_eq]
      push_cast
      have h196 : (196 : ZMod 4) = 0 := rfl
      rw [h196, zero_mul, zero_add]
    rw [h_cast_sub, h_196, h_mod_196, zero_sub]
  rw [h_pow4, h_k_eq, h_r_eq, zero_sub, neg_neg]

lemma mod137543_proof_zmod (X : ℕ) (q : ℕ) :
    let r := r_table.getD (X % 196) 2
    let val_2_r := fast_mod_pow 2 r 137543
    let val_r_X := (r + X) % 137543
    let num := (val_2_r + 137543 - val_r_X) % 137543
    let H := num / 49
    let k := q * 117600 + r
    q ≡ H * 1938 [MOD 2807] →
    (Nat.cast (2^k - k) : ZMod 137543) = (Nat.cast X : ZMod 137543) := by
  intro r val_2_r val_r_X num H k hq
  have h_k_le : k ≤ 2^k := k_le_two_pow k
  rw [Nat.cast_sub h_k_le]
  have h_pow : (Nat.cast (2^k) : ZMod 137543) = (Nat.cast (2^r) : ZMod 137543) := by
    have hk : k = 117600 * q + r := by ring
    rw [hk, pow_add, pow_mul, Nat.cast_mul, Nat.cast_pow, Nat.cast_pow]
    have h1_fast : fast_mod_pow 2 117600 137543 = 1 := by decide
    have h_eq := fast_mod_pow_eq 117600 137543 (by decide) (by omega)
    have h1_pow : 2^117600 % 137543 = 1 := by
      rw [← h_eq]
      exact h1_fast.symm
    have h1 : (Nat.cast 2 : ZMod 137543)^117600 = 1 := by
      have h1_cast : (Nat.cast 2 : ZMod 137543)^117600 = Nat.cast (2^117600) := by rw [Nat.cast_pow]
      rw [h1_cast]
      exact (ZMod.natCast_eq_natCast_iff (2^117600) 1 137543).mpr h1_pow
    rw [h1, one_pow, one_mul]
  rw [h_pow]
  have h_r_bounds := r_table_bounds ⟨X % 196, Nat.mod_lt X (by decide : 0 < 196)⟩
  have h_r_lt : r < 1073741824 := by
    have h_r_eq : r = r_table.getD (X % 196) 2 := rfl
    have h_lt := h_r_bounds.2
    change r_table.getD (X % 196) 2 < 476 at h_lt
    omega
  have h_fast_r : val_2_r = 2^r % 137543 := fast_mod_pow_eq r 137543 (by decide) h_r_lt
  have h_val_2_r_cast : (Nat.cast val_2_r : ZMod 137543) = Nat.cast (2^r) := by
    rw [h_fast_r, cast_mod_of_dvd (2^r) 137543 137543 (dvd_refl _)]

  let X_mod := X % 196
  let X_fin : Fin 196 := ⟨X_mod, Nat.mod_lt X (by decide)⟩
  let val_r_X_mod := (r + X_mod) % 137543
  let num_mod := (val_2_r + 137543 - val_r_X_mod) % 137543

  have h_div : 49 ∣ 137543 := by decide
  have h_sub_le : val_r_X ≤ val_2_r + 137543 := by
    have : val_r_X < 137543 := Nat.mod_lt _ (by decide)
    omega
  have h_sub_le_mod : val_r_X_mod ≤ val_2_r + 137543 := by
    have : val_r_X_mod < 137543 := Nat.mod_lt _ (by decide)
    omega
  
  have h_num_cast_49 : (Nat.cast num : ZMod 49) = (Nat.cast val_2_r : ZMod 49) - (Nat.cast val_r_X : ZMod 49) := by
    have h1 : (Nat.cast num : ZMod 49) = (Nat.cast ((val_2_r + 137543 - val_r_X) % 137543) : ZMod 49) := rfl
    rw [h1, cast_mod_of_dvd _ 137543 49 h_div, Nat.cast_sub h_sub_le]
    push_cast
    have h137543 : (137543 : ZMod 49) = 0 := rfl
    rw [h137543, add_zero]

  have h_num_mod_cast_49 : (Nat.cast num_mod : ZMod 49) = (Nat.cast val_2_r : ZMod 49) - (Nat.cast val_r_X_mod : ZMod 49) := by
    have h1 : (Nat.cast num_mod : ZMod 49) = (Nat.cast ((val_2_r + 137543 - val_r_X_mod) % 137543) : ZMod 49) := rfl
    rw [h1, cast_mod_of_dvd _ 137543 49 h_div, Nat.cast_sub h_sub_le_mod]
    push_cast
    have h137543 : (137543 : ZMod 49) = 0 := rfl
    rw [h137543, add_zero]

  have h_div_196 : 49 ∣ 196 := by decide
  have h_X_mod_49 : X_mod ≡ X [MOD 49] := Nat.mod_mod_of_dvd X h_div_196
  have h_add_mod : r + X_mod ≡ r + X [MOD 49] := Nat.ModEq.add_left r h_X_mod_49

  have h_val_r_X_cast : (Nat.cast val_r_X : ZMod 49) = (Nat.cast (r + X) : ZMod 49) := cast_mod_of_dvd _ 137543 49 h_div
  have h_val_r_X_mod_cast : (Nat.cast val_r_X_mod : ZMod 49) = (Nat.cast (r + X_mod) : ZMod 49) := cast_mod_of_dvd _ 137543 49 h_div

  have h_add_mod_cast : (Nat.cast (r + X_mod) : ZMod 49) = (Nat.cast (r + X) : ZMod 49) := by
    exact (ZMod.natCast_eq_natCast_iff (r + X_mod) (r + X) 49).mpr h_add_mod

  have h_val_eq : (Nat.cast val_r_X_mod : ZMod 49) = (Nat.cast val_r_X : ZMod 49) := by
    rw [h_val_r_X_mod_cast, h_add_mod_cast, ← h_val_r_X_cast]

  have h_num_eq_num_mod : (Nat.cast num : ZMod 49) = (Nat.cast num_mod : ZMod 49) := by
    rw [h_num_cast_49, h_num_mod_cast_49, h_val_eq]

  have h_num_mod_0 : num_mod % 49 = 0 := num_mod_49 X_fin
  have h_num_mod_cast_0 : (Nat.cast num_mod : ZMod 49) = 0 := by
    exact (ZMod.natCast_eq_natCast_iff num_mod 0 49).mpr h_num_mod_0
  have h_num_cast_0 : (Nat.cast num : ZMod 49) = 0 := by
    rw [h_num_eq_num_mod, h_num_mod_cast_0]
  have h_num_mod_49_val : num % 49 = 0 := by
    exact (ZMod.natCast_eq_natCast_iff num 0 49).mp h_num_cast_0

  have h_num_div : num = H * 49 := by
    have h_div_eq : num = 49 * (num / 49) + num % 49 := (Nat.div_add_mod num 49).symm
    rw [h_num_mod_49_val, add_zero, mul_comm] at h_div_eq
    exact h_div_eq

  have h_inv : 1938 * 2400 ≡ 1 [MOD 2807] := by decide
  have h_H_inv : H * (1938 * 2400) ≡ H * 1 [MOD 2807] := Nat.ModEq.mul_left H h_inv
  rw [mul_one] at h_H_inv

  have h_q_mod : q ≡ H * 1938 [MOD 2807] := hq
  have h_q_mul : q * 2400 ≡ (H * 1938) * 2400 [MOD 2807] := Nat.ModEq.mul_right 2400 h_q_mod
  have h_assoc : (H * 1938) * 2400 = H * (1938 * 2400) := by ring
  rw [h_assoc] at h_q_mul
  have h_q_mul2 : q * 2400 ≡ H [MOD 2807] := h_q_mul.trans h_H_inv

  have h_q_mul_49 : (q * 2400) * 49 ≡ H * 49 [MOD (2807 * 49)] := modeq_mul_modulus (q * 2400) H 2807 49 h_q_mul2

  have h_k_eq_num : q * 117600 ≡ num [MOD 137543] := by
    have h_mod_val : 2807 * 49 = 137543 := by decide
    have h_prod_val : (q * 2400) * 49 = q * 117600 := by ring
    rw [h_mod_val] at h_q_mul_49
    rw [h_prod_val] at h_q_mul_49
    rw [← h_num_div] at h_q_mul_49
    exact h_q_mul_49

  have h_k_cast : (Nat.cast (q * 117600) : ZMod 137543) = Nat.cast num := by
    exact (ZMod.natCast_eq_natCast_iff (q * 117600) num 137543).mpr h_k_eq_num

  have h_add_k_X : (Nat.cast k : ZMod 137543) + (Nat.cast X : ZMod 137543) = Nat.cast val_2_r := by
    have h_k_def : k = q * 117600 + r := rfl
    rw [h_k_def]
    have h_cast_add : (Nat.cast (q * 117600 + r) : ZMod 137543) = Nat.cast (q * 117600) + Nat.cast r := by push_cast; rfl
    rw [h_cast_add, h_k_cast]
    have h_val_r_X_cast : (Nat.cast val_r_X : ZMod 137543) = Nat.cast (r + X) := cast_mod_of_dvd (r + X) 137543 137543 (dvd_refl _)
    have h_num_cast_137543 : (Nat.cast num : ZMod 137543) = Nat.cast val_2_r - Nat.cast val_r_X := by
      have h1 : (Nat.cast num : ZMod 137543) = (Nat.cast ((val_2_r + 137543 - val_r_X) % 137543) : ZMod 137543) := rfl
      rw [h1, cast_mod_of_dvd _ 137543 137543 (dvd_refl _), Nat.cast_sub h_sub_le]
      push_cast
      have h137543 : (137543 : ZMod 137543) = 0 := rfl
      rw [h137543, add_zero]
    rw [h_num_cast_137543]
    push_cast at h_val_r_X_cast ⊢
    rw [h_val_r_X_cast]
    ring

  rw [h_val_2_r_cast] at h_add_k_X
  have h_final : (Nat.cast (2^r) : ZMod 137543) - Nat.cast k = Nat.cast X := by
    rw [← h_add_k_X]
    ring
  exact h_final

lemma combine_modular_proof (X : ℕ) (q : ℕ) (hq : q ≡ (let r := r_table.getD (X % 196) 2
               let val_2_r := fast_mod_pow 2 r 137543
               let val_r_X := (r + X) % 137543
               let num := (val_2_r + 137543 - val_r_X) % 137543
               let H := num / 49
               H * 1938) [MOD 2807]) :
    let r := r_table.getD (X % 196) 2
    let k := q * 117600 + r
    1 ≤ k ∧ (Nat.cast (2^k - k) : ZMod 550172) = (Nat.cast X : ZMod 550172) := by
  intro r k
  have h_r_bounds := r_table_bounds ⟨X % 196, Nat.mod_lt X (by decide)⟩
  have h_k1 : 1 ≤ k := by
    have hk_def : k = q * 117600 + r := rfl
    have hr_ge2 : 2 ≤ r := h_r_bounds.1
    omega
  refine ⟨h_k1, ?_⟩
  have h4_cast := mod4_proof_zmod X q
  have h137543_cast := mod137543_proof_zmod X q hq
  have h4 : 2^k - k ≡ X [MOD 4] := by
    exact (ZMod.natCast_eq_natCast_iff (2^k - k) X 4).mp h4_cast
  have h137543 : 2^k - k ≡ X [MOD 137543] := by
    exact (ZMod.natCast_eq_natCast_iff (2^k - k) X 137543).mp h137543_cast
  have h_coprime : Nat.Coprime 4 137543 := by decide
  have h_550172 : 2^k - k ≡ X [MOD 4 * 137543] := by
    exact (Nat.modEq_and_modEq_iff_modEq_mul h_coprime).mp ⟨h4, h137543⟩
  have h_prod : 4 * 137543 = 550172 := rfl
  rw [h_prod] at h_550172
  exact (ZMod.natCast_eq_natCast_iff (2^k - k) X 550172).mpr h_550172

lemma mem_of_mem_find_sols_loop {r start limit acc} (h : r ∈ acc) : r ∈ find_sols_loop start limit acc := by
  induction limit generalizing start acc with
  | zero => exact h
  | succ d ih =>
    unfold find_sols_loop
    split_ifs with hc
    · exact ih (List.mem_cons_of_mem _ h)
    · exact ih h

lemma mem_find_sols_loop {r start limit acc} (hs : start ≤ r) (hl : r < start + limit) (hc : check_r r = true) :
    r ∈ find_sols_loop start limit acc := by
  induction limit generalizing start acc with
  | zero => omega
  | succ d ih =>
    unfold find_sols_loop
    have h_add : start + (d + 1) = start + 1 + d := by ring
    rw [h_add] at hl
    split_ifs with hc'
    · have h_cases : start = r ∨ start + 1 ≤ r := by omega
      rcases h_cases with rfl | h_ge
      · apply mem_of_mem_find_sols_loop
        exact List.mem_cons_self
      · apply ih
        · exact h_ge
        · exact hl
    · have h_ge : start + 1 ≤ r := by
        have h_ne : start ≠ r := by
          rintro rfl
          exact hc' hc
        omega
      apply ih
      · exact h_ge
      · exact hl

lemma check_q_loop_suffix (q limit r) (h : check_q_loop q limit r = true) (d : Nat) (hd : d ≤ limit) :
    check_q_loop (q + d) (limit - d) r = true := by
  induction d generalizing q limit with
  | zero =>
    have h_eq1 : q + 0 = q := by omega
    have h_eq2 : limit - 0 = limit := by omega
    rw [h_eq1, h_eq2]
    exact h
  | succ s ih =>
    have h_limit : limit = (limit - 1) + 1 := by omega
    have h_unfold : check_q_loop q limit r = if check_q q r then false else check_q_loop (q + 1) (limit - 1) r := by
      nth_rw 1 [h_limit]
      rfl
    rw [h_unfold] at h
    split_ifs at h
    have h_le : s ≤ limit - 1 := by omega
    have ih_inst := ih (q + 1) (limit - 1) h h_le
    have h_comm1 : q + (s + 1) = q + 1 + s := by omega
    have h_comm2 : limit - (s + 1) = limit - 1 - s := by omega
    rw [h_comm1, h_comm2]
    exact ih_inst

lemma exists_M_of_surjective {n : ℕ} [NeZero n]
    (h : ∀ x : ZMod n, ∃ k, 1 ≤ k ∧ (Nat.cast (2^k - k) : ZMod n) = x) :
    ∃ M, A232616_prop n M := by
  have H : ∀ (s : Finset (ZMod n)), ∃ M, s ⊆ (Finset.Icc 1 M).image (fun k ↦ (Nat.cast (2^k - k) : ZMod n)) := by
    intro s
    refine Finset.induction_on s ?_ ?_
    · use 1
      simp
    · intro x s' hxs' ih
      rcases ih with ⟨M', hM'⟩
      rcases h x with ⟨k, hk1, hk_eq⟩
      use max M' k
      intro y hy
      rw [Finset.mem_insert] at hy
      rcases hy with rfl | hys'
      · rw [Finset.mem_image]
        refine ⟨k, ?_, hk_eq⟩
        rw [Finset.mem_Icc]
        exact ⟨hk1, le_max_right _ _⟩
      · have hy_img := hM' hys'
        rw [Finset.mem_image] at hy_img ⊢
        rcases hy_img with ⟨k', hk', hk'_eq⟩
        refine ⟨k', ?_, hk'_eq⟩
        rw [Finset.mem_Icc] at hk' ⊢
        exact ⟨hk'.1, hk'.2.trans (le_max_left _ _)⟩
  rcases H univ with ⟨M, hM⟩
  use M
  rw [A232616_prop]
  exact Eq.symm (Finset.univ_subset_iff.mp hM)

/--
Conjecture (i): $a(n) < 2 \cdot (\text{prime}(n) - 1)$ for all $n > 0$,
where $\text{prime}(n)$ is the $n$-th prime number (1-indexed).
-/
theorem oeis_232616_conjecture_i.disproof :
    ¬ (∀ (n : ℕ) (hn : 0 < n), A232616 n < 2 * (Nat.nth Nat.Prime (n - 1) - 1)) := by
  intro h
  have h1 := h 550172 (by omega)
  have h_550171 : 550172 - 1 = 550171 := by decide
  rw [h_550171] at h1
  have h_550172_nz : 550172 ≠ 0 := by decide
  have h_inf : A232616 550172 = sInf { m : ℕ | A232616_prop 550172 m } := by
    unfold A232616
    rw [dif_neg h_550172_nz]
  have h_S_nonempty : { m : ℕ | A232616_prop 550172 m }.Nonempty := by
    have h_surj : ∀ x : ZMod 550172, ∃ k, 1 ≤ k ∧ (Nat.cast (2^k - k) : ZMod 550172) = x := by
      intro x
      let r := r_table.getD (x.val % 196) 2
      let val_2_r := fast_mod_pow 2 r 137543
      let val_r_X := (r + x.val) % 137543
      let num := (val_2_r + 137543 - val_r_X) % 137543
      let H := num / 49
      let q := (H * 1938) % 2807
      use q * 117600 + r
      have hq : q ≡ H * 1938 [MOD 2807] := Nat.mod_mod (H * 1938) 2807
      have h_sh := combine_modular_proof x.val q hq
      dsimp [r, val_2_r, val_r_X, num, H, q] at h_sh ⊢
      refine ⟨h_sh.1, ?_⟩
      rw [h_sh.2]
      rw [ZMod.natCast_zmod_val x]
    rcases exists_M_of_surjective h_surj with ⟨M, hM⟩
    exact ⟨M, hM⟩
  have h_prime_bound : Nat.nth Nat.Prime 550171 ≤ 8165753 := by
    have h_count : 550172 ≤ Nat.count Nat.Prime 8165753 := by decide
    rw [← Nat.count_le_iff_le_nth (Nat.infinite_setOf_prime)]
    exact h_count
  have h_bound : 2 * (Nat.nth Nat.Prime 550171 - 1) ≤ 16331504 := by omega
  have h_prop_16331503 : A232616_prop 550172 16331503 := by
    have h_le : A232616 550172 ≤ 16331503 := by
      rw [h_inf] at h1 ⊢
      omega
    have hp_M : A232616_prop 550172 (A232616 550172) := by
      rw [h_inf]
      exact sInf_mem h_S_nonempty
    exact prop_mono h_le hp_M
  have h_mem : (13573 : ZMod 550172) ∈ (Finset.Icc 1 16331503).image (fun k => (Nat.cast (2^k - k) : ZMod 550172)) := by
    rw [← h_prop_16331503]
    exact mem_univ _
  rcases Finset.mem_image.mp h_mem with ⟨k, hk, hk_eq⟩
  have hk_range : 1 ≤ k ∧ k ≤ 16331503 := by
    exact Finset.mem_Icc.mp hk
  have hk_eq_nat : (2^k - k) % 550172 = 13573 % 550172 := by
    have hk_eq_cast : (Nat.cast (2^k - k) : ZMod 550172) = (Nat.cast 13573 : ZMod 550172) := by
      rw [hk_eq]
      rfl
    exact ZMod.natCast_eq_natCast_iff.mp hk_eq_cast
  have h_div1 : 1372 ∣ 550172 := by decide
  have hk_eq_1372 : (2^k - k) % 1372 = 1225 % 1372 := by
    have h_mod := mod_of_mod_eq hk_eq_nat h_div1
    exact h_mod
  have h_div2 : 343 ∣ 1372 := by decide
  have hk_eq_343 : (2^k - k) % 343 = 196 % 343 := by
    have h_mod := mod_of_mod_eq hk_eq_1372 h_div2
    exact h_mod
  have h_div3 : 4 ∣ 1372 := by decide
  have hk_eq_4 : (2^k - k) % 4 = 1 % 4 := by
    have h_mod := mod_of_mod_eq hk_eq_1372 h_div3
    exact h_mod
  have hk_ge2 : 2 ≤ k := by
    have h_ne1 : k ≠ 1 := by
      rintro rfl
      revert hk_eq_343
      decide
    omega
  have hk_4 : k % 4 = 3 := by
    have h_pow4 : 2^k % 4 = 0 := by
      obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hk_ge2
      rw [hd, pow_add]
      exact Nat.mul_mod_right 4 (2^d)
    have h_eq : (2^k - k) % 4 = (0 + 4 - k % 4) % 4 := by
      rw [← h_pow4]
      exact Nat.sub_mod hk_ge2 (k_le_two_pow k) 4
    have h_comb : (0 + 4 - k % 4) % 4 = 1 % 4 := by
      rw [← hk_eq_4, ← h_eq]
    omega
  have h_pow_eq : 2^k % 343 = 2^(k % 4116) % 343 := by
    have h_div_mod := Nat.div_add_mod k 4116
    conv_lhs => rw [← h_div_mod]
    exact test_power_period (k / 4116) (k % 4116)
  have h_r : (k % 4116) % 4 = 3 := by
    rw [Nat.mod_mod_of_dvd k (by decide)]
    exact hk_4
  have h_r_bound : k % 4116 < 4116 := Nat.mod_lt _ (by decide)
  have h_check_r : check_r (k % 4116) = true := by
    unfold check_r
    have h_cond : ((k % 4116) % 4 == 3) = true := by
      rw [beq_iff_eq]
      exact h_r
    rw [h_cond]
    simp only [if_true]
    rw [beq_iff_eq]
    have h_add : (2^k - k + k) % 343 = (196 + k) % 343 := by
      exact Nat.ModEq.add_right k hk_eq_343
    rw [Nat.sub_add_cancel (k_le_two_pow k)] at h_add
    have h_div343 : 343 ∣ 4116 := by decide
    have h_k_r : k ≡ k % 4116 [MOD 343] := (Nat.mod_mod_of_dvd k h_div343).symm
    have h_add_r : (196 + k) % 343 = (196 + k % 4116) % 343 := by
      exact Nat.ModEq.add_left 196 h_k_r
    have h_comm1 : (196 + k % 4116) % 343 = (k % 4116 + 196) % 343 := by
      rw [add_comm 196]
    rw [h_pow_eq] at h_add
    rw [h_add_r, h_comm1] at h_add
    exact h_add
  have h_in_list : k % 4116 ∈ [3371, 3123, 1003] := by
    have h_mem_loop : k % 4116 ∈ find_sols_loop 0 4116 [] := by
      apply mem_find_sols_loop
      · omega
      · rw [zero_add]
        exact h_r_bound
      · exact h_check_r
    rw [sols_eq] at h_mem_loop
    exact h_mem_loop
  have h_div4 : 1604 ∣ 550172 := by decide
  have hk_eq_1604 : (2^k - k) % 1604 = 741 % 1604 := by
    have h_mod := mod_of_mod_eq hk_eq_nat h_div4
    exact h_mod
  have hk_eq_1604' : fast_mod_pow 2 k 1604 = (k + 741) % 1604 := by
    have h_fast_eq := fast_mod_pow_eq k 1604 (by decide) (by omega)
    rw [h_fast_eq]
    have h_add := Nat.ModEq.add_right k hk_eq_1604
    rw [Nat.sub_add_cancel (k_le_two_pow k)] at h_add
    have h_comm : (741 + k) % 1604 = (k + 741) % 1604 := by rw [add_comm]
    rw [h_comm] at h_add
    exact h_add
  have h_q_bound : k / 4116 ≤ 3967 := by
    have hk_le := hk_range.2
    have h_div_le : k / 4116 ≤ 16331503 / 4116 := Nat.div_le_div_right hk_le
    have h_val : 16331503 / 4116 = 3967 := rfl
    omega
  have h_check_q_true : check_q (k / 4116) (k % 4116) = true := by
    unfold check_q
    have h_k_eq : 4116 * (k / 4116) + k % 4116 = k := Nat.div_add_mod k 4116
    rw [h_k_eq, hk_eq_1604']
    simp
  have h_contradiction : check_q_loop (k / 4116) (3968 - k / 4116) (k % 4116) = false := by
    have h_pos : 0 < 3968 - k / 4116 := by omega
    obtain ⟨d, hd⟩ := Nat.exists_eq_succ_of_ne_zero (ne_of_gt h_pos)
    rw [hd]
    unfold check_q_loop
    rw [h_check_q_true]
    simp
  have h_loop_zero : check_q_loop 0 3968 (k % 4116) = true := by
    rcases h_in_list with h_eq | h_eq | h_eq
    · rw [h_eq]; exact check_3371
    · rw [h_eq]; exact check_3123
    · rw [h_eq]; exact check_1003
  have h_true : check_q_loop (k / 4116) (3968 - k / 4116) (k % 4116) = true := by
    have h_suffix := check_q_loop_suffix 0 3968 (k % 4116) h_loop_zero (k / 4116) (by omega)
    rw [zero_add] at h_suffix
    exact h_suffix
  exact Bool.noConfusion (h_contradiction.symm.trans h_true)

