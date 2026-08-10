import FormalConjectures.Util.ProblemImports

open Nat Finset Rat
open scoped BigOperators

set_option maxRecDepth 200000
set_option maxHeartbeats 100000000
set_option exponentiation.threshold 2000

noncomputable def A060841 (n : ℕ) : ℕ :=
  let val_rat : ℚ := (Icc 1 n).prod (fun k : ℕ => ((k : ℚ) ^ 2) / (k.totient : ℚ))
  val_rat.num.natAbs

noncomputable def A060841_val_rat (n : ℕ) : ℚ :=
  (Icc 1 n).prod (fun k : ℕ => ((k : ℚ) ^ 2) / (k.totient : ℚ))

-- Precomputed 3-adic valuations of totient(k) for k = 1 to 1807
def v_list : List ℕ := [
0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 1, 1, 0, 0, 0, 1, 2, 0, 1, 0, 0, 0, 0, 1, 2, 1, 0, 0, 1, 0, 0, 0, 1, 1, 2, 2, 1, 0, 0, 1, 1, 0, 1, 0, 0, 0, 1, 0, 0, 1, 0, 2, 0, 1, 2, 0, 0, 0, 1, 1, 2, 0, 1, 0, 1, 0, 0, 1, 0, 1, 2, 2, 0, 2, 1, 1, 1, 0, 3, 0, 0, 1, 0, 1, 0, 0, 0, 1, 2, 0, 1, 0, 2, 0, 1, 1, 1, 0, 0, 0, 1, 1, 1, 0, 0, 2, 3, 0, 2, 1, 0, 2, 0, 0, 2, 0, 1, 0, 0, 1, 0, 1, 0, 2, 2, 0, 1, 1, 0, 0, 3, 1, 2, 0, 0, 0, 1, 1, 0, 0, 1, 1, 0, 2, 1, 2, 0, 0, 1, 2, 1, 1, 1, 1, 1, 1, 0, 0, 1, 3, 4, 0, 0, 0, 0, 1, 1, 0, 3, 1, 0, 0, 1, 0, 0, 0, 0, 1, 2, 2, 1, 0, 2, 1, 0, 0, 3, 2, 0, 0, 1, 1, 1, 1, 0, 1, 2, 0, 1, 0, 1, 0, 0, 1, 1, 1, 2, 1, 1, 0, 0, 0, 1, 2, 2, 3, 2, 0, 1, 2, 1, 1, 1, 0, 0, 2, 1, 0, 1, 0, 0, 2, 0, 0, 1, 1, 0, 0, 1, 0, 4, 1, 1, 0, 3, 1, 0, 0, 0, 2, 0, 2, 0, 0, 0, 1, 3, 1, 1, 0, 0, 0, 0, 3, 0, 1, 0, 2, 3, 0, 2, 0, 0, 0, 1, 1, 2, 1, 0, 0, 1, 0, 2, 1, 1, 1, 0, 0, 1, 2, 0, 1, 0, 2, 2, 0, 1, 0, 2, 1, 0, 2, 1, 1, 2, 1, 1, 1, 0, 1, 1, 1, 2, 1, 0, 0, 0, 0, 0, 1, 2, 3, 1, 4, 3, 0, 1, 0, 1, 0, 3, 0, 1, 1, 1, 1, 0, 0, 1, 3, 1, 1, 0, 0, 0, 0, 1, 1, 3, 0, 0, 0, 0, 0, 1, 0, 0, 1, 2, 2, 0, 2, 2, 1, 1, 0, 1, 2, 1, 1, 1, 0, 0, 0, 1, 3, 3, 2, 2, 0, 0, 0, 1, 1, 2, 1, 0, 1, 0, 1, 0, 0, 1, 1, 2, 2, 3, 0, 0, 1, 2, 0, 3, 1, 2, 0, 1, 0, 0, 1, 1, 1, 0, 1, 1, 2, 0, 1, 1, 1, 1, 0, 0, 0, 2, 0, 1, 1, 0, 2, 3, 2, 0, 3, 2, 2, 1, 0, 2, 1, 0, 2, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 2, 2, 1, 1, 2, 0, 0, 1, 1, 0, 1, 0, 0, 2, 2, 0, 1, 0, 1, 1, 2, 1, 1, 0, 0, 0, 3, 1, 1, 0, 1, 4, 5, 1, 4, 1, 0, 0, 0, 3, 1, 1, 1, 0, 1, 0, 0, 0, 0, 2, 0, 0, 1, 2, 0, 0, 3, 0, 4, 0, 1, 1, 0, 3, 0, 1, 0, 1, 2, 0, 1, 0, 1, 0, 0, 0, 1, 3, 1, 0, 0, 1, 0, 0, 1, 2, 3, 3, 2, 0, 3, 2, 1, 0, 2, 0, 2, 0, 2, 1, 2, 1, 0, 2, 2, 1, 0, 0, 0, 0, 0, 1, 4, 0, 0, 2, 1, 1, 0, 1, 0, 1, 2, 0, 1, 0, 1, 1, 0, 2, 2, 0, 0, 1, 3, 0, 0, 2, 0, 2, 1, 0, 2, 1, 0, 0, 1, 2, 2, 1, 0, 0, 1, 2, 1, 1, 1, 1, 2, 2, 0, 1, 0, 1, 1, 1, 2, 0, 1, 1, 0, 1, 2, 1, 2, 2, 2, 1, 1, 0, 2, 0, 2, 0, 1, 0, 0, 0, 1, 1, 1, 2, 0, 3, 0, 1, 2, 4, 0, 3, 0, 0, 3, 1, 0, 0, 1, 1, 1, 0, 3, 3, 0, 0, 1, 1, 1, 1, 1, 1, 2, 1, 0, 0, 2, 0, 0, 1, 0, 3, 0, 1, 1, 1, 1, 0, 1, 0, 2, 0, 1, 0, 0, 1, 0, 1, 0, 3, 4, 0, 0, 0, 1, 0, 1, 0, 2, 0, 1, 1, 1, 0, 0, 0, 0, 1, 2, 2, 1, 2, 0, 0, 1, 2, 5, 2, 1, 1, 1, 1, 1, 0, 1, 1, 2, 2, 3, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 0, 1, 1, 3, 3, 3, 0, 2, 0, 2, 4, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 2, 1, 1, 3, 0, 2, 1, 0, 0, 2, 1, 1, 0, 1, 0, 0, 1, 1, 1, 2, 2, 0, 2, 0, 3, 0, 0, 1, 0, 2, 1, 1, 2, 0, 0, 0, 3, 4, 1, 3, 2, 4, 0, 3, 1, 3, 0, 0, 0, 1, 1, 0, 1, 0, 1, 2, 0, 1, 1, 1, 1, 0, 2, 3, 0, 0, 1, 0, 1, 0, 1, 1, 1, 1, 0, 1, 0, 2, 0, 1, 2, 3, 0, 0, 1, 1, 1, 1, 0, 0, 2, 0, 3, 0, 2, 1, 0, 2, 3, 2, 2, 1, 2, 1, 1, 0, 0, 0, 2, 2, 1, 0, 0, 0, 2, 3, 0, 3, 1, 2, 0, 0, 1, 1, 0, 1, 1, 0, 0, 2, 0, 2, 1, 1, 0, 1, 2, 0, 2, 0, 1, 1, 1, 1, 2, 3, 0, 2, 0, 1, 1, 2, 1, 2, 0, 0, 1, 3, 0, 0, 0, 0, 2, 2, 2, 1, 0, 0, 1, 0, 0, 3, 1, 0, 1, 3, 2, 0, 1, 0, 1, 0, 0, 0, 0, 1, 0, 1, 3, 1, 1, 1, 1, 1, 0, 2, 1, 0, 4, 2, 5, 1, 1, 0, 4, 0, 1, 4, 0, 0, 0, 0, 0, 1, 3, 1, 1, 2, 1, 1, 1, 2, 0, 1, 1, 4, 0, 2, 0, 0, 0, 1, 0, 2, 2, 2, 0, 1, 0, 0, 1, 1, 2, 1, 0, 0, 0, 1, 3, 1, 0, 0, 4, 2, 0, 1, 1, 0, 1, 1, 0, 1, 3, 1, 0, 1, 1, 0, 0, 1, 1, 2, 2, 1, 0, 0, 1, 1, 0, 4, 1, 1, 0, 2, 0, 0, 0, 0, 1, 2, 3, 0, 1, 1, 0, 1, 0, 2, 1, 2, 0, 1, 0, 0, 1, 1, 2, 0, 3, 2, 3, 2, 2, 1, 0, 1, 3, 0, 2, 1, 1, 2, 0, 0, 2, 2, 0, 1, 2, 0, 0, 1, 2, 2, 1, 0, 2, 0, 1, 1, 0, 1, 2, 2, 2, 1, 1, 2, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 1, 4, 0, 0, 3, 0, 1, 2, 5, 1, 3, 1, 1, 0, 3, 1, 0, 0, 0, 1, 2, 2, 1, 0, 1, 1, 3, 0, 3, 1, 0, 1, 0, 0, 0, 2, 1, 2, 2, 0, 0, 0, 0, 1, 0, 3, 1, 0, 0, 0, 2, 2, 1, 0, 0, 2, 0, 1, 2, 0, 0, 2, 0, 1, 4, 0, 3, 0, 1, 1, 0, 2, 1, 2, 0, 1, 2, 0, 1, 0, 1, 1, 4, 2, 0, 1, 0, 1, 2, 1, 0, 1, 1, 2, 1, 2, 0, 0, 1, 1, 1, 0, 3, 1, 1, 1, 1, 1, 2, 2, 0, 0, 0, 1, 1, 1, 1, 0, 2, 1, 1, 2, 0, 1, 0, 2, 0, 2, 2, 2, 1, 1, 0, 1, 3, 0, 2, 2, 1, 0, 3, 2, 0, 0, 0, 1, 2, 0, 2, 0, 0, 0, 0, 1, 2, 1, 0, 1, 1, 2, 0, 0, 3, 3, 4, 0, 3, 1, 0, 2, 1, 4, 1, 0, 0, 3, 1, 0, 2, 0, 1, 3, 0, 1, 1, 0, 0, 0, 1, 1, 3, 1, 0, 1, 1, 0, 0, 3, 0, 3, 2, 0, 0, 0, 1, 1, 2, 1, 1, 1, 1, 1, 0, 1, 0, 1, 2, 2, 2, 1, 0, 0, 3, 0, 0, 2, 2, 0, 0, 0, 0, 1, 2, 0, 0, 3, 2, 0, 1, 1, 0, 1, 0, 1, 3, 1, 1, 0, 1, 1, 0, 0, 1, 2, 4, 0, 1, 1, 1, 0, 3, 0, 2, 1, 2, 0, 1, 1, 0, 0, 1, 3, 0, 4, 2, 0, 0, 0, 0, 0, 2, 1, 1, 0, 4, 1, 1, 0, 1, 2, 2, 0, 2, 1, 0, 1, 1, 1, 2, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 2, 3, 2, 0, 1, 1, 2, 2, 0, 0, 0, 1, 1, 1, 2, 1, 5, 6, 2, 5, 1, 3, 1, 0, 1, 5, 1, 1, 1, 1, 0, 0, 1, 0, 1, 2, 2, 0, 2, 0, 3, 1, 1, 2, 0, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 0, 3, 1, 1, 0, 2, 0, 0, 1, 0, 1, 0, 3, 0, 3, 0, 3, 2, 0, 2, 2, 2, 0, 0, 2, 1, 4, 0, 0, 1, 1, 2, 0, 3, 1, 2, 0, 0, 1, 5, 1, 1, 0, 1, 1, 1, 0, 2, 2, 2, 1, 0, 1, 0, 3, 0, 0, 1, 2, 0, 1, 2, 0, 0, 0, 1, 2, 3, 1, 2, 1, 0, 0, 1, 1, 2, 0, 2, 0, 1, 1, 1, 1, 0, 1, 0, 2, 0, 2, 1, 0, 3, 2, 2, 0, 0, 3, 1, 0, 1, 0, 0, 1, 2, 0, 0, 2, 0, 1, 1, 1, 1, 2, 0, 0, 2, 0, 1, 0, 0, 3, 4, 4, 3, 1, 1, 3, 1, 2, 3, 4, 1, 0, 0, 3, 3, 1, 0, 3, 0, 0, 1, 0, 1, 0, 1, 1, 3, 1, 1, 0, 3, 1, 2, 0, 1, 1, 2, 2, 2, 0, 1, 1, 1, 1, 3, 1, 0, 1, 1, 0, 0, 2, 1, 3, 1, 0, 2, 0, 2, 1, 0, 0, 1, 1, 1, 0, 2, 1, 0, 1, 2, 1, 2, 1, 0, 0, 0, 1, 1, 0, 5, 2, 1, 0, 1, 1, 0, 2, 0, 3, 0, 0, 1, 0, 1, 1, 0, 1, 1, 1, 0, 1, 1, 0, 0, 0, 1, 2, 4, 0, 2, 3, 0, 0, 0, 2, 2, 1, 2, 0, 1, 2, 1, 3, 1, 2, 2, 2, 0, 1, 1, 2, 1, 1, 3, 1, 1, 0, 1, 0, 0, 0, 1, 2, 0, 2, 3, 1, 1, 0, 1, 0, 1, 0, 0, 2, 1, 3, 0, 0, 1, 3, 4, 1, 1, 2, 0, 0, 1, 0, 3, 1, 4, 1, 0, 0, 0, 1, 1, 1, 2, 0, 1, 0, 2, 2, 2
]

def sum_v (n : ℕ) : ℕ :=
  match n with
  | 0 => 0
  | m + 1 => sum_v m + v_list.getD m 0

def sum_u (n : ℕ) : ℕ :=
  match n with
  | 0 => 0
  | m + 1 => sum_u m + 2 * padicValNat 3 (m + 1)

def num_val (n : ℕ) : ℕ :=
  match n with
  | 0 => 1
  | m + 1 => num_val m * (m + 1) ^ 2

def den_val (n : ℕ) : ℕ :=
  match n with
  | 0 => 1
  | m + 1 => den_val m * totient (m + 1)

def totient_loop (n : ℕ) (acc : ℕ) (i : ℕ) : ℕ := 
  match i with
  | 0 => acc
  | i' + 1 =>
    if n.gcd (i' + 1) == 1 then totient_loop n (acc + 1) i'
    else totient_loop n acc i'

def fast_totient (n : ℕ) : ℕ := 
  if n = 1 then 1
  else totient_loop n 0 (n - 1)

lemma totient_loop_eq_filter (n : ℕ) (hn : n > 1) (acc : ℕ) (i : ℕ) :
    totient_loop n acc i = acc + ((List.range (i + 1)).filter (fun a => n.gcd a == 1)).length := by
  induction i generalizing acc with
  | zero =>
    dsimp [totient_loop]
    have h_gcd : (n.gcd 0 == 1) = false := by
      have h1 : n.gcd 0 = n := Nat.gcd_zero_right n
      change decide (n.gcd 0 = 1) = false
      simp only [h1]
      exact decide_eq_false hn.ne'
    simp only [List.filter_cons, List.filter_nil, List.length]
    rw [h_gcd]
    rfl
  | succ i' ih =>
    dsimp [totient_loop]
    split_ifs with h
    · rw [ih]
      have : (List.range (i' + 1 + 1)).filter (fun a => n.gcd a == 1) =
             ((List.range (i' + 1)).filter (fun a => n.gcd a == 1)) ++ [i' + 1] := by
        rw [List.range_succ, List.filter_append]
        simp [h]
      rw [this, List.length_append]
      simp
      omega
    · rw [ih]
      have : (List.range (i' + 1 + 1)).filter (fun a => n.gcd a == 1) =
             ((List.range (i' + 1)).filter (fun a => n.gcd a == 1)) := by
        rw [List.range_succ, List.filter_append]
        simp [h]
      rw [this]

theorem fast_totient_eq_totient (n : ℕ) : fast_totient n = totient n := by
  rcases n with _ | _ | n''
  · rfl
  · rfl
  · have hn_gt1 : n'' + 2 > 1 := by omega
    dsimp [fast_totient, totient]
    rw [totient_loop_eq_filter (n'' + 2) hn_gt1 0 (n'' + 1)]
    simp
    rfl

lemma totient_dvd_val_block_0 (m : ℕ) (h1 : 0 ≤ m) (h2 : m < 30) : 3 ^ (v_list.getD m 0) ∣ totient (m + 1) := by
  have hd : m - 0 < 30 := by omega
  generalize h_d : m - 0 = d at *
  have h_eq : m = 0 + d := by omega
  rw [h_eq]
  rw [← fast_totient_eq_totient]
  rcases d with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | d_large
  · exact one_dvd _
  · exact one_dvd _
  · exact one_dvd _
  · exact one_dvd _
  · exact one_dvd _
  · exact one_dvd _
  · decide
  · exact one_dvd _
  · decide
  · exact one_dvd _
  · exact one_dvd _
  · exact one_dvd _
  · decide
  · decide
  · exact one_dvd _
  · exact one_dvd _
  · exact one_dvd _
  · decide
  · decide
  · exact one_dvd _
  · decide
  · exact one_dvd _
  · exact one_dvd _
  · exact one_dvd _
  · exact one_dvd _
  · decide
  · decide
  · decide
  · exact one_dvd _
  · exact one_dvd _
  · omega

lemma totient_dvd_val_block_1 (m : ℕ) (h1 : 30 ≤ m) (h2 : m < 60) : 3 ^ (v_list.getD m 0) ∣ totient (m + 1) := by
  have hd : m - 30 < 30 := by omega
  generalize h_d : m - 30 = d at *
  have h_eq : m = 30 + d := by omega
  rw [h_eq]
  rw [← fast_totient_eq_totient]
  rcases d with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | d_large
  · decide
  · exact one_dvd _
  · exact one_dvd _
  · exact one_dvd _
  · decide
  · decide
  · decide
  · decide
  · decide
  · exact one_dvd _
  · exact one_dvd _
  · decide
  · decide
  · exact one_dvd _
  · decide
  · exact one_dvd _
  · exact one_dvd _
  · exact one_dvd _
  · decide
  · exact one_dvd _
  · exact one_dvd _
  · decide
  · exact one_dvd _
  · decide
  · exact one_dvd _
  · decide
  · decide
  · exact one_dvd _
  · exact one_dvd _
  · exact one_dvd _
  · omega

lemma totient_dvd_val_block_2 (m : ℕ) (h1 : 60 ≤ m) (h2 : m < 90) : 3 ^ (v_list.getD m 0) ∣ totient (m + 1) := by
  have hd : m - 60 < 30 := by omega
  generalize h_d : m - 60 = d at *
  have h_eq : m = 60 + d := by omega
  rw [h_eq]
  rw [← fast_totient_eq_totient]
  rcases d with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | d_large
  · decide
  · decide
  · decide
  · exact one_dvd _
  · decide
  · exact one_dvd _
  · decide
  · exact one_dvd _
  · exact one_dvd _
  · decide
  · exact one_dvd _
  · decide
  · decide
  · decide
  · exact one_dvd _
  · decide
  · decide
  · decide
  · decide
  · exact one_dvd _
  · decide
  · exact one_dvd _
  · exact one_dvd _
  · decide
  · exact one_dvd _
  · decide
  · exact one_dvd _
  · exact one_dvd _
  · exact one_dvd _
  · decide
  · omega

lemma totient_dvd_val_block_3 (m : ℕ) (h1 : 90 ≤ m) (h2 : m < 120) : 3 ^ (v_list.getD m 0) ∣ totient (m + 1) := by
  have hd : m - 90 < 30 := by omega
  generalize h_d : m - 90 = d at *
  have h_eq : m = 90 + d := by omega
  rw [h_eq]
  rw [← fast_totient_eq_totient]
  rcases d with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | d_large
  · decide
  · exact one_dvd _
  · decide
  · exact one_dvd _
  · decide
  · exact one_dvd _
  · decide
  · decide
  · decide
  · exact one_dvd _
  · exact one_dvd _
  · exact one_dvd _
  · decide
  · decide
  · decide
  · exact one_dvd _
  · exact one_dvd _
  · decide
  · decide
  · exact one_dvd _
  · decide
  · decide
  · exact one_dvd _
  · decide
  · exact one_dvd _
  · exact one_dvd _
  · decide
  · exact one_dvd _
  · decide
  · exact one_dvd _
  · omega

lemma totient_dvd_val_block_4 (m : ℕ) (h1 : 120 ≤ m) (h2 : m < 150) : 3 ^ (v_list.getD m 0) ∣ totient (m + 1) := by
  have hd : m - 120 < 30 := by omega
  generalize h_d : m - 120 = d at *
  have h_eq : m = 120 + d := by omega
  rw [h_eq]
  rw [← fast_totient_eq_totient]
  rcases d with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | d_large
  · exact one_dvd _
  · decide
  · exact one_dvd _
  · decide
  · exact one_dvd _
  · decide
  · decide
  · exact one_dvd _
  · decide
  · decide
  · exact one_dvd _
  · exact one_dvd _
  · decide
  · decide
  · decide
  · exact one_dvd _
  · exact one_dvd _
  · exact one_dvd _
  · decide
  · decide
  · exact one_dvd _
  · exact one_dvd _
  · decide
  · decide
  · exact one_dvd _
  · decide
  · decide
  · decide
  · exact one_dvd _
  · exact one_dvd _
  · omega

lemma totient_dvd_val_block_5 (m : ℕ) (h1 : 150 ≤ m) (h2 : m < 180) : 3 ^ (v_list.getD m 0) ∣ totient (m + 1) := by
  have hd : m - 150 < 30 := by omega
  generalize h_d : m - 150 = d at *
  have h_eq : m = 150 + d := by omega
  rw [h_eq]
  rw [← fast_totient_eq_totient]
  rcases d with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | d_large
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · exact one_dvd _
  · exact one_dvd _
  · decide
  · decide
  · decide
  · exact one_dvd _
  · exact one_dvd _
  · exact one_dvd _
  · exact one_dvd _
  · decide
  · decide
  · exact one_dvd _
  · decide
  · decide
  · exact one_dvd _
  · exact one_dvd _
  · decide
  · exact one_dvd _
  · exact one_dvd _
  · exact one_dvd _
  · exact one_dvd _
  · decide
  · omega

lemma totient_dvd_val_block_6 (m : ℕ) (h1 : 180 ≤ m) (h2 : m < 210) : 3 ^ (v_list.getD m 0) ∣ totient (m + 1) := by
  have hd : m - 180 < 30 := by omega
  generalize h_d : m - 180 = d at *
  have h_eq : m = 180 + d := by omega
  rw [h_eq]
  rw [← fast_totient_eq_totient]
  rcases d with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | d_large
  · decide
  · decide
  · decide
  · exact one_dvd _
  · decide
  · decide
  · exact one_dvd _
  · exact one_dvd _
  · decide
  · decide
  · exact one_dvd _
  · exact one_dvd _
  · decide
  · decide
  · decide
  · decide
  · exact one_dvd _
  · decide
  · decide
  · exact one_dvd _
  · decide
  · exact one_dvd _
  · decide
  · exact one_dvd _
  · exact one_dvd _
  · decide
  · decide
  · decide
  · decide
  · decide
  · omega

lemma totient_dvd_val_block_7 (m : ℕ) (h1 : 210 ≤ m) (h2 : m < 240) : 3 ^ (v_list.getD m 0) ∣ totient (m + 1) := by
  have hd : m - 210 < 30 := by omega
  generalize h_d : m - 210 = d at *
  have h_eq : m = 210 + d := by omega
  rw [h_eq]
  rw [← fast_totient_eq_totient]
  rcases d with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | d_large
  · decide
  · exact one_dvd _
  · exact one_dvd _
  · exact one_dvd _
  · decide
  · decide
  · decide
  · decide
  · decide
  · exact one_dvd _
  · decide
  · decide
  · decide
  · decide
  · decide
  · exact one_dvd _
  · exact one_dvd _
  · decide
  · decide
  · exact one_dvd _
  · decide
  · exact one_dvd _
  · exact one_dvd _
  · decide
  · exact one_dvd _
  · exact one_dvd _
  · decide
  · decide
  · exact one_dvd _
  · exact one_dvd _
  · omega

lemma totient_dvd_val_block_8 (m : ℕ) (h1 : 240 ≤ m) (h2 : m < 270) : 3 ^ (v_list.getD m 0) ∣ totient (m + 1) := by
  have hd : m - 240 < 30 := by omega
  generalize h_d : m - 240 = d at *
  have h_eq : m = 240 + d := by omega
  rw [h_eq]
  rw [← fast_totient_eq_totient]
  rcases d with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | d_large
  · decide
  · exact one_dvd _
  · decide
  · decide
  · decide
  · exact one_dvd _
  · decide
  · decide
  · exact one_dvd _
  · exact one_dvd _
  · exact one_dvd _
  · decide
  · exact one_dvd _
  · decide
  · exact one_dvd _
  · exact one_dvd _
  · exact one_dvd _
  · decide
  · decide
  · decide
  · decide
  · exact one_dvd _
  · exact one_dvd _
  · exact one_dvd _
  · exact one_dvd _
  · decide
  · exact one_dvd _
  · decide
  · exact one_dvd _
  · decide
  · omega

lemma totient_dvd_val_block_9 (m : ℕ) (h1 : 270 ≤ m) (h2 : m < 300) : 3 ^ (v_list.getD m 0) ∣ totient (m + 1) := by
  have hd : m - 270 < 30 := by omega
  generalize h_d : m - 270 = d at *
  have h_eq : m = 270 + d := by omega
  rw [h_eq]
  rw [← fast_totient_eq_totient]
  rcases d with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | d_large
  · decide
  · exact one_dvd _
  · decide
  · exact one_dvd _
  · exact one_dvd _
  · exact one_dvd _
  · decide
  · decide
  · decide
  · decide
  · exact one_dvd _
  · exact one_dvd _
  · decide
  · exact one_dvd _
  · decide
  · decide
  · decide
  · decide
  · exact one_dvd _
  · exact one_dvd _
  · decide
  · decide
  · exact one_dvd _
  · decide
  · exact one_dvd _
  · decide
  · decide
  · exact one_dvd _
  · decide
  · exact one_dvd _
  · omega

lemma totient_dvd_val_block_10 (m : ℕ) (h1 : 300 ≤ m) (h2 : m < 330) : 3 ^ (v_list.getD m 0) ∣ totient (m + 1) := by
  have hd : m - 300 < 30 := by omega
  generalize h_d : m - 300 = d at *
  have h_eq : m = 300 + d := by omega
  rw [h_eq]
  rw [← fast_totient_eq_totient]
  rcases d with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | d_large
  · decide
  · decide
  · exact one_dvd _
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · exact one_dvd _
  · decide
  · decide
  · decide
  · decide
  · decide
  · exact one_dvd _
  · exact one_dvd _
  · exact one_dvd _
  · exact one_dvd _
  · exact one_dvd _
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · exact one_dvd _
  · decide
  · exact one_dvd _
  · omega

lemma totient_dvd_val_block_11 (m : ℕ) (h1 : 330 ≤ m) (h2 : m < 360) : 3 ^ (v_list.getD m 0) ∣ totient (m + 1) := by
  have hd : m - 330 < 30 := by omega
  generalize h_d : m - 330 = d at *
  have h_eq : m = 330 + d := by omega
  rw [h_eq]
  rw [← fast_totient_eq_totient]
  rcases d with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | d_large
  · decide
  · exact one_dvd _
  · decide
  · exact one_dvd _
  · decide
  · decide
  · decide
  · decide
  · exact one_dvd _
  · exact one_dvd _
  · decide
  · decide
  · decide
  · decide
  · exact one_dvd _
  · exact one_dvd _
  · exact one_dvd _
  · exact one_dvd _
  · decide
  · decide
  · decide
  · exact one_dvd _
  · exact one_dvd _
  · exact one_dvd _
  · exact one_dvd _
  · exact one_dvd _
  · decide
  · exact one_dvd _
  · exact one_dvd _
  · decide
  · omega

lemma totient_dvd_val_block_12 (m : ℕ) (h1 : 360 ≤ m) (h2 : m < 390) : 3 ^ (v_list.getD m 0) ∣ totient (m + 1) := by
  have hd : m - 360 < 30 := by omega
  generalize h_d : m - 360 = d at *
  have h_eq : m = 360 + d := by omega
  rw [h_eq]
  rw [← fast_totient_eq_totient]
  rcases d with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | d_large
  · decide
  · decide
  · exact one_dvd _
  · decide
  · decide
  · decide
  · decide
  · exact one_dvd _
  · decide
  · decide
  · decide
  · decide
  · decide
  · exact one_dvd _
  · exact one_dvd _
  · exact one_dvd _
  · decide
  · decide
  · decide
  · decide
  · decide
  · exact one_dvd _
  · exact one_dvd _
  · exact one_dvd _
  · decide
  · decide
  · decide
  · decide
  · exact one_dvd _
  · decide
  · omega

lemma totient_dvd_val_block_13 (m : ℕ) (h1 : 390 ≤ m) (h2 : m < 420) : 3 ^ (v_list.getD m 0) ∣ totient (m + 1) := by
  have hd : m - 390 < 30 := by omega
  generalize h_d : m - 390 = d at *
  have h_eq : m = 390 + d := by omega
  rw [h_eq]
  rw [← fast_totient_eq_totient]
  rcases d with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | d_large
  · exact one_dvd _
  · decide
  · exact one_dvd _
  · exact one_dvd _
  · decide
  · decide
  · decide
  · decide
  · decide
  · exact one_dvd _
  · exact one_dvd _
  · decide
  · decide
  · exact one_dvd _
  · decide
  · decide
  · decide
  · exact one_dvd _
  · decide
  · exact one_dvd _
  · exact one_dvd _
  · decide
  · decide
  · decide
  · exact one_dvd _
  · decide
  · decide
  · decide
  · exact one_dvd _
  · decide
  · omega

lemma totient_dvd_val_block_14 (m : ℕ) (h1 : 420 ≤ m) (h2 : m < 450) : 3 ^ (v_list.getD m 0) ∣ totient (m + 1) := by
  have hd : m - 420 < 30 := by omega
  generalize h_d : m - 420 = d at *
  have h_eq : m = 420 + d := by omega
  rw [h_eq]
  rw [← fast_totient_eq_totient]
  rcases d with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | d_large
  · decide
  · decide
  · decide
  · exact one_dvd _
  · exact one_dvd _
  · exact one_dvd _
  · decide
  · exact one_dvd _
  · decide
  · decide
  · exact one_dvd _
  · decide
  · decide
  · decide
  · exact one_dvd _
  · decide
  · decide
  · decide
  · decide
  · exact one_dvd _
  · decide
  · decide
  · exact one_dvd _
  · decide
  · exact one_dvd _
  · decide
  · exact one_dvd _
  · decide
  · exact one_dvd _
  · decide
  · omega

lemma totient_dvd_val_block_15 (m : ℕ) (h1 : 450 ≤ m) (h2 : m < 480) : 3 ^ (v_list.getD m 0) ∣ totient (m + 1) := by
  have hd : m - 450 < 30 := by omega
  generalize h_d : m - 450 = d at *
  have h_eq : m = 450 + d := by omega
  rw [h_eq]
  rw [← fast_totient_eq_totient]
  rcases d with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | d_large
  · exact one_dvd _
  · exact one_dvd _
  · decide
  · exact one_dvd _
  · decide
  · decide
  · decide
  · decide
  · decide
  · exact one_dvd _
  · exact one_dvd _
  · decide
  · decide
  · exact one_dvd _
  · decide
  · exact one_dvd _
  · exact one_dvd _
  · decide
  · decide
  · exact one_dvd _
  · decide
  · exact one_dvd _
  · decide
  · decide
  · decide
  · decide
  · decide
  · exact one_dvd _
  · exact one_dvd _
  · exact one_dvd _
  · omega

lemma totient_dvd_val_block_16 (m : ℕ) (h1 : 480 ≤ m) (h2 : m < 510) : 3 ^ (v_list.getD m 0) ∣ totient (m + 1) := by
  have hd : m - 480 < 30 := by omega
  generalize h_d : m - 480 = d at *
  have h_eq : m = 480 + d := by omega
  rw [h_eq]
  rw [← fast_totient_eq_totient]
  rcases d with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | d_large
  · decide
  · decide
  · decide
  · exact one_dvd _
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · exact one_dvd _
  · exact one_dvd _
  · exact one_dvd _
  · decide
  · decide
  · decide
  · decide
  · exact one_dvd _
  · decide
  · exact one_dvd _
  · exact one_dvd _
  · exact one_dvd _
  · exact one_dvd _
  · decide
  · exact one_dvd _
  · exact one_dvd _
  · decide
  · decide
  · exact one_dvd _
  · exact one_dvd _
  · omega

lemma totient_dvd_val_block_17 (m : ℕ) (h1 : 510 ≤ m) (h2 : m < 540) : 3 ^ (v_list.getD m 0) ∣ totient (m + 1) := by
  have hd : m - 510 < 30 := by omega
  generalize h_d : m - 510 = d at *
  have h_eq : m = 510 + d := by omega
  rw [h_eq]
  rw [← fast_totient_eq_totient]
  rcases d with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | d_large
  · decide
  · exact one_dvd _
  · decide
  · exact one_dvd _
  · decide
  · decide
  · exact one_dvd _
  · decide
  · exact one_dvd _
  · decide
  · exact one_dvd _
  · decide
  · decide
  · exact one_dvd _
  · decide
  · exact one_dvd _
  · decide
  · exact one_dvd _
  · exact one_dvd _
  · exact one_dvd _
  · decide
  · decide
  · decide
  · exact one_dvd _
  · exact one_dvd _
  · decide
  · exact one_dvd _
  · exact one_dvd _
  · decide
  · decide
  · omega

lemma totient_dvd_val_block_18 (m : ℕ) (h1 : 540 ≤ m) (h2 : m < 570) : 3 ^ (v_list.getD m 0) ∣ totient (m + 1) := by
  have hd : m - 540 < 30 := by omega
  generalize h_d : m - 540 = d at *
  have h_eq : m = 540 + d := by omega
  rw [h_eq]
  rw [← fast_totient_eq_totient]
  rcases d with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | d_large
  · decide
  · decide
  · decide
  · exact one_dvd _
  · decide
  · decide
  · decide
  · exact one_dvd _
  · decide
  · exact one_dvd _
  · decide
  · exact one_dvd _
  · decide
  · decide
  · decide
  · decide
  · exact one_dvd _
  · decide
  · decide
  · decide
  · exact one_dvd _
  · exact one_dvd _
  · exact one_dvd _
  · exact one_dvd _
  · exact one_dvd _
  · decide
  · decide
  · exact one_dvd _
  · exact one_dvd _
  · decide
  · omega

lemma totient_dvd_val_block_19 (m : ℕ) (h1 : 570 ≤ m) (h2 : m < 600) : 3 ^ (v_list.getD m 0) ∣ totient (m + 1) := by
  have hd : m - 570 < 30 := by omega
  generalize h_d : m - 570 = d at *
  have h_eq : m = 570 + d := by omega
  rw [h_eq]
  rw [← fast_totient_eq_totient]
  rcases d with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | d_large
  · decide
  · decide
  · exact one_dvd _
  · decide
  · exact one_dvd _
  · decide
  · decide
  · exact one_dvd _
  · decide
  · exact one_dvd _
  · decide
  · decide
  · exact one_dvd _
  · decide
  · decide
  · exact one_dvd _
  · exact one_dvd _
  · decide
  · decide
  · exact one_dvd _
  · exact one_dvd _
  · decide
  · exact one_dvd _
  · decide
  · decide
  · exact one_dvd _
  · decide
  · decide
  · exact one_dvd _
  · exact one_dvd _
  · omega

lemma totient_dvd_val_block_20 (m : ℕ) (h1 : 600 ≤ m) (h2 : m < 630) : 3 ^ (v_list.getD m 0) ∣ totient (m + 1) := by
  have hd : m - 600 < 30 := by omega
  generalize h_d : m - 600 = d at *
  have h_eq : m = 600 + d := by omega
  rw [h_eq]
  rw [← fast_totient_eq_totient]
  rcases d with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | d_large
  · decide
  · decide
  · decide
  · decide
  · exact one_dvd _
  · exact one_dvd _
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · exact one_dvd _
  · decide
  · exact one_dvd _
  · decide
  · decide
  · decide
  · decide
  · exact one_dvd _
  · decide
  · decide
  · exact one_dvd _
  · decide
  · decide
  · decide
  · decide
  · decide
  · omega

lemma totient_dvd_val_block_21 (m : ℕ) (h1 : 630 ≤ m) (h2 : m < 660) : 3 ^ (v_list.getD m 0) ∣ totient (m + 1) := by
  have hd : m - 630 < 30 := by omega
  generalize h_d : m - 630 = d at *
  have h_eq : m = 630 + d := by omega
  rw [h_eq]
  rw [← fast_totient_eq_totient]
  rcases d with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | d_large
  · decide
  · decide
  · decide
  · exact one_dvd _
  · decide
  · exact one_dvd _
  · decide
  · exact one_dvd _
  · decide
  · exact one_dvd _
  · exact one_dvd _
  · exact one_dvd _
  · decide
  · decide
  · decide
  · decide
  · exact one_dvd _
  · decide
  · exact one_dvd _
  · decide
  · decide
  · decide
  · exact one_dvd _
  · decide
  · exact one_dvd _
  · exact one_dvd _
  · decide
  · decide
  · exact one_dvd _
  · exact one_dvd _
  · omega

lemma totient_dvd_val_block_22 (m : ℕ) (h1 : 660 ≤ m) (h2 : m < 690) : 3 ^ (v_list.getD m 0) ∣ totient (m + 1) := by
  have hd : m - 660 < 30 := by omega
  generalize h_d : m - 660 = d at *
  have h_eq : m = 660 + d := by omega
  rw [h_eq]
  rw [← fast_totient_eq_totient]
  rcases d with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | d_large
  · decide
  · decide
  · decide
  · exact one_dvd _
  · decide
  · decide
  · exact one_dvd _
  · exact one_dvd _
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · exact one_dvd _
  · exact one_dvd _
  · decide
  · exact one_dvd _
  · exact one_dvd _
  · decide
  · exact one_dvd _
  · decide
  · exact one_dvd _
  · decide
  · decide
  · decide
  · decide
  · exact one_dvd _
  · omega

lemma totient_dvd_val_block_23 (m : ℕ) (h1 : 690 ≤ m) (h2 : m < 720) : 3 ^ (v_list.getD m 0) ∣ totient (m + 1) := by
  have hd : m - 690 < 30 := by omega
  generalize h_d : m - 690 = d at *
  have h_eq : m = 690 + d := by omega
  rw [h_eq]
  rw [← fast_totient_eq_totient]
  rcases d with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | d_large
  · decide
  · exact one_dvd _
  · decide
  · exact one_dvd _
  · decide
  · exact one_dvd _
  · exact one_dvd _
  · decide
  · exact one_dvd _
  · decide
  · exact one_dvd _
  · decide
  · decide
  · exact one_dvd _
  · exact one_dvd _
  · exact one_dvd _
  · decide
  · exact one_dvd _
  · decide
  · exact one_dvd _
  · decide
  · exact one_dvd _
  · decide
  · decide
  · decide
  · exact one_dvd _
  · exact one_dvd _
  · exact one_dvd _
  · exact one_dvd _
  · decide
  · omega

lemma totient_dvd_val_block_24 (m : ℕ) (h1 : 720 ≤ m) (h2 : m < 750) : 3 ^ (v_list.getD m 0) ∣ totient (m + 1) := by
  have hd : m - 720 < 30 := by omega
  generalize h_d : m - 720 = d at *
  have h_eq : m = 720 + d := by omega
  rw [h_eq]
  rw [← fast_totient_eq_totient]
  rcases d with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | d_large
  · decide
  · decide
  · decide
  · decide
  · exact one_dvd _
  · exact one_dvd _
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · exact one_dvd _
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · exact one_dvd _
  · decide
  · exact one_dvd _
  · decide
  · decide
  · exact one_dvd _
  · decide
  · exact one_dvd _
  · omega

lemma totient_dvd_val_block_25 (m : ℕ) (h1 : 750 ≤ m) (h2 : m < 780) : 3 ^ (v_list.getD m 0) ∣ totient (m + 1) := by
  have hd : m - 750 < 30 := by omega
  generalize h_d : m - 750 = d at *
  have h_eq : m = 750 + d := by omega
  rw [h_eq]
  rw [← fast_totient_eq_totient]
  rcases d with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | d_large
  · decide
  · exact one_dvd _
  · exact one_dvd _
  · decide
  · decide
  · decide
  · decide
  · decide
  · exact one_dvd _
  · decide
  · exact one_dvd _
  · decide
  · decide
  · exact one_dvd _
  · decide
  · exact one_dvd _
  · decide
  · exact one_dvd _
  · decide
  · decide
  · exact one_dvd _
  · decide
  · exact one_dvd _
  · decide
  · decide
  · decide
  · decide
  · exact one_dvd _
  · decide
  · decide
  · omega

lemma totient_dvd_val_block_26 (m : ℕ) (h1 : 780 ≤ m) (h2 : m < 810) : 3 ^ (v_list.getD m 0) ∣ totient (m + 1) := by
  have hd : m - 780 < 30 := by omega
  generalize h_d : m - 780 = d at *
  have h_eq : m = 780 + d := by omega
  rw [h_eq]
  rw [← fast_totient_eq_totient]
  rcases d with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | d_large
  · exact one_dvd _
  · exact one_dvd _
  · decide
  · decide
  · decide
  · exact one_dvd _
  · decide
  · exact one_dvd _
  · exact one_dvd _
  · decide
  · decide
  · decide
  · decide
  · decide
  · exact one_dvd _
  · decide
  · exact one_dvd _
  · decide
  · exact one_dvd _
  · exact one_dvd _
  · decide
  · exact one_dvd _
  · decide
  · decide
  · decide
  · decide
  · exact one_dvd _
  · exact one_dvd _
  · exact one_dvd _
  · decide
  · omega

lemma totient_dvd_val_block_27 (m : ℕ) (h1 : 810 ≤ m) (h2 : m < 840) : 3 ^ (v_list.getD m 0) ∣ totient (m + 1) := by
  have hd : m - 810 < 30 := by omega
  generalize h_d : m - 810 = d at *
  have h_eq : m = 810 + d := by omega
  rw [h_eq]
  rw [← fast_totient_eq_totient]
  rcases d with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | d_large
  · decide
  · decide
  · decide
  · decide
  · decide
  · exact one_dvd _
  · decide
  · decide
  · decide
  · exact one_dvd _
  · exact one_dvd _
  · exact one_dvd _
  · decide
  · decide
  · exact one_dvd _
  · decide
  · exact one_dvd _
  · decide
  · decide
  · exact one_dvd _
  · decide
  · decide
  · decide
  · decide
  · exact one_dvd _
  · decide
  · decide
  · exact one_dvd _
  · exact one_dvd _
  · decide
  · omega

lemma totient_dvd_val_block_28 (m : ℕ) (h1 : 840 ≤ m) (h2 : m < 870) : 3 ^ (v_list.getD m 0) ∣ totient (m + 1) := by
  have hd : m - 840 < 30 := by omega
  generalize h_d : m - 840 = d at *
  have h_eq : m = 840 + d := by omega
  rw [h_eq]
  rw [← fast_totient_eq_totient]
  rcases d with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | d_large
  · exact one_dvd _
  · decide
  · exact one_dvd _
  · decide
  · decide
  · decide
  · decide
  · exact one_dvd _
  · decide
  · exact one_dvd _
  · decide
  · exact one_dvd _
  · decide
  · decide
  · decide
  · exact one_dvd _
  · exact one_dvd _
  · decide
  · decide
  · decide
  · decide
  · exact one_dvd _
  · exact one_dvd _
  · decide
  · exact one_dvd _
  · decide
  · exact one_dvd _
  · decide
  · decide
  · exact one_dvd _
  · omega

lemma totient_dvd_val_block_29 (m : ℕ) (h1 : 870 ≤ m) (h2 : m < 900) : 3 ^ (v_list.getD m 0) ∣ totient (m + 1) := by
  have hd : m - 870 < 30 := by omega
  generalize h_d : m - 870 = d at *
  have h_eq : m = 870 + d := by omega
  rw [h_eq]
  rw [← fast_totient_eq_totient]
  rcases d with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | d_large
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · exact one_dvd _
  · exact one_dvd _
  · exact one_dvd _
  · decide
  · decide
  · decide
  · exact one_dvd _
  · exact one_dvd _
  · exact one_dvd _
  · decide
  · decide
  · exact one_dvd _
  · decide
  · decide
  · decide
  · exact one_dvd _
  · exact one_dvd _
  · decide
  · decide
  · exact one_dvd _
  · decide
  · decide
  · omega

lemma totient_dvd_val_block_30 (m : ℕ) (h1 : 900 ≤ m) (h2 : m < 930) : 3 ^ (v_list.getD m 0) ∣ totient (m + 1) := by
  have hd : m - 900 < 30 := by omega
  generalize h_d : m - 900 = d at *
  have h_eq : m = 900 + d := by omega
  rw [h_eq]
  rw [← fast_totient_eq_totient]
  rcases d with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | d_large
  · exact one_dvd _
  · exact one_dvd _
  · decide
  · exact one_dvd _
  · decide
  · decide
  · decide
  · exact one_dvd _
  · decide
  · decide
  · exact one_dvd _
  · decide
  · exact one_dvd _
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · exact one_dvd _
  · decide
  · exact one_dvd _
  · decide
  · decide
  · decide
  · decide
  · decide
  · exact one_dvd _
  · exact one_dvd _
  · decide
  · omega

lemma totient_dvd_val_block_31 (m : ℕ) (h1 : 930 ≤ m) (h2 : m < 960) : 3 ^ (v_list.getD m 0) ∣ totient (m + 1) := by
  have hd : m - 930 < 30 := by omega
  generalize h_d : m - 930 = d at *
  have h_eq : m = 930 + d := by omega
  rw [h_eq]
  rw [← fast_totient_eq_totient]
  rcases d with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | d_large
  · decide
  · exact one_dvd _
  · exact one_dvd _
  · exact one_dvd _
  · exact one_dvd _
  · decide
  · decide
  · decide
  · decide
  · exact one_dvd _
  · exact one_dvd _
  · decide
  · exact one_dvd _
  · exact one_dvd _
  · decide
  · decide
  · exact one_dvd _
  · decide
  · decide
  · decide
  · exact one_dvd _
  · decide
  · exact one_dvd _
  · decide
  · exact one_dvd _
  · exact one_dvd _
  · exact one_dvd _
  · exact one_dvd _
  · decide
  · exact one_dvd _
  · omega

lemma totient_dvd_val_block_32 (m : ℕ) (h1 : 960 ≤ m) (h2 : m < 990) : 3 ^ (v_list.getD m 0) ∣ totient (m + 1) := by
  have hd : m - 960 < 30 := by omega
  generalize h_d : m - 960 = d at *
  have h_eq : m = 960 + d := by omega
  rw [h_eq]
  rw [← fast_totient_eq_totient]
  rcases d with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | d_large
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · exact one_dvd _
  · decide
  · decide
  · exact one_dvd _
  · decide
  · decide
  · decide
  · decide
  · decide
  · exact one_dvd _
  · decide
  · exact one_dvd _
  · decide
  · decide
  · exact one_dvd _
  · exact one_dvd _
  · exact one_dvd _
  · exact one_dvd _
  · exact one_dvd _
  · decide
  · decide
  · decide
  · decide
  · omega

lemma totient_dvd_val_block_33 (m : ℕ) (h1 : 990 ≤ m) (h2 : m < 1020) : 3 ^ (v_list.getD m 0) ∣ totient (m + 1) := by
  have hd : m - 990 < 30 := by omega
  generalize h_d : m - 990 = d at *
  have h_eq : m = 990 + d := by omega
  rw [h_eq]
  rw [← fast_totient_eq_totient]
  rcases d with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | d_large
  · decide
  · decide
  · decide
  · decide
  · decide
  · exact one_dvd _
  · decide
  · decide
  · decide
  · exact one_dvd _
  · decide
  · exact one_dvd _
  · exact one_dvd _
  · exact one_dvd _
  · decide
  · exact one_dvd _
  · decide
  · decide
  · decide
  · exact one_dvd _
  · decide
  · exact one_dvd _
  · exact one_dvd _
  · decide
  · decide
  · decide
  · decide
  · exact one_dvd _
  · exact one_dvd _
  · exact one_dvd _
  · omega

lemma totient_dvd_val_block_34 (m : ℕ) (h1 : 1020 ≤ m) (h2 : m < 1050) : 3 ^ (v_list.getD m 0) ∣ totient (m + 1) := by
  have hd : m - 1020 < 30 := by omega
  generalize h_d : m - 1020 = d at *
  have h_eq : m = 1020 + d := by omega
  rw [h_eq]
  rw [← fast_totient_eq_totient]
  rcases d with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | d_large
  · decide
  · decide
  · decide
  · exact one_dvd _
  · exact one_dvd _
  · decide
  · decide
  · exact one_dvd _
  · decide
  · decide
  · exact one_dvd _
  · decide
  · decide
  · exact one_dvd _
  · decide
  · decide
  · decide
  · exact one_dvd _
  · decide
  · decide
  · exact one_dvd _
  · exact one_dvd _
  · decide
  · decide
  · decide
  · decide
  · decide
  · exact one_dvd _
  · exact one_dvd _
  · decide
  · omega

lemma totient_dvd_val_block_35 (m : ℕ) (h1 : 1050 ≤ m) (h2 : m < 1080) : 3 ^ (v_list.getD m 0) ∣ totient (m + 1) := by
  have hd : m - 1050 < 30 := by omega
  generalize h_d : m - 1050 = d at *
  have h_eq : m = 1050 + d := by omega
  rw [h_eq]
  rw [← fast_totient_eq_totient]
  rcases d with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | d_large
  · decide
  · exact one_dvd _
  · decide
  · decide
  · decide
  · exact one_dvd _
  · decide
  · exact one_dvd _
  · exact one_dvd _
  · exact one_dvd _
  · exact one_dvd _
  · decide
  · decide
  · decide
  · exact one_dvd _
  · decide
  · decide
  · exact one_dvd _
  · decide
  · exact one_dvd _
  · decide
  · decide
  · decide
  · exact one_dvd _
  · decide
  · exact one_dvd _
  · exact one_dvd _
  · decide
  · decide
  · decide
  · omega

lemma totient_dvd_val_block_36 (m : ℕ) (h1 : 1080 ≤ m) (h2 : m < 1110) : 3 ^ (v_list.getD m 0) ∣ totient (m + 1) := by
  have hd : m - 1080 < 30 := by omega
  generalize h_d : m - 1080 = d at *
  have h_eq : m = 1080 + d := by omega
  rw [h_eq]
  rw [← fast_totient_eq_totient]
  rcases d with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | d_large
  · exact one_dvd _
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · exact one_dvd _
  · decide
  · decide
  · exact one_dvd _
  · decide
  · decide
  · decide
  · decide
  · exact one_dvd _
  · exact one_dvd _
  · decide
  · decide
  · exact one_dvd _
  · decide
  · decide
  · exact one_dvd _
  · exact one_dvd _
  · decide
  · decide
  · decide
  · decide
  · exact one_dvd _
  · decide
  · omega

lemma totient_dvd_val_block_37 (m : ℕ) (h1 : 1110 ≤ m) (h2 : m < 1140) : 3 ^ (v_list.getD m 0) ∣ totient (m + 1) := by
  have hd : m - 1110 < 30 := by omega
  generalize h_d : m - 1110 = d at *
  have h_eq : m = 1110 + d := by omega
  rw [h_eq]
  rw [← fast_totient_eq_totient]
  rcases d with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | d_large
  · exact one_dvd _
  · decide
  · decide
  · exact one_dvd _
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · exact one_dvd _
  · decide
  · exact one_dvd _
  · decide
  · exact one_dvd _
  · decide
  · exact one_dvd _
  · decide
  · exact one_dvd _
  · decide
  · decide
  · decide
  · decide
  · exact one_dvd _
  · exact one_dvd _
  · decide
  · exact one_dvd _
  · decide
  · decide
  · omega

lemma totient_dvd_val_block_38 (m : ℕ) (h1 : 1140 ≤ m) (h2 : m < 1170) : 3 ^ (v_list.getD m 0) ∣ totient (m + 1) := by
  have hd : m - 1140 < 30 := by omega
  generalize h_d : m - 1140 = d at *
  have h_eq : m = 1140 + d := by omega
  rw [h_eq]
  rw [← fast_totient_eq_totient]
  rcases d with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | d_large
  · decide
  · decide
  · decide
  · decide
  · decide
  · exact one_dvd _
  · decide
  · decide
  · exact one_dvd _
  · exact one_dvd _
  · exact one_dvd _
  · decide
  · decide
  · decide
  · decide
  · exact one_dvd _
  · decide
  · decide
  · decide
  · exact one_dvd _
  · decide
  · decide
  · exact one_dvd _
  · decide
  · exact one_dvd _
  · exact one_dvd _
  · exact one_dvd _
  · decide
  · decide
  · decide
  · omega

lemma totient_dvd_val_block_39 (m : ℕ) (h1 : 1170 ≤ m) (h2 : m < 1200) : 3 ^ (v_list.getD m 0) ∣ totient (m + 1) := by
  have hd : m - 1170 < 30 := by omega
  generalize h_d : m - 1170 = d at *
  have h_eq : m = 1170 + d := by omega
  rw [h_eq]
  rw [← fast_totient_eq_totient]
  rcases d with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | d_large
  · decide
  · exact one_dvd _
  · exact one_dvd _
  · exact one_dvd _
  · exact one_dvd _
  · decide
  · exact one_dvd _
  · decide
  · decide
  · exact one_dvd _
  · exact one_dvd _
  · exact one_dvd _
  · decide
  · decide
  · decide
  · exact one_dvd _
  · exact one_dvd _
  · decide
  · exact one_dvd _
  · decide
  · decide
  · exact one_dvd _
  · exact one_dvd _
  · decide
  · exact one_dvd _
  · decide
  · decide
  · exact one_dvd _
  · decide
  · exact one_dvd _
  · omega

lemma totient_dvd_val_block_40 (m : ℕ) (h1 : 1200 ≤ m) (h2 : m < 1230) : 3 ^ (v_list.getD m 0) ∣ totient (m + 1) := by
  have hd : m - 1200 < 30 := by omega
  generalize h_d : m - 1200 = d at *
  have h_eq : m = 1200 + d := by omega
  rw [h_eq]
  rw [← fast_totient_eq_totient]
  rcases d with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | d_large
  · decide
  · decide
  · exact one_dvd _
  · decide
  · decide
  · decide
  · exact one_dvd _
  · decide
  · decide
  · exact one_dvd _
  · decide
  · exact one_dvd _
  · decide
  · decide
  · decide
  · decide
  · exact one_dvd _
  · decide
  · exact one_dvd _
  · decide
  · decide
  · decide
  · exact one_dvd _
  · decide
  · decide
  · decide
  · decide
  · decide
  · exact one_dvd _
  · exact one_dvd _
  · omega

lemma totient_dvd_val_block_41 (m : ℕ) (h1 : 1230 ≤ m) (h2 : m < 1260) : 3 ^ (v_list.getD m 0) ∣ totient (m + 1) := by
  have hd : m - 1230 < 30 := by omega
  generalize h_d : m - 1230 = d at *
  have h_eq : m = 1230 + d := by omega
  rw [h_eq]
  rw [← fast_totient_eq_totient]
  rcases d with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | d_large
  · decide
  · decide
  · decide
  · exact one_dvd _
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · exact one_dvd _
  · exact one_dvd _
  · exact one_dvd _
  · decide
  · decide
  · decide
  · decide
  · exact one_dvd _
  · decide
  · decide
  · decide
  · decide
  · exact one_dvd _
  · decide
  · exact one_dvd _
  · decide
  · exact one_dvd _
  · decide
  · omega

lemma totient_dvd_val_block_42 (m : ℕ) (h1 : 1260 ≤ m) (h2 : m < 1290) : 3 ^ (v_list.getD m 0) ∣ totient (m + 1) := by
  have hd : m - 1260 < 30 := by omega
  generalize h_d : m - 1260 = d at *
  have h_eq : m = 1260 + d := by omega
  rw [h_eq]
  rw [← fast_totient_eq_totient]
  rcases d with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | d_large
  · decide
  · decide
  · decide
  · decide
  · exact one_dvd _
  · decide
  · decide
  · exact one_dvd _
  · decide
  · decide
  · decide
  · exact one_dvd _
  · decide
  · decide
  · decide
  · decide
  · exact one_dvd _
  · decide
  · exact one_dvd _
  · decide
  · exact one_dvd _
  · decide
  · exact one_dvd _
  · decide
  · exact one_dvd _
  · exact one_dvd _
  · decide
  · exact one_dvd _
  · decide
  · decide
  · omega

lemma totient_dvd_val_block_43 (m : ℕ) (h1 : 1290 ≤ m) (h2 : m < 1320) : 3 ^ (v_list.getD m 0) ∣ totient (m + 1) := by
  have hd : m - 1290 < 30 := by omega
  generalize h_d : m - 1290 = d at *
  have h_eq : m = 1290 + d := by omega
  rw [h_eq]
  rw [← fast_totient_eq_totient]
  rcases d with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | d_large
  · decide
  · decide
  · decide
  · exact one_dvd _
  · exact one_dvd _
  · decide
  · decide
  · exact one_dvd _
  · decide
  · exact one_dvd _
  · exact one_dvd _
  · decide
  · decide
  · exact one_dvd _
  · decide
  · exact one_dvd _
  · decide
  · decide
  · decide
  · decide
  · decide
  · exact one_dvd _
  · exact one_dvd _
  · exact one_dvd _
  · decide
  · decide
  · decide
  · exact one_dvd _
  · decide
  · decide
  · omega

lemma totient_dvd_val_block_44 (m : ℕ) (h1 : 1320 ≤ m) (h2 : m < 1350) : 3 ^ (v_list.getD m 0) ∣ totient (m + 1) := by
  have hd : m - 1320 < 30 := by omega
  generalize h_d : m - 1320 = d at *
  have h_eq : m = 1320 + d := by omega
  rw [h_eq]
  rw [← fast_totient_eq_totient]
  rcases d with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | d_large
  · decide
  · decide
  · decide
  · decide
  · exact one_dvd _
  · exact one_dvd _
  · exact one_dvd _
  · decide
  · decide
  · decide
  · decide
  · exact one_dvd _
  · decide
  · exact one_dvd _
  · exact one_dvd _
  · exact one_dvd _
  · exact one_dvd _
  · decide
  · exact one_dvd _
  · exact one_dvd _
  · decide
  · decide
  · exact one_dvd _
  · exact one_dvd _
  · decide
  · exact one_dvd _
  · decide
  · exact one_dvd _
  · decide
  · decide
  · omega

lemma totient_dvd_val_block_45 (m : ℕ) (h1 : 1350 ≤ m) (h2 : m < 1380) : 3 ^ (v_list.getD m 0) ∣ totient (m + 1) := by
  have hd : m - 1350 < 30 := by omega
  generalize h_d : m - 1350 = d at *
  have h_eq : m = 1350 + d := by omega
  rw [h_eq]
  rw [← fast_totient_eq_totient]
  rcases d with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | d_large
  · exact one_dvd _
  · decide
  · exact one_dvd _
  · decide
  · exact one_dvd _
  · decide
  · decide
  · exact one_dvd _
  · decide
  · exact one_dvd _
  · decide
  · exact one_dvd _
  · exact one_dvd _
  · exact one_dvd _
  · decide
  · decide
  · decide
  · exact one_dvd _
  · exact one_dvd _
  · decide
  · exact one_dvd _
  · exact one_dvd _
  · decide
  · decide
  · decide
  · decide
  · decide
  · exact one_dvd _
  · decide
  · decide
  · omega

lemma totient_dvd_val_block_46 (m : ℕ) (h1 : 1380 ≤ m) (h2 : m < 1410) : 3 ^ (v_list.getD m 0) ∣ totient (m + 1) := by
  have hd : m - 1380 < 30 := by omega
  generalize h_d : m - 1380 = d at *
  have h_eq : m = 1380 + d := by omega
  rw [h_eq]
  rw [← fast_totient_eq_totient]
  rcases d with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | d_large
  · decide
  · exact one_dvd _
  · decide
  · exact one_dvd _
  · decide
  · exact one_dvd _
  · decide
  · decide
  · decide
  · decide
  · exact one_dvd _
  · decide
  · decide
  · decide
  · exact one_dvd _
  · exact one_dvd _
  · exact one_dvd _
  · exact one_dvd _
  · exact one_dvd _
  · decide
  · decide
  · exact one_dvd _
  · exact one_dvd _
  · decide
  · decide
  · decide
  · exact one_dvd _
  · decide
  · exact one_dvd _
  · decide
  · omega

lemma totient_dvd_val_block_47 (m : ℕ) (h1 : 1410 ≤ m) (h2 : m < 1440) : 3 ^ (v_list.getD m 0) ∣ totient (m + 1) := by
  have hd : m - 1410 < 30 := by omega
  generalize h_d : m - 1410 = d at *
  have h_eq : m = 1410 + d := by omega
  rw [h_eq]
  rw [← fast_totient_eq_totient]
  rcases d with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | d_large
  · decide
  · exact one_dvd _
  · decide
  · exact one_dvd _
  · decide
  · decide
  · exact one_dvd _
  · decide
  · decide
  · exact one_dvd _
  · exact one_dvd _
  · decide
  · decide
  · exact one_dvd _
  · exact one_dvd _
  · decide
  · exact one_dvd _
  · decide
  · decide
  · exact one_dvd _
  · decide
  · decide
  · exact one_dvd _
  · exact one_dvd _
  · decide
  · decide
  · decide
  · decide
  · exact one_dvd _
  · exact one_dvd _
  · omega

lemma totient_dvd_val_block_48 (m : ℕ) (h1 : 1440 ≤ m) (h2 : m < 1470) : 3 ^ (v_list.getD m 0) ∣ totient (m + 1) := by
  have hd : m - 1440 < 30 := by omega
  generalize h_d : m - 1440 = d at *
  have h_eq : m = 1440 + d := by omega
  rw [h_eq]
  rw [← fast_totient_eq_totient]
  rcases d with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | d_large
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · exact one_dvd _
  · decide
  · exact one_dvd _
  · decide
  · decide
  · decide
  · decide
  · exact one_dvd _
  · decide
  · decide
  · exact one_dvd _
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · exact one_dvd _
  · decide
  · exact one_dvd _
  · omega

lemma totient_dvd_val_block_49 (m : ℕ) (h1 : 1470 ≤ m) (h2 : m < 1500) : 3 ^ (v_list.getD m 0) ∣ totient (m + 1) := by
  have hd : m - 1470 < 30 := by omega
  generalize h_d : m - 1470 = d at *
  have h_eq : m = 1470 + d := by omega
  rw [h_eq]
  rw [← fast_totient_eq_totient]
  rcases d with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | d_large
  · decide
  · exact one_dvd _
  · decide
  · exact one_dvd _
  · exact one_dvd _
  · exact one_dvd _
  · decide
  · decide
  · decide
  · decide
  · exact one_dvd _
  · decide
  · exact one_dvd _
  · decide
  · decide
  · decide
  · exact one_dvd _
  · decide
  · exact one_dvd _
  · exact one_dvd _
  · decide
  · decide
  · exact one_dvd _
  · exact one_dvd _
  · decide
  · decide
  · decide
  · exact one_dvd _
  · decide
  · decide
  · omega

lemma totient_dvd_val_block_50 (m : ℕ) (h1 : 1500 ≤ m) (h2 : m < 1530) : 3 ^ (v_list.getD m 0) ∣ totient (m + 1) := by
  have hd : m - 1500 < 30 := by omega
  generalize h_d : m - 1500 = d at *
  have h_eq : m = 1500 + d := by omega
  rw [h_eq]
  rw [← fast_totient_eq_totient]
  rcases d with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | d_large
  · exact one_dvd _
  · exact one_dvd _
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · exact one_dvd _
  · exact one_dvd _
  · decide
  · exact one_dvd _
  · exact one_dvd _
  · decide
  · exact one_dvd _
  · decide
  · exact one_dvd _
  · decide
  · decide
  · decide
  · decide
  · exact one_dvd _
  · decide
  · exact one_dvd _
  · decide
  · exact one_dvd _
  · decide
  · exact one_dvd _
  · omega

lemma totient_dvd_val_block_51 (m : ℕ) (h1 : 1530 ≤ m) (h2 : m < 1560) : 3 ^ (v_list.getD m 0) ∣ totient (m + 1) := by
  have hd : m - 1530 < 30 := by omega
  generalize h_d : m - 1530 = d at *
  have h_eq : m = 1530 + d := by omega
  rw [h_eq]
  rw [← fast_totient_eq_totient]
  rcases d with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | d_large
  · exact one_dvd _
  · decide
  · exact one_dvd _
  · decide
  · exact one_dvd _
  · decide
  · decide
  · exact one_dvd _
  · exact one_dvd _
  · exact one_dvd _
  · decide
  · exact one_dvd _
  · decide
  · exact one_dvd _
  · decide
  · exact one_dvd _
  · decide
  · decide
  · decide
  · exact one_dvd _
  · exact one_dvd _
  · exact one_dvd _
  · exact one_dvd _
  · decide
  · decide
  · decide
  · decide
  · decide
  · exact one_dvd _
  · exact one_dvd _
  · omega

lemma totient_dvd_val_block_52 (m : ℕ) (h1 : 1560 ≤ m) (h2 : m < 1590) : 3 ^ (v_list.getD m 0) ∣ totient (m + 1) := by
  have hd : m - 1560 < 30 := by omega
  generalize h_d : m - 1560 = d at *
  have h_eq : m = 1560 + d := by omega
  rw [h_eq]
  rw [← fast_totient_eq_totient]
  rcases d with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | d_large
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · exact one_dvd _
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · exact one_dvd _
  · decide
  · exact one_dvd _
  · decide
  · decide
  · exact one_dvd _
  · decide
  · exact one_dvd _
  · decide
  · exact one_dvd _
  · exact one_dvd _
  · decide
  · decide
  · decide
  · omega

lemma totient_dvd_val_block_53 (m : ℕ) (h1 : 1590 ≤ m) (h2 : m < 1620) : 3 ^ (v_list.getD m 0) ∣ totient (m + 1) := by
  have hd : m - 1590 < 30 := by omega
  generalize h_d : m - 1590 = d at *
  have h_eq : m = 1590 + d := by omega
  rw [h_eq]
  rw [← fast_totient_eq_totient]
  rcases d with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | d_large
  · decide
  · decide
  · exact one_dvd _
  · decide
  · exact one_dvd _
  · decide
  · decide
  · exact one_dvd _
  · decide
  · exact one_dvd _
  · decide
  · exact one_dvd _
  · decide
  · decide
  · exact one_dvd _
  · decide
  · exact one_dvd _
  · decide
  · decide
  · decide
  · decide
  · exact one_dvd _
  · decide
  · decide
  · exact one_dvd _
  · exact one_dvd _
  · decide
  · decide
  · decide
  · exact one_dvd _
  · omega

lemma totient_dvd_val_block_54 (m : ℕ) (h1 : 1620 ≤ m) (h2 : m < 1650) : 3 ^ (v_list.getD m 0) ∣ totient (m + 1) := by
  have hd : m - 1620 < 30 := by omega
  generalize h_d : m - 1620 = d at *
  have h_eq : m = 1620 + d := by omega
  rw [h_eq]
  rw [← fast_totient_eq_totient]
  rcases d with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | d_large
  · decide
  · exact one_dvd _
  · exact one_dvd _
  · decide
  · decide
  · decide
  · decide
  · decide
  · exact one_dvd _
  · decide
  · exact one_dvd _
  · decide
  · exact one_dvd _
  · exact one_dvd _
  · decide
  · exact one_dvd _
  · decide
  · decide
  · decide
  · decide
  · exact one_dvd _
  · exact one_dvd _
  · exact one_dvd _
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · exact one_dvd _
  · omega

lemma totient_dvd_val_block_55 (m : ℕ) (h1 : 1650 ≤ m) (h2 : m < 1680) : 3 ^ (v_list.getD m 0) ∣ totient (m + 1) := by
  have hd : m - 1650 < 30 := by omega
  generalize h_d : m - 1650 = d at *
  have h_eq : m = 1650 + d := by omega
  rw [h_eq]
  rw [← fast_totient_eq_totient]
  rcases d with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | d_large
  · decide
  · decide
  · decide
  · exact one_dvd _
  · exact one_dvd _
  · exact one_dvd _
  · decide
  · decide
  · exact one_dvd _
  · decide
  · exact one_dvd _
  · decide
  · decide
  · exact one_dvd _
  · decide
  · decide
  · decide
  · decide
  · exact one_dvd _
  · decide
  · decide
  · exact one_dvd _
  · exact one_dvd _
  · decide
  · exact one_dvd _
  · decide
  · exact one_dvd _
  · decide
  · decide
  · decide
  · omega

lemma totient_dvd_val_block_56 (m : ℕ) (h1 : 1680 ≤ m) (h2 : m < 1710) : 3 ^ (v_list.getD m 0) ∣ totient (m + 1) := by
  have hd : m - 1680 < 30 := by omega
  generalize h_d : m - 1680 = d at *
  have h_eq : m = 1680 + d := by omega
  rw [h_eq]
  rw [← fast_totient_eq_totient]
  rcases d with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | d_large
  · decide
  · exact one_dvd _
  · decide
  · exact one_dvd _
  · decide
  · exact one_dvd _
  · decide
  · decide
  · decide
  · exact one_dvd _
  · exact one_dvd _
  · decide
  · decide
  · decide
  · decide
  · exact one_dvd _
  · exact one_dvd _
  · decide
  · exact one_dvd _
  · decide
  · exact one_dvd _
  · decide
  · decide
  · exact one_dvd _
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · omega

lemma totient_dvd_val_block_57 (m : ℕ) (h1 : 1710 ≤ m) (h2 : m < 1740) : 3 ^ (v_list.getD m 0) ∣ totient (m + 1) := by
  have hd : m - 1710 < 30 := by omega
  generalize h_d : m - 1710 = d at *
  have h_eq : m = 1710 + d := by omega
  rw [h_eq]
  rw [← fast_totient_eq_totient]
  rcases d with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | d_large
  · decide
  · decide
  · exact one_dvd _
  · exact one_dvd _
  · exact one_dvd _
  · decide
  · decide
  · decide
  · exact one_dvd _
  · exact one_dvd _
  · exact one_dvd _
  · decide
  · decide
  · exact one_dvd _
  · decide
  · decide
  · decide
  · exact one_dvd _
  · exact one_dvd _
  · decide
  · decide
  · exact one_dvd _
  · decide
  · decide
  · exact one_dvd _
  · exact one_dvd _
  · decide
  · exact one_dvd _
  · decide
  · decide
  · omega

lemma totient_dvd_val_block_58 (m : ℕ) (h1 : 1740 ≤ m) (h2 : m < 1770) : 3 ^ (v_list.getD m 0) ∣ totient (m + 1) := by
  have hd : m - 1740 < 30 := by omega
  generalize h_d : m - 1740 = d at *
  have h_eq : m = 1740 + d := by omega
  rw [h_eq]
  rw [← fast_totient_eq_totient]
  rcases d with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | d_large
  · decide
  · exact one_dvd _
  · decide
  · decide
  · exact one_dvd _
  · decide
  · exact one_dvd _
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · exact one_dvd _
  · decide
  · exact one_dvd _
  · decide
  · decide
  · decide
  · decide
  · decide
  · exact one_dvd _
  · exact one_dvd _
  · decide
  · decide
  · exact one_dvd _
  · exact one_dvd _
  · exact one_dvd _
  · exact one_dvd _
  · decide
  · omega

lemma totient_dvd_val_block_59 (m : ℕ) (h1 : 1770 ≤ m) (h2 : m < 1800) : 3 ^ (v_list.getD m 0) ∣ totient (m + 1) := by
  have hd : m - 1770 < 30 := by omega
  generalize h_d : m - 1770 = d at *
  have h_eq : m = 1770 + d := by omega
  rw [h_eq]
  rw [← fast_totient_eq_totient]
  rcases d with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | d_large
  · decide
  · decide
  · decide
  · exact one_dvd _
  · exact one_dvd _
  · decide
  · exact one_dvd _
  · exact one_dvd _
  · decide
  · decide
  · exact one_dvd _
  · decide
  · decide
  · decide
  · exact one_dvd _
  · decide
  · exact one_dvd _
  · decide
  · exact one_dvd _
  · exact one_dvd _
  · exact one_dvd _
  · exact one_dvd _
  · decide
  · exact one_dvd _
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · omega

lemma totient_dvd_val_block_60 (m : ℕ) (h1 : 1800 ≤ m) (h2 : m < 1807) : 3 ^ (v_list.getD m 0) ∣ totient (m + 1) := by
  have hd : m - 1800 < 7 := by omega
  generalize h_d : m - 1800 = d at *
  have h_eq : m = 1800 + d := by omega
  rw [h_eq]
  rw [← fast_totient_eq_totient]
  rcases d with _ | _ | _ | _ | _ | _ | _ | d_large
  · decide
  · exact one_dvd _
  · decide
  · decide
  · exact one_dvd _
  · decide
  · decide
  · omega

lemma totient_dvd_val (m : ℕ) (hm : m < 1807) : 3 ^ (v_list.getD m 0) ∣ totient (m + 1) := by
  have h_cases : m < 30 ∨ (30 ≤ m ∧ m < 60) ∨ (60 ≤ m ∧ m < 90) ∨ (90 ≤ m ∧ m < 120) ∨ (120 ≤ m ∧ m < 150) ∨ (150 ≤ m ∧ m < 180) ∨ (180 ≤ m ∧ m < 210) ∨ (210 ≤ m ∧ m < 240) ∨ (240 ≤ m ∧ m < 270) ∨ (270 ≤ m ∧ m < 300) ∨ (300 ≤ m ∧ m < 330) ∨ (330 ≤ m ∧ m < 360) ∨ (360 ≤ m ∧ m < 390) ∨ (390 ≤ m ∧ m < 420) ∨ (420 ≤ m ∧ m < 450) ∨ (450 ≤ m ∧ m < 480) ∨ (480 ≤ m ∧ m < 510) ∨ (510 ≤ m ∧ m < 540) ∨ (540 ≤ m ∧ m < 570) ∨ (570 ≤ m ∧ m < 600) ∨ (600 ≤ m ∧ m < 630) ∨ (630 ≤ m ∧ m < 660) ∨ (660 ≤ m ∧ m < 690) ∨ (690 ≤ m ∧ m < 720) ∨ (720 ≤ m ∧ m < 750) ∨ (750 ≤ m ∧ m < 780) ∨ (780 ≤ m ∧ m < 810) ∨ (810 ≤ m ∧ m < 840) ∨ (840 ≤ m ∧ m < 870) ∨ (870 ≤ m ∧ m < 900) ∨ (900 ≤ m ∧ m < 930) ∨ (930 ≤ m ∧ m < 960) ∨ (960 ≤ m ∧ m < 990) ∨ (990 ≤ m ∧ m < 1020) ∨ (1020 ≤ m ∧ m < 1050) ∨ (1050 ≤ m ∧ m < 1080) ∨ (1080 ≤ m ∧ m < 1110) ∨ (1110 ≤ m ∧ m < 1140) ∨ (1140 ≤ m ∧ m < 1170) ∨ (1170 ≤ m ∧ m < 1200) ∨ (1200 ≤ m ∧ m < 1230) ∨ (1230 ≤ m ∧ m < 1260) ∨ (1260 ≤ m ∧ m < 1290) ∨ (1290 ≤ m ∧ m < 1320) ∨ (1320 ≤ m ∧ m < 1350) ∨ (1350 ≤ m ∧ m < 1380) ∨ (1380 ≤ m ∧ m < 1410) ∨ (1410 ≤ m ∧ m < 1440) ∨ (1440 ≤ m ∧ m < 1470) ∨ (1470 ≤ m ∧ m < 1500) ∨ (1500 ≤ m ∧ m < 1530) ∨ (1530 ≤ m ∧ m < 1560) ∨ (1560 ≤ m ∧ m < 1590) ∨ (1590 ≤ m ∧ m < 1620) ∨ (1620 ≤ m ∧ m < 1650) ∨ (1650 ≤ m ∧ m < 1680) ∨ (1680 ≤ m ∧ m < 1710) ∨ (1710 ≤ m ∧ m < 1740) ∨ (1740 ≤ m ∧ m < 1770) ∨ (1770 ≤ m ∧ m < 1800) ∨ (1800 ≤ m ∧ m < 1807) := by omega
  rcases h_cases with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · exact totient_dvd_val_block_0 m (by omega) h
  · exact totient_dvd_val_block_1 m h.left h.right
  · exact totient_dvd_val_block_2 m h.left h.right
  · exact totient_dvd_val_block_3 m h.left h.right
  · exact totient_dvd_val_block_4 m h.left h.right
  · exact totient_dvd_val_block_5 m h.left h.right
  · exact totient_dvd_val_block_6 m h.left h.right
  · exact totient_dvd_val_block_7 m h.left h.right
  · exact totient_dvd_val_block_8 m h.left h.right
  · exact totient_dvd_val_block_9 m h.left h.right
  · exact totient_dvd_val_block_10 m h.left h.right
  · exact totient_dvd_val_block_11 m h.left h.right
  · exact totient_dvd_val_block_12 m h.left h.right
  · exact totient_dvd_val_block_13 m h.left h.right
  · exact totient_dvd_val_block_14 m h.left h.right
  · exact totient_dvd_val_block_15 m h.left h.right
  · exact totient_dvd_val_block_16 m h.left h.right
  · exact totient_dvd_val_block_17 m h.left h.right
  · exact totient_dvd_val_block_18 m h.left h.right
  · exact totient_dvd_val_block_19 m h.left h.right
  · exact totient_dvd_val_block_20 m h.left h.right
  · exact totient_dvd_val_block_21 m h.left h.right
  · exact totient_dvd_val_block_22 m h.left h.right
  · exact totient_dvd_val_block_23 m h.left h.right
  · exact totient_dvd_val_block_24 m h.left h.right
  · exact totient_dvd_val_block_25 m h.left h.right
  · exact totient_dvd_val_block_26 m h.left h.right
  · exact totient_dvd_val_block_27 m h.left h.right
  · exact totient_dvd_val_block_28 m h.left h.right
  · exact totient_dvd_val_block_29 m h.left h.right
  · exact totient_dvd_val_block_30 m h.left h.right
  · exact totient_dvd_val_block_31 m h.left h.right
  · exact totient_dvd_val_block_32 m h.left h.right
  · exact totient_dvd_val_block_33 m h.left h.right
  · exact totient_dvd_val_block_34 m h.left h.right
  · exact totient_dvd_val_block_35 m h.left h.right
  · exact totient_dvd_val_block_36 m h.left h.right
  · exact totient_dvd_val_block_37 m h.left h.right
  · exact totient_dvd_val_block_38 m h.left h.right
  · exact totient_dvd_val_block_39 m h.left h.right
  · exact totient_dvd_val_block_40 m h.left h.right
  · exact totient_dvd_val_block_41 m h.left h.right
  · exact totient_dvd_val_block_42 m h.left h.right
  · exact totient_dvd_val_block_43 m h.left h.right
  · exact totient_dvd_val_block_44 m h.left h.right
  · exact totient_dvd_val_block_45 m h.left h.right
  · exact totient_dvd_val_block_46 m h.left h.right
  · exact totient_dvd_val_block_47 m h.left h.right
  · exact totient_dvd_val_block_48 m h.left h.right
  · exact totient_dvd_val_block_49 m h.left h.right
  · exact totient_dvd_val_block_50 m h.left h.right
  · exact totient_dvd_val_block_51 m h.left h.right
  · exact totient_dvd_val_block_52 m h.left h.right
  · exact totient_dvd_val_block_53 m h.left h.right
  · exact totient_dvd_val_block_54 m h.left h.right
  · exact totient_dvd_val_block_55 m h.left h.right
  · exact totient_dvd_val_block_56 m h.left h.right
  · exact totient_dvd_val_block_57 m h.left h.right
  · exact totient_dvd_val_block_58 m h.left h.right
  · exact totient_dvd_val_block_59 m h.left h.right
  · exact totient_dvd_val_block_60 m h.left h.right
lemma pow_two_mul_padic_dvd (x : ℕ) : 3 ^ (2 * padicValNat 3 x) ∣ x ^ 2 := by
  have h := pow_padicValNat_dvd (p := 3) (n := x)
  have h2 := mul_dvd_mul h h
  rw [← sq, ← sq] at h2
  have h_pow : (3 ^ padicValNat 3 x) ^ 2 = 3 ^ (2 * padicValNat 3 x) := by
    rw [pow_mul']
  rw [h_pow] at h2
  exact h2

lemma den_val_pos (n : ℕ) : den_val n > 0 := by
  induction n with
  | zero => simp [den_val]
  | succ m ih =>
    dsimp [den_val]
    have : totient (m + 1) > 0 := totient_pos.mpr (by omega)
    positivity

lemma num_val_pos (n : ℕ) : num_val n > 0 := by
  induction n with
  | zero => simp [num_val]
  | succ m ih =>
    dsimp [num_val]
    positivity

lemma den_val_dvd (n : ℕ) (hn : n ≤ 1807) : 3 ^ (sum_v n) ∣ den_val n := by
  induction n with
  | zero => simp [sum_v, den_val]
  | succ m ih =>
    have hm : m ≤ 1807 := by omega
    have hm2 : m < 1807 := by omega
    have ih_m := ih (by omega)
    dsimp [den_val]
    have h_tot := totient_dvd_val m hm2
    have h_mul := mul_dvd_mul ih_m h_tot
    have h_pow : 3 ^ sum_v (m + 1) = 3 ^ sum_v m * 3 ^ (v_list.getD m 0) := by
      dsimp [sum_v]
      exact pow_add 3 (sum_v m) (v_list.getD m 0)
    rw [h_pow]
    exact h_mul

lemma num_val_dvd (n : ℕ) (hn : n ≤ 1807) : 3 ^ (sum_u n) ∣ num_val n := by
  induction n with
  | zero => simp [sum_u, num_val]
  | succ m ih =>
    have hm : m ≤ 1807 := by omega
    have hm2 : m < 1807 := by omega
    have ih_m := ih (by omega)
    dsimp [num_val]
    have h_sq := pow_two_mul_padic_dvd (m + 1)
    have h_mul := mul_dvd_mul ih_m h_sq
    have h_pow : 3 ^ (sum_u m + 2 * padicValNat 3 (m + 1)) = 3 ^ sum_u m * 3 ^ (2 * padicValNat 3 (m + 1)) := pow_add 3 _ _
    rw [h_pow]
    exact h_mul

lemma padic_val_num_val (n : ℕ) (hn : n ≤ 1807) : padicValNat 3 (num_val n) = sum_u n := by
  induction n with
  | zero =>
    dsimp [num_val, sum_u]
    exact padicValNat.one
  | succ m ih =>
    have hm : m ≤ 1807 := by omega
    have hm2 : m < 1807 := by omega
    dsimp [num_val, sum_u]
    have h_pos_A : num_val m ≠ 0 := (num_val_pos m).ne'
    have h_pos_B : (m + 1) ^ 2 ≠ 0 := by positivity
    rw [padicValNat.mul h_pos_A h_pos_B]
    rw [ih (by omega)]
    have h_val_sq : padicValNat 3 ((m + 1) ^ 2) = 2 * padicValNat 3 (m + 1) := by
      haveI : Fact (Nat.Prime 3) := ⟨by decide⟩
      exact padicValNat.pow 2 (by positivity)
    rw [h_val_sq]

lemma A060841_val_rat_eq_num_div_den (n : ℕ) :
  A060841_val_rat n = (num_val n : ℚ) / (den_val n : ℚ) := by
  induction n with
  | zero =>
    dsimp [A060841_val_rat, num_val, den_val]
    have h1 : Icc 1 0 = ∅ := rfl
    rw [h1, prod_empty]
    norm_num
  | succ m ih =>
    have h_le : 1 ≤ succ m := Nat.succ_pos m
    have h_insert : insert (succ m) (Icc 1 m) = Icc 1 (succ m) := insert_Icc_right_eq_Icc_succ h_le
    have h_not_mem : succ m ∉ Icc 1 m := by simp
    dsimp [A060841_val_rat]
    rw [← h_insert, prod_insert h_not_mem]
    have h_fold : (∏ x ∈ Icc 1 m, (x : ℚ) ^ 2 / (totient x : ℚ)) = A060841_val_rat m := rfl
    rw [h_fold, ih]
    dsimp [num_val, den_val]
    push_cast
    ring

lemma dvd_den_of_not_dvd {x : ℚ} {P Q : ℤ} (h : x = (P : ℚ) / (3 * Q : ℚ)) (h3 : ¬ 3 ∣ P) (hQ : Q ≠ 0) : 3 ∣ (x.den : ℤ) := by
  have hx : (x : ℚ) = (x.num : ℚ) / (x.den : ℚ) := by exact x.num_div_den.symm
  have h_eq : (x.num : ℚ) / (x.den : ℚ) = (P : ℚ) / (3 * Q : ℚ) := by
    rw [← hx]
    exact h
  have h_den_ne : (x.den : ℚ) ≠ 0 := by exact_mod_cast x.den_nz
  have h_3Q_ne : (3 * Q : ℚ) ≠ 0 := by
    intro hc
    have : 3 * Q = 0 := by exact_mod_cast hc
    omega
  have h_cross := (div_eq_div_iff h_den_ne h_3Q_ne).mp h_eq
  have h_cross_z : (x.num : ℤ) * (3 * Q) = P * x.den := by
    exact_mod_cast h_cross
  have h_cross_z_mul : (x.num : ℤ) * (3 * Q) = 3 * (x.num * Q) := by ring
  have h_cross_z_rewrite : P * x.den = (x.num : ℤ) * (3 * Q) := h_cross_z.symm
  have h_dvd : 3 ∣ P * (x.den : ℤ) := by
    rw [h_cross_z_rewrite, h_cross_z_mul]
    use x.num * Q
  have h_prime : Prime (3 : ℤ) := by
    norm_num
  exact (Prime.dvd_mul h_prime).mp h_dvd |>.elim (fun hP => False.elim (h3 hP)) id

lemma num_val_not_dvd_1807 : ¬ 3 ^ 1799 ∣ num_val 1807 := by
  haveI : Fact (Nat.Prime 3) := ⟨by decide⟩
  have h_not := pow_succ_padicValNat_not_dvd (n := num_val 1807) (num_val_pos 1807).ne'
  have h_val : padicValNat 3 (num_val 1807) = 1798 := padic_val_num_val 1807 (by omega)
  have h_eval : 1798 + 1 = 1799 := rfl
  rw [h_val, h_eval] at h_not
  exact h_not

lemma not_isPowerOfTwo_of_dvd_three {n : ℕ} (h : 3 ∣ n) : ¬ n.isPowerOfTwo := by
  rintro ⟨k, rfl⟩
  have h3 : Nat.Prime 3 := by decide
  have hdvd : 3 ∣ 2 := h3.dvd_of_dvd_pow h
  norm_num at hdvd

lemma spec_1807_den_dvd_three : 3 ∣ ((A060841_val_rat 1807).den : ℤ) := by
  have h_rat : A060841_val_rat 1807 = ((num_val 1807 / 3 ^ 1798 : ℕ) : ℚ) / (3 * ((den_val 1807 / 3 ^ 1799 : ℕ) : ℚ)) := by
    rw [A060841_val_rat_eq_num_div_den 1807]
    have h_num_dvd : 3 ^ 1798 ∣ num_val 1807 := num_val_dvd 1807 (by omega)
    have h_den_dvd : 3 ^ 1799 ∣ den_val 1807 := den_val_dvd 1807 (by omega)
    have h_num : (num_val 1807 : ℚ) = (3 ^ 1798 * (num_val 1807 / 3 ^ 1798) : ℚ) := by
      push_cast
      congr 1
      exact (Nat.mul_div_cancel' h_num_dvd).symm
    have h_den : (den_val 1807 : ℚ) = (3 ^ 1799 * (den_val 1807 / 3 ^ 1799) : ℚ) := by
      push_cast
      congr 1
      exact (Nat.mul_div_cancel' h_den_dvd).symm
    rw [h_num, h_den]
    have h_pow3 : (3 : ℚ) ^ 1799 = (3 : ℚ) ^ 1798 * 3 := by
      have : (3 : ℚ) ^ 1799 = (3 : ℚ) ^ (1798 + 1) := rfl
      rw [this, pow_add]
      ring
    have h_assoc : (3 : ℚ) ^ 1798 * 3 * ((den_val 1807 / 3 ^ 1799 : ℕ) : ℚ) = (3 : ℚ) ^ 1798 * (3 * ((den_val 1807 / 3 ^ 1799 : ℕ) : ℚ)) := by ring
    rw [h_assoc]
    exact mul_div_mul_left _ _ (by positivity)
  have h3 : ¬ 3 ∣ ((num_val 1807 / 3 ^ 1798 : ℕ) : ℤ) := by
    intro h_dvd
    have h_dvd_nat : 3 ∣ num_val 1807 / 3 ^ 1798 := by exact_mod_cast h_dvd
    have h_dvd_all : 3 ^ 1799 ∣ num_val 1807 := by
      have h_num_dvd : 3 ^ 1798 ∣ num_val 1807 := num_val_dvd 1807 (by omega)
      have h_eq : num_val 1807 = 3 ^ 1798 * (num_val 1807 / 3 ^ 1798) := (Nat.mul_div_cancel' h_num_dvd).symm
      rw [h_eq]
      obtain ⟨k, rfl⟩ := h_dvd_nat
      use k
      ring
    have h_not_dvd := num_val_not_dvd_1807
    exact h_not_dvd h_dvd_all
  have hQ : ((den_val 1807 / 3 ^ 1799 : ℕ) : ℤ) ≠ 0 := by
    have h_pos : den_val 1807 > 0 := den_val_pos 1807
    intro hc
    have h_zero : den_val 1807 / 3 ^ 1799 = 0 := by exact_mod_cast hc
    have h_lt : den_val 1807 < 3 ^ 1799 := Nat.div_eq_zero_iff.mp h_zero |>.elim (by omega) id
    have h_den_dvd : 3 ^ 1799 ∣ den_val 1807 := den_val_dvd 1807 (by omega)
    have h_le := Nat.le_of_dvd h_pos h_den_dvd
    omega
  exact dvd_den_of_not_dvd h_rat h3 hQ

theorem oeis_60841_conjecture_0.disproof :
  ¬ (∀ (n : ℕ) (hn : 1 ≤ n),
    (A060841_val_rat n).den.isPowerOfTwo ∧
    ((A060841_val_rat n).isInt ↔ n ∈ Icc 1 34 ∨ n = 36 ∨ n = 38)) := by
  intro h
  have h_1807 := h 1807 (by omega)
  have h_pow := h_1807.left
  have h_dvd := spec_1807_den_dvd_three
  have h_not_pow := not_isPowerOfTwo_of_dvd_three (by exact_mod_cast h_dvd)
  exact h_not_pow h_pow
