import Mathlib

open Nat

lemma mod_add_P (m M P y i : ℕ) (hP : ∀ x ≥ M, 10^(x + P) ≡ 10^x [MOD m]) (hy : y ≥ M) :
    10^(y + i * P) ≡ 10^y [MOD m] := by
  induction i with
  | zero =>
    have : y + 0 * P = y := by omega
    rw [this]
  | succ i ih =>
    rw [succ_mul, ← add_assoc]
    have h1 : 10^(y + i * P + P) ≡ 10^(y + i * P) [MOD m] := hP _ (by omega)
    exact Nat.ModEq.trans h1 ih

lemma sum_partnerList_mod_gen (m M P : ℕ) (start : ℕ) (L : List ℕ) (hP : ∀ x ≥ M, 10^(x + P) ≡ 10^x [MOD m])
    (hL : ∀ y ∈ L, y ≥ M) :
    (List.map (fun x => 10^x) ((List.range' start L.length).zip L |>.map (fun ⟨i, y⟩ => y + i * P))).sum ≡
    (List.map (fun x => 10^x) L).sum [MOD m] := by
  induction L generalizing start with
  | nil =>
    simp
    exact Nat.ModEq.refl 0
  | cons hd tl ih =>
    simp only [List.length_cons, List.range'_succ, List.zip_cons_cons, List.map_cons, List.sum_cons]
    apply Nat.ModEq.add
    · exact mod_add_P m M P hd start hP (hL hd (List.Mem.head _))
    · exact ih (start + 1) (fun y hy => hL y (List.Mem.tail _ hy))

lemma sum_partnerList_mod (m M P : ℕ) (L : List ℕ) (hP : ∀ x ≥ M, 10^(x + P) ≡ 10^x [MOD m])
    (hL : ∀ y ∈ L, y ≥ M) :
    (List.map (fun x => 10^x) ((List.range L.length).zip L |>.map (fun ⟨i, y⟩ => y + i * P))).sum ≡
    (List.map (fun x => 10^x) L).sum [MOD m] := by
  have H : List.range L.length = List.range' 0 L.length := by simp [List.range_eq_range']
  rw [H]
  exact sum_partnerList_mod_gen m M P 0 L hP hL

