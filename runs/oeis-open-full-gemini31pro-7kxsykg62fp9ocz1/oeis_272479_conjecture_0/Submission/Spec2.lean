import FormalConjectures.Util.ProblemImports
open Nat
open Classical
open Finset

/--
A272479: $a(n)$ is the smallest $k$ different from $n$ such that $(n, k)$ is a Harshad amicable pair.
Let $D(n)$ be the sum of digits of $n$.
$m$ and $k$ are Harshad amicable if they are distinct integers such that $D(m) \mid k$ and $D(k) \mid m$.
For any $n$ with no Harshad amicable partner, $a(n)=0$ (Conjecture: the sequence contains no zeros.)
-/
noncomputable def a (n : ℕ) : ℕ :=
  let dsum (m : ℕ) : ℕ := (digits 10 m).sum
  let partners : Set ℕ := {k | k > 0 ∧ k ≠ n ∧ dsum n ∣ k ∧ dsum k ∣ n}
  if h : partners.Nonempty then sInf partners else 0

lemma n_lt_ten_pow (n : ℕ) : n < 10 ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    calc n + 1 ≤ 10 ^ n + 1 := Nat.add_le_add_right (le_of_lt ih) 1
      _ < 10 ^ n + 10 ^ n * 9 := by
        apply Nat.add_lt_add_left
        have : 1 ≤ 10 ^ n := Nat.one_le_pow _ _ (by decide)
        nlinarith
      _ = 10 ^ n * 1 + 10 ^ n * 9 := by ring
      _ = 10 ^ n * 10 := by ring
      _ = 10 ^ (n + 1) := by ring

lemma ofDigits_eq_zero_of_all_zero {b : ℕ} {L : List ℕ} (h : ∀ x ∈ L, x = 0) : ofDigits b L = 0 := by
  induction L with
  | nil => rfl
  | cons hd tl ih =>
    dsimp [ofDigits]
    have h1 : hd = 0 := h hd (List.Mem.head _)
    have h2 : ofDigits b tl = 0 := ih (fun x hx => h x (List.Mem.tail _ hx))
    rw [h1, h2, mul_zero, add_zero]

lemma digits_sum_pos (n : ℕ) (hn : n > 0) : (digits 10 n).sum > 0 := by
  by_contra h_zero
  have h1 : (digits 10 n).sum = 0 := by omega
  have H0 : ∀ x ∈ digits 10 n, x = 0 := by
    intro x hx
    exact List.sum_eq_zero_iff.mp h1 x hx
  have : ofDigits 10 (digits 10 n) = 0 := ofDigits_eq_zero_of_all_zero H0
  have : n = 0 := by
    calc n = ofDigits 10 (digits 10 n) := (ofDigits_digits 10 n).symm
      _ = 0 := this
  omega

lemma sum_digits_eq_sum_L (b : ℕ) (hb : 1 < b) (l : ℕ) (L : List ℕ)
    (hlen : L.length = l) (hlt : ∀ x ∈ L, x < b) :
    (digits b (ofDigits b L)).sum = L.sum := by
  exact sum_digits_ofDigits_eq_sum hb ⟨hlen, hlt⟩

theorem false_of_disproof : False := sorry



lemma exists_M_P (m : ℕ) (hm : m > 0) : ∃ M P, P > 0 ∧ ∀ x ≥ M, 10^(x + P) ≡ 10^x [MOD m] := by
  let f : Fin (m + 1) → Fin m := fun i => ⟨(10^i.val) % m, mod_lt _ hm⟩
  have : ∃ i j : Fin (m + 1), i ≠ j ∧ f i = f j := Fintype.exists_ne_map_eq_of_card_lt f (by simp)
  rcases this with ⟨i, j, hne, heq⟩
  have hlt : i.val < j.val ∨ j.val < i.val := by
    rcases lt_trichotomy i.val j.val with h | h | h
    · left; exact h
    · exfalso; apply hne; ext; exact h
    · right; exact h
  wlog hlt_i_j : i.val < j.val generalizing i j
  · rcases hlt with h | h
    · contradiction
    · exact this j i hne.symm heq.symm (Or.inl h) h
  use i.val, j.val - i.val
  have hp : j.val - i.val > 0 := tsub_pos_of_lt hlt_i_j
  refine ⟨hp, ?_⟩
  intro x hx
  have heq2 : 10^i.val ≡ 10^j.val [MOD m] := by
    have h1 : (f i).val = (f j).val := congrArg _ heq
    exact h1
  obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hx
  subst hd
  have h3 : 10^(i.val + d + (j.val - i.val)) = 10^j.val * 10^d := by
    rw [add_right_comm, add_tsub_cancel_of_le (le_of_lt hlt_i_j), pow_add]
  have h4 : 10^(i.val + d) = 10^i.val * 10^d := pow_add _ _ _
  rw [h3, h4]
  exact ModEq.mul_right _ heq2.symm

lemma mem_zip_left {α β} {a : α} {b : β} {l1 : List α} {l2 : List β} : (a, b) ∈ l1.zip l2 → a ∈ l1 := by
  induction l1 generalizing l2 with
  | nil => simp
  | cons h1 t1 ih =>
    intro h
    cases l2 with
    | nil => simp at h
    | cons h2 t2 =>
      simp only [List.zip_cons_cons, List.mem_cons] at h
      rcases h with h | h
      · have : a = h1 := congrArg Prod.fst h
        rw [this]
        exact List.Mem.head _
      · exact List.Mem.tail _ (ih h)

lemma mem_zip_right {α β} {a : α} {b : β} {l1 : List α} {l2 : List β} : (a, b) ∈ l1.zip l2 → b ∈ l2 := by
  induction l1 generalizing l2 with
  | nil => simp
  | cons h1 t1 ih =>
    intro h
    cases l2 with
    | nil => simp at h
    | cons h2 t2 =>
      simp only [List.zip_cons_cons, List.mem_cons] at h
      rcases h with h | h
      · have : b = h2 := congrArg Prod.snd h
        rw [this]
        exact List.Mem.head _
      · exact List.Mem.tail _ (ih h)

lemma nodup_of_pairwise_lt (L : List ℕ) (h : L.Pairwise (· < ·)) : L.Nodup := by
  induction L with
  | nil => exact List.nodup_nil
  | cons hd tl ih =>
    have h1 : tl.Pairwise (· < ·) := List.pairwise_cons.mp h |>.2
    have h2 : ∀ x ∈ tl, hd < x := List.pairwise_cons.mp h |>.1
    have h3 : hd ∉ tl := fun h_in => lt_irrefl hd (h2 hd h_in)
    exact List.nodup_cons.mpr ⟨h3, ih h1⟩

def digitsFromExponents (X : List ℕ) (max_exp : ℕ) : List ℕ :=
  List.ofFn (fun i : Fin max_exp => if (i:ℕ) ∈ X then 1 else 0)

lemma sum_toFinset_eq_sum_map (X : List ℕ) (h_distinct : X.Nodup) :
    ∑ i ∈ X.toFinset, 10 ^ i = (X.map (fun x => 10^x)).sum := by
  induction X with
  | nil => simp
  | cons hd tl ih =>
    simp only [List.toFinset_cons, List.map_cons, List.sum_cons]
    have h1 : hd ∉ tl := List.nodup_cons.mp h_distinct |>.1
    have h2 : tl.Nodup := List.nodup_cons.mp h_distinct |>.2
    have h3 : hd ∉ tl.toFinset := by simp [h1]
    rw [sum_insert h3, ih h2]

lemma ofDigits_digitsFromExponents (X : List ℕ) (max_exp : ℕ) (h_distinct : X.Nodup) (h_max : ∀ x ∈ X, x < max_exp) :
  ofDigits 10 (digitsFromExponents X max_exp) = (X.map (fun x => 10^x)).sum := by
  dsimp [digitsFromExponents]
  rw [ofDigits_eq_sum_mapIdx, List.mapIdx_eq_ofFn]
  have H1 : (List.ofFn fun i : Fin (List.ofFn fun i : Fin max_exp => if (i : ℕ) ∈ X then 1 else 0).length =>
      (List.ofFn fun i : Fin max_exp => if (i : ℕ) ∈ X then 1 else 0).get i * 10 ^ (i : ℕ)) =
      (List.ofFn fun i : Fin max_exp => (if (i : ℕ) ∈ X then 1 else 0) * 10 ^ (i : ℕ)) := by
    apply List.ext_get
    · simp
    · intro i h1 h2
      simp
  rw [H1, List.sum_ofFn]
  have Hsum : (∑ i : Fin max_exp, (if (i:ℕ) ∈ X then 1 else 0) * 10 ^ (i:ℕ)) = ∑ i ∈ range max_exp, (if i ∈ X then 1 else 0) * 10 ^ i := by
    exact (sum_range (fun i => (if i ∈ X then 1 else 0) * 10 ^ i)).symm
  rw [Hsum]
  have H2 : (∑ i ∈ range max_exp, (if i ∈ X then 1 else 0) * 10 ^ i) = ∑ i ∈ range max_exp, if i ∈ X then 10 ^ i else 0 := by
    apply sum_congr rfl
    intro i _
    by_cases hi : i ∈ X
    · rw [if_pos hi, if_pos hi, one_mul]
    · rw [if_neg hi, if_neg hi, zero_mul]
  rw [H2]
  have H3 : (∑ i ∈ range max_exp, if i ∈ X then 10 ^ i else 0) = ∑ i ∈ (range max_exp).filter (· ∈ X), 10 ^ i := by
    exact (sum_filter _ _).symm
  rw [H3]
  have H4 : (range max_exp).filter (· ∈ X) = X.toFinset := by
    ext a
    simp only [mem_filter, mem_range, List.mem_toFinset]
    exact ⟨fun h => h.2, fun h => ⟨h_max a h, h⟩⟩
  rw [H4, sum_toFinset_eq_sum_map X h_distinct]


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



@[simp]
def ninesAsc (M : ℕ) (k : ℕ) : List ℕ :=
  match k with
  | 0 => []
  | k' + 1 => ninesAsc M k' ++ List.replicate 9 (M + k')

def makeListAsc (m M k : ℕ) : List ℕ :=
  [M] ++ ninesAsc M k ++ List.replicate (m - 1) (M + k)

lemma mem_ninesAsc (M k x : ℕ) : x ∈ ninesAsc M k ↔ M ≤ x ∧ x < M + k := by
  induction k with
  | zero => simp
  | succ k' ih =>
    unfold ninesAsc
    simp [ih]
    constructor
    · rintro (⟨h1, h2⟩ | h3)
      · exact ⟨h1, by omega⟩
      · exact ⟨by omega, by omega⟩
    · rintro ⟨h1, h2⟩
      have h3 : x < M + k' ∨ x = M + k' := by omega
      rcases h3 with h3 | h3
      · exact Or.inl ⟨h1, h3⟩
      · exact Or.inr h3

lemma pairwise_le_replicate (n x : ℕ) : (List.replicate n x).Pairwise (· ≤ ·) := by
  apply List.pairwise_replicate.mpr
  exact Or.inr (le_refl _)

lemma pairwise_le_ninesAsc (M k : ℕ) : (ninesAsc M k).Pairwise (· ≤ ·) := by
  induction k with
  | zero => simp
  | succ k' ih =>
    unfold ninesAsc
    apply List.pairwise_append.mpr
    refine ⟨ih, pairwise_le_replicate _ _, ?_⟩
    intro x hx y hy
    rw [mem_ninesAsc] at hx
    have hy2 : y = M + k' := List.eq_of_mem_replicate hy
    omega

lemma pairwise_le_makeListAsc (m M k : ℕ) : (makeListAsc m M k).Pairwise (· ≤ ·) := by
  unfold makeListAsc
  apply List.pairwise_append.mpr
  refine ⟨?_, pairwise_le_replicate _ _, ?_⟩
  · apply List.pairwise_append.mpr
    refine ⟨by simp, pairwise_le_ninesAsc M k, ?_⟩
    intro x hx y hy
    have hx2 : x = M := by simp at hx; exact hx
    rw [mem_ninesAsc] at hy
    omega
  · intro x hx y hy
    have hy2 : y = M + k := List.eq_of_mem_replicate hy
    simp at hx
    rcases hx with hx | hx
    · omega
    · rw [mem_ninesAsc] at hx
      omega
lemma strictMono_of_sorted_add_P_gen (start : ℕ) (L : List ℕ) (h_sorted : L.Pairwise (· ≤ ·)) (P : ℕ) (hP : P > 0) :
    ((List.range' start L.length).zip L |>.map (fun ⟨i, y⟩ => y + i * P)).Pairwise (· < ·) := by
  induction L generalizing start with
  | nil => simp
  | cons hd tl ih =>
    simp only [List.length_cons, List.range'_succ, List.zip_cons_cons, List.map_cons, List.pairwise_cons]
    have h1 : tl.Pairwise (· ≤ ·) := List.pairwise_cons.mp h_sorted |>.2
    refine ⟨?_, ih (start + 1) h1⟩
    intro x hx
    rw [List.mem_map] at hx
    rcases hx with ⟨⟨i, y⟩, h_mem, rfl⟩
    have h_in_tl : y ∈ tl := mem_zip_right h_mem
    have h_le : hd ≤ y := List.pairwise_cons.mp h_sorted |>.1 y h_in_tl
    have h_i : i ≥ start + 1 := by
      have H2 : i ∈ List.range' (start + 1) tl.length := mem_zip_left h_mem
      have H3 := List.mem_range'.mp H2
      omega
    calc hd + start * P < hd + start * P + P := lt_add_of_pos_right _ hP
      _ = hd + (start + 1) * P := by ring
      _ ≤ y + i * P := by
        apply Nat.add_le_add h_le
        exact Nat.mul_le_mul_right P h_i

lemma strictMono_of_sorted_add_P (L : List ℕ) (h_sorted : L.Pairwise (· ≤ ·)) (P : ℕ) (hP : P > 0) :
    ((List.range L.length).zip L |>.map (fun ⟨i, y⟩ => y + i * P)).Pairwise (· < ·) := by
  have H : List.range L.length = List.range' 0 L.length := by simp [List.range_eq_range']
  rw [H]
  exact strictMono_of_sorted_add_P_gen 0 L h_sorted P hP

lemma sum_digitsFromExponents (X : List ℕ) (max_exp : ℕ) (h_max : ∀ x ∈ X, x < max_exp) (h_dup : X.Nodup) :
    (digitsFromExponents X max_exp).sum = X.length := by
  dsimp [digitsFromExponents]
  rw [List.sum_ofFn]
  have Hsum : (∑ i : Fin max_exp, (if (i:ℕ) ∈ X then 1 else 0)) = ∑ i ∈ range max_exp, if i ∈ X then 1 else 0 := by
    exact (sum_range (fun i => if i ∈ X then 1 else 0)).symm
  rw [Hsum]
  have H3 : (∑ i ∈ range max_exp, if i ∈ X then 1 else 0) = ∑ i ∈ (range max_exp).filter (· ∈ X), 1 := by
    exact (sum_filter _ _).symm
  rw [H3]
  have H4 : (range max_exp).filter (· ∈ X) = X.toFinset := by
    ext a
    simp only [mem_filter, mem_range, List.mem_toFinset]
    exact ⟨fun h => h.2, fun h => ⟨h_max a h, h⟩⟩
  rw [H4, sum_const, smul_eq_mul, mul_one, List.toFinset_card_of_nodup h_dup]

lemma digitsFromExponents_lt (X : List ℕ) (max_exp : ℕ) (x : ℕ) (hx : x ∈ digitsFromExponents X max_exp) :
    x < 10 := by
  dsimp [digitsFromExponents] at hx
  rw [List.mem_ofFn] at hx
  rcases hx with ⟨i, rfl⟩
  split_ifs
  · decide
  · decide

lemma digitsFromExponents_length (X : List ℕ) (max_exp : ℕ) :
    (digitsFromExponents X max_exp).length = max_exp := by
  dsimp [digitsFromExponents]
  simp

lemma makeListAsc_ge_M (m M k x : ℕ) (hx : x ∈ makeListAsc m M k) : x ≥ M := by
  unfold makeListAsc at hx
  simp at hx
  rcases hx with hx | hx | hx
  · omega
  · rw [mem_ninesAsc] at hx
    omega
  · omega

lemma partnerList_ge_M (m M k P x : ℕ) (hx : x ∈ ((List.range (makeListAsc m M k).length).zip (makeListAsc m M k)).map (fun ⟨i, y⟩ => y + i * P)) : x ≥ M := by
  rw [List.mem_map] at hx
  rcases hx with ⟨iy, h_mem, rfl⟩
  rcases iy with ⟨i, y⟩
  have h_in : y ∈ makeListAsc m M k := mem_zip_right h_mem
  have h_ge : y ≥ M := makeListAsc_ge_M m M k y h_in
  calc M ≤ y := h_ge
    _ ≤ y + i * P := Nat.le_add_right _ _

lemma mod_nine_eq_sum_digits (n : ℕ) : n ≡ (digits 10 n).sum [MOD 9] := by
  have H : ofDigits 10 (digits 10 n) ≡ (digits 10 n).sum [MOD 9] := by
    have h : ∀ L : List ℕ, ofDigits 10 L ≡ L.sum [MOD 9] := by
      intro L
      induction L with
      | nil => rfl
      | cons hd tl ih =>
        dsimp [ofDigits]
        have h1 : 10 ≡ 1 [MOD 9] := by rfl
        have h2 : 10 * ofDigits 10 tl ≡ 1 * tl.sum [MOD 9] := Nat.ModEq.mul h1 ih
        have h3 : 10 * ofDigits 10 tl ≡ tl.sum [MOD 9] := by
          rw [one_mul] at h2; exact h2
        exact Nat.ModEq.add Nat.ModEq.rfl h3
    exact h (digits 10 n)
  rw [ofDigits_digits 10 n] at H
  exact H

lemma sum_le_ofDigits (L : List ℕ) : L.sum ≤ ofDigits 10 L := by
  induction L with
  | nil => simp
  | cons hd tl ih =>
    dsimp [ofDigits]
    calc hd + tl.sum ≤ hd + ofDigits 10 tl := Nat.add_le_add_left ih hd
      _ ≤ hd + 10 * ofDigits 10 tl := by
        apply Nat.add_le_add_left
        calc ofDigits 10 tl = 1 * ofDigits 10 tl := by ring
          _ ≤ 10 * ofDigits 10 tl := Nat.mul_le_mul_right _ (by decide)

lemma digits_sum_le_n (n : ℕ) : (digits 10 n).sum ≤ n := by
  calc (digits 10 n).sum ≤ ofDigits 10 (digits 10 n) := sum_le_ofDigits _
    _ = n := ofDigits_digits 10 n

lemma exists_k_prime (n m : ℕ) (hm : m = (digits 10 n).sum) : ∃ k', n = m + 9 * k' := by
  have h1 : n ≡ m [MOD 9] := by
    rw [hm]
    exact mod_nine_eq_sum_digits n
  have h2 : m ≤ n := by
    rw [hm]
    exact digits_sum_le_n n
  have h3 : (n - m) % 9 = 0 := by
    have h4 : n % 9 = m % 9 := h1
    omega
  use (n - m) / 9
  have h5 : 9 * ((n - m) / 9) = n - m := Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero h3)
  omega

lemma n_lt_ten_pow_new (n : ℕ) : n < 10 ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    calc n + 1 ≤ 10 ^ n + 1 := Nat.add_le_add_right (le_of_lt ih) 1
      _ < 10 ^ n + 10 ^ n * 9 := by
        apply Nat.add_lt_add_left
        have : 1 ≤ 10 ^ n := Nat.one_le_pow _ _ (by decide)
        nlinarith
      _ = 10 ^ (n + 1) := by ring

lemma k_gt_n_new (n : ℕ) (Y : Finset ℕ) (h_n_pos : n > 0) (h_Y_nonempty : Y.Nonempty) (h_min : ∀ y ∈ Y, y ≥ n) :
    (∑ y ∈ Y, 10^y) > n := by
  have ⟨y0, hy0⟩ := h_Y_nonempty
  have h1 : 10^y0 ≤ ∑ y ∈ Y, 10^y := single_le_sum (fun _ _ => Nat.zero_le _) hy0
  have h2 : n ≤ y0 := h_min y0 hy0
  have h3 : 10^n ≤ 10^y0 := Nat.pow_le_pow_right (by decide) h2
  have h4 : n < 10^n := n_lt_ten_pow_new n
  omega

lemma length_ninesAsc (M k : ℕ) : (ninesAsc M k).length = 9 * k := by
  induction k with
  | zero => rfl
  | succ k' ih =>
    unfold ninesAsc
    simp [ih]
    omega

lemma length_makeListAsc (m M k : ℕ) (hm : m > 0) : (makeListAsc m M k).length = m + 9 * k := by
  unfold makeListAsc
  simp [length_ninesAsc]
  omega

lemma sum_ninesAsc (M k : ℕ) : ((ninesAsc M k).map (fun x => 10^x)).sum = 10^(M + k) - 10^M := by
  induction k with
  | zero => simp
  | succ k' ih =>
    unfold ninesAsc
    simp [ih]
    have h1 : 10^(M + (k' + 1)) = 10^(M + k') * 10 := by
      rw [← add_assoc, pow_succ]
    have h2 : 10^M ≤ 10^(M + k') := Nat.pow_le_pow_right (by decide) (Nat.le_add_right _ _)
    omega

lemma sum_makeListAsc (m M k : ℕ) (hm : m > 0) :
  ((makeListAsc m M k).map (fun x => 10^x)).sum = m * 10^(M + k) := by
  unfold makeListAsc
  simp [sum_ninesAsc]
  have h2 : 10^M ≤ 10^(M + k) := Nat.pow_le_pow_right (by decide) (Nat.le_add_right _ _)
  have h3 : (m - 1) * 10^(M + k) = m * 10^(M + k) - 10^(M + k) := by
    rw [tsub_mul, one_mul]
  have h4 : 10^(M + k) ≤ m * 10^(M + k) := by
    calc 10^(M + k) = 1 * 10^(M + k) := (one_mul _).symm
      _ ≤ m * 10^(M + k) := Nat.mul_le_mul_right _ hm
  omega


/-- A272479 Conjecture: the sequence contains no zeros. -/
theorem oeis_272479_conjecture_0 : ∀ n : ℕ, n > 0 → a n ≠ 0 := by
  intro n hn
  dsimp [a]
  let m := (digits 10 n).sum
  have hm : m > 0 := digits_sum_pos n hn
  have ⟨M0, P, hP_pos, hP⟩ := exists_M_P m hm
  let M := max M0 n
  have hP2 : ∀ x ≥ M, 10^(x + P) ≡ 10^x [MOD m] := fun x hx => hP x (by omega)
  have ⟨k', hk'⟩ := exists_k_prime n m rfl
  
  let L_asc := makeListAsc m M k'
  let Y_list := ((List.range L_asc.length).zip L_asc).map (fun ⟨i, y⟩ => y + i * P)
  
  have H_L_asc_len : L_asc.length = n := by
    calc L_asc.length = m + 9 * k' := length_makeListAsc m M k' hm
      _ = n := hk'.symm

  have H_Y_list_len : Y_list.length = n := by
    simp [Y_list, H_L_asc_len]

  have H_Y_nodup : Y_list.Nodup := by
    apply nodup_of_pairwise_lt
    have h_sorted : L_asc.Pairwise (· ≤ ·) := pairwise_le_makeListAsc m M k'
    have h_strict : Y_list.Pairwise (· < ·) := by
      have := strictMono_of_sorted_add_P L_asc h_sorted P hP_pos
      exact this
    exact h_strict

  have H_L_asc_ge : ∀ y ∈ L_asc, y ≥ M := fun y hy => makeListAsc_ge_M m M k' y hy

  have H_Y_list_ge : ∀ y ∈ Y_list, y ≥ M := fun y hy => partnerList_ge_M m M k' P y hy

  let L := digitsFromExponents Y_list (Y_list.foldr max 0 + 1)
  
  have h_max_bound : ∀ x ∈ Y_list, x < Y_list.foldr max 0 + 1 := by
    intro x hx
    have : x ≤ Y_list.foldr max 0 := List.le_max_of_le hx (by rfl)
    omega

  let k := ofDigits 10 L
  
  have hk_eq : k = (Y_list.map (fun x => 10^x)).sum := by
    dsimp [k, L]
    exact ofDigits_digitsFromExponents Y_list (Y_list.foldr max 0 + 1) H_Y_nodup h_max_bound

  have hk_mod : k % m = 0 := by
    have h1 : k ≡ (L_asc.map (fun x => 10^x)).sum [MOD m] := by
      rw [hk_eq]
      exact sum_partnerList_mod m M P L_asc hP2 H_L_asc_ge
    have h2 : (L_asc.map (fun x => 10^x)).sum = m * 10^(M + k') := sum_makeListAsc m M k' hm
    have h3 : k ≡ m * 10^(M + k') [MOD m] := by
      rw [h2] at h1
      exact h1
    have h4 : m * 10^(M + k') ≡ 0 [MOD m] := by
      change (m * 10^(M + k')) % m = 0 % m
      rw [Nat.mul_mod_right, Nat.zero_mod]
    have h5 : k ≡ 0 [MOD m] := Nat.ModEq.trans h3 h4
    exact h5

  have hL_sum : L.sum = n := by
    dsimp [L]
    rw [sum_digitsFromExponents Y_list _ h_max_bound H_Y_nodup]
    exact H_Y_list_len

  have hL_len : L.length = Y_list.foldr max 0 + 1 := digitsFromExponents_length Y_list _
  
  have hL_lt : ∀ x ∈ L, x < 10 := fun x hx => digitsFromExponents_lt Y_list _ x hx
  
  have h_dig : (digits 10 k).sum = n := by
    have h10 : 1 < 10 := by decide
    have H_sum : (digits 10 (ofDigits 10 L)).sum = L.sum := sum_digits_eq_sum_L 10 h10 _ L hL_len hL_lt
    rw [H_sum, hL_sum]
    
  have H_Y_nonempty : Y_list.toFinset.Nonempty := by
    have h_len : Y_list.length > 0 := by omega
    cases h_Y : Y_list with
    | cons hd tl => 
      use hd
      simp

  have hk_gt : k > n := by
    rw [hk_eq, ← sum_toFinset_eq_sum_map Y_list H_Y_nodup]
    apply k_gt_n_new n Y_list.toFinset hn H_Y_nonempty
    intro y hy
    rw [List.mem_toFinset] at hy
    have : y ≥ M := H_Y_list_ge y hy
    omega

  have hk_pos : k > 0 := by omega
  have hk_ne : k ≠ n := by omega
  
  have H_partner : k ∈ {x | x > 0 ∧ x ≠ n ∧ m ∣ x ∧ (digits 10 x).sum ∣ n} := by
    simp only [Set.mem_setOf_eq]
    refine ⟨hk_pos, hk_ne, Nat.dvd_of_mod_eq_zero hk_mod, ?_⟩
    rw [h_dig]
    exact dvd_rfl

  have H_nonempty : {x | x > 0 ∧ x ≠ n ∧ m ∣ x ∧ (digits 10 x).sum ∣ n}.Nonempty := ⟨k, H_partner⟩
  have H_s : (if h : {x | x > 0 ∧ ¬x = n ∧ m ∣ x ∧ (digits 10 x).sum ∣ n}.Nonempty then sInf {x | x > 0 ∧ ¬x = n ∧ m ∣ x ∧ (digits 10 x).sum ∣ n} else 0) ≠ 0 := by
    rw [dif_pos H_nonempty]
    have H_sInf := Nat.sInf_mem H_nonempty
    exact _root_.ne_of_gt H_sInf.1
  exact H_s

theorem oeis_272479_conjecture_0.disproof : ¬ (type_of% @oeis_272479_conjecture_0) := sorry
