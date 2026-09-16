import Mathlib

def my_minFacAux (n k fuel : ℕ) : ℕ :=
  match fuel with
  | 0 => n
  | f + 1 =>
    if n < k * k then n
    else if k ∣ n then k
    else my_minFacAux n (k + 2) f

lemma my_minFacAux_eq (n k fuel : ℕ) (hfuel : n < k + 2 * fuel) :
  my_minFacAux n k fuel = Nat.minFacAux n k := by
  induction fuel generalizing k with
  | zero =>
    unfold my_minFacAux
    have hk : n < k * k := by
      have : n < k := by omega
      calc n < k := this
           _ ≤ k * k := Nat.le_mul_self k
    rw [Nat.minFacAux]
    simp [hk]
  | succ f ih =>
    unfold my_minFacAux
    rw [Nat.minFacAux]
    split_ifs with h1 h2
    · rfl
    · rfl
    · rw [ih]
      omega

def my_minFac (n : ℕ) : ℕ :=
  if 2 ∣ n then 2
  else my_minFacAux n 3 n

lemma my_minFac_eq (n : ℕ) : my_minFac n = Nat.minFac n := by
  unfold my_minFac
  rw [Nat.minFac_eq]
  split_ifs with h
  · rfl
  · have hfuel : n < 3 + 2 * n := by omega
    rw [my_minFacAux_eq n 3 n hfuel]

def my_prime (n : ℕ) : Bool :=
  if n < 2 then false
  else if my_minFac n == n then true
  else false

lemma my_prime_eq (n : ℕ) : my_prime n = true ↔ Nat.Prime n := by
  unfold my_prime
  split_ifs with h1 h2
  · simp [Nat.prime_def_minFac]
    intro h
    omega
  · simp [my_minFac_eq] at h2
    simp [Nat.prime_def_minFac, h2]
    omega
  · simp [my_minFac_eq] at h2
    simp [Nat.prime_def_minFac, h2]

def my_pi_chunk (start len : ℕ) : ℕ :=
  match len with
  | 0 => 0
  | l + 1 => my_pi_chunk start l + if my_prime (start + l) then 1 else 0

lemma my_pi_chunk_eq_countP (start len : ℕ) :
  my_pi_chunk start len = ((List.range len).map (fun i => start + i)).countP my_prime := by
  induction len with
  | zero => rfl
  | succ l ih =>
    unfold my_pi_chunk
    rw [ih]
    have : List.range (l + 1) = List.range l ++ [l] := List.range_succ
    rw [this, List.map_append, List.countP_append, List.map_singleton, List.countP_singleton]

lemma my_prime_eq_decide (n : ℕ) : my_prime n = decide (Nat.Prime n) := by
  have := my_prime_eq n
  cases h : my_prime n
  · simp [h] at this
    exact (decide_eq_false this).symm
  · simp [h] at this
    exact (decide_eq_true this).symm

lemma countP_eq_primeCounting (n : ℕ) :
  (List.range (n + 1)).countP my_prime = Nat.primeCounting n := by
  rw [Nat.primeCounting]
  unfold Nat.primeCounting'
  unfold Nat.count
  have h_eq : my_prime = fun b => decide (Nat.Prime b) := by
    funext b
    exact my_prime_eq_decide b
  rw [h_eq]

lemma my_pi_chunk_0_eq (n : ℕ) : my_pi_chunk 0 (n + 1) = Nat.primeCounting n := by
  rw [my_pi_chunk_eq_countP 0 (n + 1)]
  have h_map : (List.range (n + 1)).map (fun i => 0 + i) = List.range (n + 1) := by
    simp
  rw [h_map]
  exact countP_eq_primeCounting n

def my_pi (n : ℕ) : ℕ := my_pi_chunk 0 (n + 1)

lemma my_pi_eq (n : ℕ) : my_pi n = Nat.primeCounting n := by
  unfold my_pi
  exact my_pi_chunk_0_eq n

@[simp] lemma my_pi_chunk_succ (start l : ℕ) :
  my_pi_chunk start (l + 1) = my_pi_chunk start l + if my_prime (start + l) then 1 else 0 := rfl

lemma my_pi_chunk_add (start len1 len2 : ℕ) :
  my_pi_chunk start (len1 + len2) = my_pi_chunk start len1 + my_pi_chunk (start + len1) len2 := by
  induction len2 with
  | zero =>
    simp [my_pi_chunk]
  | succ l ih =>
    have h_add : len1 + (l + 1) = (len1 + l) + 1 := by omega
    rw [h_add]
    rw [my_pi_chunk_succ]
    rw [ih]
    rw [my_pi_chunk_succ]
    have h_add2 : start + len1 + l = start + (len1 + l) := by omega
    rw [h_add2]
    omega

lemma my_pi_chunk_mono (start len1 len2 : ℕ) (h : len1 ≤ len2) :
  my_pi_chunk start len1 ≤ my_pi_chunk start len2 := by
  have h_add : len2 = len1 + (len2 - len1) := by omega
  nth_rw 1 [h_add]
  rw [my_pi_chunk_add]
  omega

lemma my_pi_mono {a b : ℕ} (h : a ≤ b) : my_pi a ≤ my_pi b := by
  unfold my_pi
  apply my_pi_chunk_mono
  omega
lemma my_pi_def_eq (n) : my_pi n = my_pi_chunk 0 (n + 1) := rfl

lemma pi_step (curr prev diff val_prev diff_val : ℕ)
  (h_curr : curr = prev + diff)
  (h_prev : my_pi prev = val_prev)
  (h_diff : my_pi_chunk (prev + 1) diff = diff_val) :
  my_pi curr = val_prev + diff_val := by
  subst h_curr h_prev h_diff
  unfold my_pi
  have h_add : prev + diff + 1 = (prev + 1) + diff := by omega
  rw [h_add, my_pi_chunk_add]
  congr 1
  congr 1
  omega
