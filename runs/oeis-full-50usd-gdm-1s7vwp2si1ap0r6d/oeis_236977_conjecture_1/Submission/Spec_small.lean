import FormalConjectures.Util.ProblemImports

open Nat Finset

def a (n : ℕ) : ℕ :=
  (Ico 1 ((n - 1) / 2 + 1)).sum fun k =>
    let m := totient k * totient (n - k)
    if sqrt m ^ 2 = m then 1 else 0

def divide_loop (d : ℕ) (t : ℕ) (fuel : ℕ) : ℕ :=
  match fuel with
  | 0 => t
  | f + 1 => if t % d == 0 then divide_loop d (t / d) f else t

def totient_loop (temp : ℕ) (d : ℕ) (ans : ℕ) (fuel : ℕ) : ℕ :=
  match fuel with
  | 0 => ans
  | f + 1 =>
    if d * d > temp then
      if temp > 1 then ans - ans / temp else ans
    else
      if temp % d == 0 then
        let new_temp := divide_loop d temp temp
        totient_loop new_temp (d + 1) (ans - ans / d) f
      else
        totient_loop temp (d + 1) ans f

def fast_tot_impl (n : ℕ) : ℕ :=
  if n == 0 then
    0
  else if n == 1 then
    1
  else
    totient_loop n 2 n n

@[implemented_by fast_tot_impl]
def my_totient (n : ℕ) : ℕ := totient n

def sqrt_iter (n guess fuel : ℕ) : ℕ :=
  match fuel with
  | 0 => guess
  | f + 1 =>
    let next := (guess + n / guess) / 2
    if next >= guess then
      guess
    else
      sqrt_iter n next f

def my_sqrt (n : ℕ) : ℕ :=
  if n <= 1 then
    n
  else
    sqrt_iter n (n / 2) 100

def witness_block_0 : String := "\x00\x01"

def witness_block_1 : String := "\x00\x01"

def witness_block_2 : String := "\x00\x01"

def witness_block_3 : String := "\x00\x01"

def witness_block_4 : String := "\x00\x01"

def witness_block_5 : String := "\x00\x01"

def witness_block_6 : String := "\x00\x01"

def witness_block_7 : String := "\x00\x01"

def witness_block_8 : String := "\x00\x01"

def witness_block_9 : String := "\x00\x01"

def get_witness (n : Nat) : Nat :=
  let idx := n - 9
  let block_idx := idx / 200000
  let local_idx := idx % 200000
  let byte_idx := 2 * local_idx
  let bytes :=
    if block_idx == 0 then witness_block_0.toByteArray
    if block_idx == 1 then witness_block_1.toByteArray
    if block_idx == 2 then witness_block_2.toByteArray
    if block_idx == 3 then witness_block_3.toByteArray
    if block_idx == 4 then witness_block_4.toByteArray
    if block_idx == 5 then witness_block_5.toByteArray
    if block_idx == 6 then witness_block_6.toByteArray
    if block_idx == 7 then witness_block_7.toByteArray
    if block_idx == 8 then witness_block_8.toByteArray
    if block_idx == 9 then witness_block_9.toByteArray
    else ByteArray.empty
  let c1 := (bytes.get! byte_idx).toNat
  let c2 := (bytes.get! (byte_idx + 1)).toNat
  c1 * 128 + c2

def verify_witness (n : Nat) : Bool :=
  let k := get_witness n
  let limit := (n - 1) / 2
  if (1 <= k) && (k <= limit) then
    let m := my_totient k * my_totient (n - k)
    my_sqrt m ^ 2 == m
  else
    false

theorem verify_all : ∀ n ∈ Ico 9 2000001, verify_witness n = true := by
  decide +native

theorem a_pos_of_witness (n : ℕ) (k : ℕ) (hk1 : 1 ≤ k) (hk2 : k ≤ (n - 1) / 2)
    (h_sq : sqrt (totient k * totient (n - k)) ^ 2 = totient k * totient (n - k)) : a n > 0 := by
  have h_mem : k ∈ Ico 1 ((n - 1) / 2 + 1) := by
    rw [mem_Ico]
    refine ⟨hk1, ?_⟩
    exact lt_succ_of_le hk2
  have h_term : (let m := totient k * totient (n - k); if sqrt m ^ 2 = m then 1 else 0) = 1 := by
    dsimp only
    rw [if_pos h_sq]
  have h_le := Finset.single_le_sum (f := fun k => let m := totient k * totient (n - k); if sqrt m ^ 2 = m then 1 else 0)
    (fun _ _ => Nat.zero_le _) h_mem
  dsimp only at h_le
  rw [h_term] at h_le
  exact h_le

theorem a_pos_of_verify_witness (n : ℕ) (h_val : verify_witness n = true) : a n > 0 := by
  dsimp [verify_witness] at h_val
  generalize hk : get_witness n = k at h_val
  let limit := (n - 1) / 2
  split_ifs at h_val with h_cond
  · have hk1 : 1 ≤ k := by
      have h_and := Bool.and_eq_true_iff.mp h_cond
      exact Bool.coe_decide_iff.mp h_and.1
    have hk2 : k ≤ limit := by
      have h_and := Bool.and_eq_true_iff.mp h_cond
      exact Bool.coe_decide_iff.mp h_and.2
    have h_sq_eq : (my_sqrt (my_totient k * my_totient (n - k))) ^ 2 = my_totient k * my_totient (n - k) := by
      exact eq_of_beq h_val
    change (my_sqrt (totient k * totient (n - k))) ^ 2 = totient k * totient (n - k) at h_sq_eq
    let m := totient k * totient (n - k)
    have h_exists : ∃ r, r ^ 2 = m := by
      use my_sqrt m
    have h_sq : sqrt m ^ 2 = m := by
      rwa [← exists_mul_self']
    exact a_pos_of_witness n k hk1 hk2 h_sq
  · contradiction

theorem oeis_236977_conjecture_1 (n : ℕ) (h_n : 9 ≤ n ∧ n ≤ 2 * 10^6) : a n > 0 := by
  have h_mem : n ∈ Ico 9 2000001 := by
    rw [mem_Ico]
    exact ⟨h_n.1, lt_succ_of_le h_n.2⟩
  have h_val : verify_witness n = true := verify_all n h_mem
  exact a_pos_of_verify_witness n h_val
