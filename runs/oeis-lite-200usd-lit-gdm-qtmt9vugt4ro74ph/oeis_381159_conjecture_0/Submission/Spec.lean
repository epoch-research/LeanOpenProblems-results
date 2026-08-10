import FormalConjectures.Util.ProblemImports

set_option maxRecDepth 100000

open Nat

/--
Numbers whose prime divisors all end in the same digit.
-/
def A381159_condition (n : ℕ) : Prop :=
  Finset.card (n.primeFactors.image (fun p => p % 10)) ≤ 1

/--
A381159: Numbers whose prime divisors all end in the same digit.
-/
noncomputable def A381159 (n : ℕ) : ℕ := n.nth A381159_condition

/--
A381159 51st All-Russian Mathematical Olympiad for Schoolchildren. Problem.
Let us call a natural number "lopsided" if it is greater than 1 and all its prime divisors end with the same digit.
Is there an increasing arithmetic progression with a difference not exceeding 2025,
consisting of 150 natural numbers, each of which is "lopsided"? (A. Chironov)

We formalize the positive answer to the question/conjecture.
The condition for "lopsided" for n > 1 is exactly A381159_condition n.
We require the starting term a to be at least 2 to ensure all terms are > 1.
-/

def get_pq (d : ℕ) : ℕ × ℕ :=
  if d % 11 ≠ 0 ∧ d % 13 ≠ 0 then (11, 13)
  else if d % 7 ≠ 0 ∧ d % 19 ≠ 0 then (7, 19)
  else if d % 5 ≠ 0 ∧ d % 29 ≠ 0 then (5, 29)
  else if d % 3 ≠ 0 ∧ d % 17 ≠ 0 then (3, 17)
  else (2, 17)

lemma get_pq_properties (d : ℕ) :
  Nat.Prime (get_pq d).1 ∧
  Nat.Prime (get_pq d).2 ∧
  (get_pq d).1 ≠ (get_pq d).2 ∧
  (get_pq d).1 % 10 ≠ (get_pq d).2 % 10 ∧
  (get_pq d).1 * (get_pq d).2 ≤ 150 := by
  dsimp [get_pq]
  split_ifs <;> (repeat constructor <;> decide)

lemma helper : ∀ d : Fin 2026, d.val ≥ 1 → ¬ (get_pq d.val).1 ∣ d.val ∧ ¬ (get_pq d.val).2 ∣ d.val := by
  decide

lemma coprime_d_mul (d p q : ℕ) (hp : Nat.Prime p) (hq : Nat.Prime q) (hdp : ¬ p ∣ d) (hdq : ¬ q ∣ d) :
  d.Coprime (p * q) := by
  have cp : p.Coprime d := (hp.coprime_iff_not_dvd).mpr hdp
  have cq : q.Coprime d := (hq.coprime_iff_not_dvd).mpr hdq
  have cpd : d.Coprime p := cp.symm
  have cqd : d.Coprime q := cq.symm
  exact cpd.mul_right cqd

lemma exists_i_dvd (a d p q : ℕ) (hp : Nat.Prime p) (hq : Nat.Prime q)
  (hdp : ¬ p ∣ d) (hdq : ¬ q ∣ d) (hpq : p * q ≤ 150) :
  ∃ (i : Fin 150), p * q ∣ a + i.val * d := by
  have hc : d.Coprime (p * q) := coprime_d_mul d p q hp hq hdp hdq
  have h_pos : p * q > 0 := by
    have hp2 : p ≥ 2 := hp.two_le
    have hq2 : q ≥ 2 := hq.two_le
    nlinarith
  haveI : NeZero (p * q) := ⟨h_pos.ne'⟩
  let u := ZMod.unitOfCoprime d hc
  let v : ZMod (p * q) := ↑(u⁻¹)
  let i_zmod : ZMod (p * q) := - (a : ZMod (p * q)) * v
  let i_val := i_zmod.val
  have h_val_lt : i_val < p * q := ZMod.val_lt i_zmod
  have h_val_lt_150 : i_val < 150 := by omega
  let i : Fin 150 := ⟨i_val, h_val_lt_150⟩
  use i
  dsimp [i]
  have h_eq : (i_val : ZMod (p * q)) = i_zmod := by simp [i_val]
  rw [← ZMod.natCast_eq_zero_iff (a + i_val * d) (p * q)]
  push_cast
  rw [h_eq]
  dsimp [i_zmod]
  have h_u : (d : ZMod (p * q)) = (u : ZMod (p * q)) := rfl
  rw [h_u]
  have h_inv : v * (u : ZMod (p * q)) = 1 := by
    dsimp [v]
    exact_mod_cast Units.inv_mul u
  calc
    ↑a + (-↑a * v) * ↑u = ↑a + -↑a * (v * ↑u) := by ring
    _ = ↑a + -↑a * 1 := by rw [h_inv]
    _ = 0 := by ring

lemma card_ge_two_of_mem_of_ne {α : Type*} [DecidableEq α] {S : Finset α} {x y : α}
  (hx : x ∈ S) (hy : y ∈ S) (hne : x ≠ y) : 2 ≤ S.card := by
  have h_sub : {x, y} ⊆ S := by
    intro a ha
    rw [Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with rfl | rfl
    · exact hx
    · exact hy
  have h_card : ({x, y} : Finset α).card = 2 := Finset.card_pair hne
  rw [← h_card]
  exact Finset.card_le_card h_sub

theorem oeis_381159_conjecture_0.disproof :
  ¬ ∃ (a d : ℕ),
    2 ≤ a ∧ -- The starting number 'a' must be lopsided, hence > 1. All subsequent terms will also be > 1.
    1 ≤ d ∧ -- 'd' must be positive for an increasing arithmetic progression
    d ≤ 2025 ∧ -- difference not exceeding 2025
    ∀ (i : Fin 150), A381159_condition (a + i.val * d) := by
  intro h
  rcases h with ⟨a, d, ha, hd, hd2025, h_cond⟩
  let p := (get_pq d).1
  let q := (get_pq d).2
  have h_prop := get_pq_properties d
  have hp : Nat.Prime p := h_prop.1
  have hq : Nat.Prime q := h_prop.2.1
  have hpq_ne : p ≠ q := h_prop.2.2.1
  have hpq_mod : p % 10 ≠ q % 10 := h_prop.2.2.2.1
  have hpq : p * q ≤ 150 := h_prop.2.2.2.2
  have h_dfin : d < 2026 := by omega
  let d_fin : Fin 2026 := ⟨d, h_dfin⟩
  have h_help := helper d_fin (by exact hd)
  have hdp : ¬ p ∣ d := h_help.1
  have hdq : ¬ q ∣ d := h_help.2
  have h_ex := exists_i_dvd a d p q hp hq hdp hdq hpq
  rcases h_ex with ⟨i, h_div⟩
  let n := a + i.val * d
  have h_n_cond := h_cond i
  have hn_ne_zero : n ≠ 0 := by omega
  have hp_dvd_n : p ∣ n := by
    have h_p_dvd_pq : p ∣ p * q := dvd_mul_right p q
    exact dvd_trans h_p_dvd_pq h_div
  have hq_dvd_n : q ∣ n := by
    have h_q_dvd_pq : q ∣ p * q := dvd_mul_left q p
    exact dvd_trans h_q_dvd_pq h_div
  have hp_mem : p ∈ n.primeFactors := Nat.mem_primeFactors.mpr ⟨hp, hp_dvd_n, hn_ne_zero⟩
  have hq_mem : q ∈ n.primeFactors := Nat.mem_primeFactors.mpr ⟨hq, hq_dvd_n, hn_ne_zero⟩
  have hp_mem_im : p % 10 ∈ n.primeFactors.image (fun p => p % 10) := Finset.mem_image_of_mem (fun p => p % 10) hp_mem
  have hq_mem_im : q % 10 ∈ n.primeFactors.image (fun p => p % 10) := Finset.mem_image_of_mem (fun p => p % 10) hq_mem
  have h_card_ge : 2 ≤ Finset.card (n.primeFactors.image (fun p => p % 10)) :=
    card_ge_two_of_mem_of_ne hp_mem_im hq_mem_im hpq_mod
  have h_card_le : Finset.card (n.primeFactors.image (fun p => p % 10)) ≤ 1 := h_n_cond
  omega
