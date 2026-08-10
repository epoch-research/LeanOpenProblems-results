import FormalConjectures.Util.ProblemImports

open Nat Finset

def A308734_test (n : ℕ) : ℕ :=
  let M := Nat.sqrt n + 1

  Finset.sum (range M) fun a =>
  Finset.sum (range M) fun b =>
  Finset.sum (range M) fun c =>
  Finset.sum (range M) fun d =>
  Finset.sum (range M) fun x =>
  Finset.sum (range M) fun y =>
    let term1 := (2^a * 3^b)^2
    let term2 := (2^c * 5^d)^2

    if term1 + term2 + x^2 + y^2 = n ∧ x ≤ y
    then 1
    else 0

lemma A308734_pos_of_exists (n : ℕ) (a b c d x y : ℕ)
    (ha : a < Nat.sqrt n + 1) (hb : b < Nat.sqrt n + 1)
    (hc : c < Nat.sqrt n + 1) (hd : d < Nat.sqrt n + 1)
    (hx : x < Nat.sqrt n + 1) (hy : y < Nat.sqrt n + 1)
    (h : (2^a * 3^b)^2 + (2^c * 5^d)^2 + x^2 + y^2 = n)
    (hxy : x ≤ y) :
    A308734_test n > 0 := by
  have h_a : a ∈ range (Nat.sqrt n + 1) := mem_range.mpr ha
  have h_b : b ∈ range (Nat.sqrt n + 1) := mem_range.mpr hb
  have h_c : c ∈ range (Nat.sqrt n + 1) := mem_range.mpr hc
  have h_d : d ∈ range (Nat.sqrt n + 1) := mem_range.mpr hd
  have h_x : x ∈ range (Nat.sqrt n + 1) := mem_range.mpr hx
  have h_y : y ∈ range (Nat.sqrt n + 1) := mem_range.mpr hy

  -- M is Nat.sqrt n + 1
  -- We want to show A308734 n > 0, which is A308734 n ≥ 1.
  -- We will use single_le_sum repeatedly.
  have h1 : (Finset.sum (range (Nat.sqrt n + 1)) fun b =>
             Finset.sum (range (Nat.sqrt n + 1)) fun c =>
             Finset.sum (range (Nat.sqrt n + 1)) fun d =>
             Finset.sum (range (Nat.sqrt n + 1)) fun x =>
             Finset.sum (range (Nat.sqrt n + 1)) fun y =>
             if (2^a * 3^b)^2 + (2^c * 5^d)^2 + x^2 + y^2 = n ∧ x ≤ y then 1 else 0)
            ≤ A308734_test n := by
    apply single_le_sum (fun _ _ => Nat.zero_le _) h_a

  have h2 : (Finset.sum (range (Nat.sqrt n + 1)) fun c =>
             Finset.sum (range (Nat.sqrt n + 1)) fun d =>
             Finset.sum (range (Nat.sqrt n + 1)) fun x =>
             Finset.sum (range (Nat.sqrt n + 1)) fun y =>
             if (2^a * 3^b)^2 + (2^c * 5^d)^2 + x^2 + y^2 = n ∧ x ≤ y then 1 else 0)
            ≤ (Finset.sum (range (Nat.sqrt n + 1)) fun b =>
               Finset.sum (range (Nat.sqrt n + 1)) fun c =>
               Finset.sum (range (Nat.sqrt n + 1)) fun d =>
               Finset.sum (range (Nat.sqrt n + 1)) fun x =>
               Finset.sum (range (Nat.sqrt n + 1)) fun y =>
               if (2^a * 3^b)^2 + (2^c * 5^d)^2 + x^2 + y^2 = n ∧ x ≤ y then 1 else 0) := by
    apply single_le_sum (fun _ _ => Nat.zero_le _) h_b

  have h3 : (Finset.sum (range (Nat.sqrt n + 1)) fun d =>
             Finset.sum (range (Nat.sqrt n + 1)) fun x =>
             Finset.sum (range (Nat.sqrt n + 1)) fun y =>
             if (2^a * 3^b)^2 + (2^c * 5^d)^2 + x^2 + y^2 = n ∧ x ≤ y then 1 else 0)
            ≤ (Finset.sum (range (Nat.sqrt n + 1)) fun c =>
               Finset.sum (range (Nat.sqrt n + 1)) fun d =>
               Finset.sum (range (Nat.sqrt n + 1)) fun x =>
               Finset.sum (range (Nat.sqrt n + 1)) fun y =>
               if (2^a * 3^b)^2 + (2^c * 5^d)^2 + x^2 + y^2 = n ∧ x ≤ y then 1 else 0) := by
    apply single_le_sum (fun _ _ => Nat.zero_le _) h_c

  have h4 : (Finset.sum (range (Nat.sqrt n + 1)) fun x =>
             Finset.sum (range (Nat.sqrt n + 1)) fun y =>
             if (2^a * 3^b)^2 + (2^c * 5^d)^2 + x^2 + y^2 = n ∧ x ≤ y then 1 else 0)
            ≤ (Finset.sum (range (Nat.sqrt n + 1)) fun d =>
               Finset.sum (range (Nat.sqrt n + 1)) fun x =>
               Finset.sum (range (Nat.sqrt n + 1)) fun y =>
               if (2^a * 3^b)^2 + (2^c * 5^d)^2 + x^2 + y^2 = n ∧ x ≤ y then 1 else 0) := by
    apply single_le_sum (fun _ _ => Nat.zero_le _) h_d

  have h5 : (Finset.sum (range (Nat.sqrt n + 1)) fun y =>
             if (2^a * 3^b)^2 + (2^c * 5^d)^2 + x^2 + y^2 = n ∧ x ≤ y then 1 else 0)
            ≤ (Finset.sum (range (Nat.sqrt n + 1)) fun x =>
               Finset.sum (range (Nat.sqrt n + 1)) fun y =>
               if (2^a * 3^b)^2 + (2^c * 5^d)^2 + x^2 + y^2 = n ∧ x ≤ y then 1 else 0) := by
    apply single_le_sum (fun _ _ => Nat.zero_le _) h_x

  have h6 : (if (2^a * 3^b)^2 + (2^c * 5^d)^2 + x^2 + y^2 = n ∧ x ≤ y then 1 else 0)
            ≤ (Finset.sum (range (Nat.sqrt n + 1)) fun y =>
               if (2^a * 3^b)^2 + (2^c * 5^d)^2 + x^2 + y^2 = n ∧ x ≤ y then 1 else 0) := by
    apply single_le_sum (fun _ _ => Nat.zero_le _) h_y

  have h_term : (if (2^a * 3^b)^2 + (2^c * 5^d)^2 + x^2 + y^2 = n ∧ x ≤ y then 1 else 0) = 1 := by
    simp [h, hxy]

  have h_final : 1 ≤ A308734_test n := by
    rw [← h_term]
    exact h6.trans (h5.trans (h4.trans (h3.trans (h2.trans h1))))

  exact h_final

example : A308734_test 2 > 0 := by
  apply A308734_pos_of_exists 2 0 0 0 0 0 0 <;> try decide

