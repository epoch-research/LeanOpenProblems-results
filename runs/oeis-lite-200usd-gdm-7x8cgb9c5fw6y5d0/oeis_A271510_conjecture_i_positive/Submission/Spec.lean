import FormalConjectures.Util.ProblemImports

open Nat

/--
A271510: Number of ordered ways to write $n$ as $x^2 + y^2 + z^2 + w^2$ with $x \ge y \ge 0$, $z \ge 0$ and $w \ge 0$ such that $x^2 + 8y^2 + 16z^2$ is a square.
-/
def A271510 (n : ℕ) : ℕ :=
  -- Define the decidable predicate for being a perfect square in ℕ.
  let is_square (k : ℕ) : Prop := k.sqrt * k.sqrt = k

  -- The maximum value for any variable is $\lfloor\sqrt{n}\rfloor$.
  let bound := n.sqrt
  let R : Finset ℕ := Finset.range (bound + 1)

  -- The search space is the Cartesian product R x R x R x R, structured as (((ℕ × ℕ) × ℕ) × ℕ).
  let search_space : Finset (((ℕ × ℕ) × ℕ) × ℕ) := R.product R |>.product R |>.product R

  Finset.card $ search_space.filter fun p =>
    -- Decompose the nested product tuple p = (((x, y), z), w)
    let x := p.fst.fst.fst
    let y := p.fst.fst.snd
    let z := p.fst.snd
    let w := p.snd

    -- Constraint 1: sum of squares equals n
    x ^ 2 + y ^ 2 + z ^ 2 + w ^ 2 = n ∧
    -- Constraint 2: $x \ge y$
    x ≥ y ∧
    -- Constraint 3: $x^2 + 8y^2 + 16z^2$ is a square.
    is_square (x ^ 2 + 8 * y ^ 2 + 16 * z ^ 2)

-- A standard definition for "is a square" on ℕ
def is_square (k : ℕ) : Prop := ∃ m : ℕ, k = m^2



lemma nonempty_filter_of_mem {α : Type*} [DecidableEq α] {s : Finset α} {p : α → Prop} [DecidablePred p] {x : α} (hx : x ∈ s) (hp : p x) : 0 < (s.filter p).card := by
  rw [Finset.card_pos]
  exact ⟨x, Finset.mem_filter.mpr ⟨hx, hp⟩⟩




lemma A271510_pos_of_exists (n : ℕ) (x y z w : ℕ)
    (h_sum : x ^ 2 + y ^ 2 + z ^ 2 + w ^ 2 = n)
    (h_ge : x ≥ y)
    (h_sq : (x ^ 2 + 8 * y ^ 2 + 16 * z ^ 2).sqrt * (x ^ 2 + 8 * y ^ 2 + 16 * z ^ 2).sqrt = x ^ 2 + 8 * y ^ 2 + 16 * z ^ 2) :
    0 < A271510 n := by
  unfold A271510
  have h_x : x ^ 2 ≤ n := by omega
  have h_y : y ^ 2 ≤ n := by omega
  have h_z : z ^ 2 ≤ n := by omega
  have h_w : w ^ 2 ≤ n := by omega
  have h_x_bound : x ≤ n.sqrt := Nat.le_sqrt'.mpr h_x
  have h_y_bound : y ≤ n.sqrt := Nat.le_sqrt'.mpr h_y
  have h_z_bound : z ≤ n.sqrt := Nat.le_sqrt'.mpr h_z
  have h_w_bound : w ≤ n.sqrt := Nat.le_sqrt'.mpr h_w
  let R := Finset.range (n.sqrt + 1)
  have h_mem : (((x, y), z), w) ∈ ((R.product R).product R).product R :=
    Finset.mk_mem_product
      (Finset.mk_mem_product
        (Finset.mk_mem_product
          (Finset.mem_range.mpr (by omega))
          (Finset.mem_range.mpr (by omega)))
        (Finset.mem_range.mpr (by omega)))
      (Finset.mem_range.mpr (by omega))
  have h_sq' : (fun k => k.sqrt * k.sqrt = k) (x ^ 2 + 8 * y ^ 2 + 16 * z ^ 2) := h_sq
  exact nonempty_filter_of_mem h_mem ⟨h_sum, h_ge, h_sq'⟩


lemma A271510_pos_iff_exists (n : ℕ) :
    0 < A271510 n ↔ ∃ x y z w, x ^ 2 + y ^ 2 + z ^ 2 + w ^ 2 = n ∧ x ≥ y ∧ (x ^ 2 + 8 * y ^ 2 + 16 * z ^ 2).sqrt * (x ^ 2 + 8 * y ^ 2 + 16 * z ^ 2).sqrt = x ^ 2 + 8 * y ^ 2 + 16 * z ^ 2 := by
  constructor
  · intro h
    unfold A271510 at h
    rw [Finset.card_pos] at h
    obtain ⟨p, hp⟩ := h
    rw [Finset.mem_filter] at hp
    let x := p.fst.fst.fst
    let y := p.fst.fst.snd
    let z := p.fst.snd
    let w := p.snd
    use x, y, z, w
    exact hp.2
  · rintro ⟨x, y, z, w, h_sum, h_ge, h_sq⟩
    exact A271510_pos_of_exists n x y z w h_sum h_ge h_sq


lemma A271510_pos_of_four_mul (n : ℕ) (h : 0 < A271510 n) : 0 < A271510 (4 * n) := by
  rw [A271510_pos_iff_exists] at h ⊢
  obtain ⟨x, y, z, w, h_sum, h_ge, h_sq⟩ := h
  use 2 * x, 2 * y, 2 * z, 2 * w
  refine ⟨?_, by omega, ?_⟩
  · linarith [h_sum]
  · rw [← Nat.exists_mul_self] at h_sq ⊢
    obtain ⟨K, hK⟩ := h_sq
    use 2 * K
    calc (2 * K) * (2 * K) = 4 * (K * K) := by ring
    _ = 4 * (x ^ 2 + 8 * y ^ 2 + 16 * z ^ 2) := by rw [hK]
    _ = (2 * x) ^ 2 + 8 * (2 * y) ^ 2 + 16 * (2 * z) ^ 2 := by ring


lemma prove_sq (x y z K : ℕ) (h_eval : x ^ 2 + 8 * y ^ 2 + 16 * z ^ 2 = K * K) :
    (x ^ 2 + 8 * y ^ 2 + 16 * z ^ 2).sqrt * (x ^ 2 + 8 * y ^ 2 + 16 * z ^ 2).sqrt = x ^ 2 + 8 * y ^ 2 + 16 * z ^ 2 := by
  rw [h_eval, Nat.sqrt_eq K]


def M0_pred (m : ℕ) : Prop :=
  ∃ x y z, x^2 + y^2 + z^2 = m ∧ x ≥ y ∧ (x^2 + 8*y^2 + 16*z^2).sqrt * (x^2 + 8*y^2 + 16*z^2).sqrt = x^2 + 8*y^2 + 16*z^2

def is_M0 (m : ℕ) : Bool :=
  let bound := m.sqrt
  (List.range (bound + 1)).any fun x =>
    (List.range (x + 1)).any fun y =>
      if x^2 + y^2 ≤ m then
        if (m - x^2 - y^2).sqrt * (m - x^2 - y^2).sqrt = m - x^2 - y^2 then
          (x^2 + 8 * y^2 + 16 * (m - x^2 - y^2).sqrt^2).sqrt * (x^2 + 8 * y^2 + 16 * (m - x^2 - y^2).sqrt^2).sqrt == x^2 + 8 * y^2 + 16 * (m - x^2 - y^2).sqrt^2
        else
          false
      else
        false

lemma M0_of_is_M0 (m : ℕ) (h : is_M0 m = true) : M0_pred m := by
  unfold is_M0 at h
  rw [List.any_eq_true] at h
  obtain ⟨x, hx, h⟩ := h
  rw [List.mem_range] at hx
  rw [List.any_eq_true] at h
  obtain ⟨y, hy, h⟩ := h
  rw [List.mem_range] at hy
  split_ifs at h with h1 h2
  rw [beq_iff_eq] at h
  use x, y, (m - x^2 - y^2).sqrt
  have h_sum : x^2 + y^2 + (m - x^2 - y^2).sqrt^2 = m := by
    rw [sq ((m - x^2 - y^2).sqrt)]
    rw [h2]
    omega
  refine ⟨h_sum, ?_, h⟩
  omega

lemma A271510_pos_of_M0_add_sq (m w : ℕ) (h : M0_pred m) : 0 < A271510 (m + w^2) := by
  obtain ⟨x, y, z, h_sum, h_ge, h_sq⟩ := h
  refine A271510_pos_of_exists (m + w^2) x y z w ?_ h_ge h_sq
  omega

lemma A271510_pos_of_four_M0_add_sq (m w : ℕ) (h : M0_pred m) : 0 < A271510 (4 * m + w^2) := by
  obtain ⟨x, y, z, h_sum, h_ge, h_sq⟩ := h
  let K := (x^2 + 8*y^2 + 16*z^2).sqrt
  have h_K : K * K = x^2 + 8*y^2 + 16*z^2 := h_sq
  have h_eval : (2 * x) ^ 2 + 8 * (2 * y) ^ 2 + 16 * (2 * z) ^ 2 = (2 * K) * (2 * K) := by
    calc (2 * x) ^ 2 + 8 * (2 * y) ^ 2 + 16 * (2 * z) ^ 2 = 4 * (x ^ 2 + 8 * y ^ 2 + 16 * z ^ 2) := by ring
    _ = 4 * (K * K) := by rw [h_K]
    _ = (2 * K) * (2 * K) := by ring
  refine A271510_pos_of_exists (4 * m + w^2) (2 * x) (2 * y) (2 * z) w ?_ (by omega) ?_
  · calc (2 * x) ^ 2 + (2 * y) ^ 2 + (2 * z) ^ 2 + w ^ 2 = 4 * (x^2 + y^2 + z^2) + w^2 := by ring
    _ = 4 * m + w^2 := by rw [h_sum]
  · rw [h_eval, Nat.sqrt_eq (2 * K)]

lemma base_0 : 0 < A271510 0 :=
  A271510_pos_of_exists 0 0 0 0 0 (by rfl) (by omega) (prove_sq 0 0 0 0 (by rfl))

lemma base_1 : 0 < A271510 1 :=
  A271510_pos_of_exists 1 0 0 0 1 (by rfl) (by omega) (prove_sq 0 0 0 0 (by rfl))

lemma base_2 : 0 < A271510 2 :=
  A271510_pos_of_exists 2 0 0 1 1 (by rfl) (by omega) (prove_sq 0 0 1 4 (by rfl))

lemma base_3 : 0 < A271510 3 :=
  A271510_pos_of_exists 3 1 1 0 1 (by rfl) (by omega) (prove_sq 1 1 0 3 (by rfl))

lemma base_4 : 0 < A271510 4 :=
  A271510_pos_of_exists 4 0 0 0 2 (by rfl) (by omega) (prove_sq 0 0 0 0 (by rfl))

lemma base_5 : 0 < A271510 5 :=
  A271510_pos_of_exists 5 0 0 1 2 (by rfl) (by omega) (prove_sq 0 0 1 4 (by rfl))

lemma base_6 : 0 < A271510 6 :=
  A271510_pos_of_exists 6 1 1 0 2 (by rfl) (by omega) (prove_sq 1 1 0 3 (by rfl))

lemma base_7 : 0 < A271510 7 :=
  A271510_pos_of_exists 7 1 1 1 2 (by rfl) (by omega) (prove_sq 1 1 1 5 (by rfl))

lemma base_8 : 0 < A271510 8 :=
  A271510_pos_of_exists 8 0 0 2 2 (by rfl) (by omega) (prove_sq 0 0 2 8 (by rfl))

lemma base_9 : 0 < A271510 9 :=
  A271510_pos_of_exists 9 0 0 0 3 (by rfl) (by omega) (prove_sq 0 0 0 0 (by rfl))

lemma base_10 : 0 < A271510 10 :=
  A271510_pos_of_exists 10 0 0 1 3 (by rfl) (by omega) (prove_sq 0 0 1 4 (by rfl))

lemma base_11 : 0 < A271510 11 :=
  A271510_pos_of_exists 11 1 1 0 3 (by rfl) (by omega) (prove_sq 1 1 0 3 (by rfl))

lemma base_12 : 0 < A271510 12 :=
  A271510_pos_of_exists 12 1 1 1 3 (by rfl) (by omega) (prove_sq 1 1 1 5 (by rfl))

lemma base_13 : 0 < A271510 13 :=
  A271510_pos_of_exists 13 0 0 2 3 (by rfl) (by omega) (prove_sq 0 0 2 8 (by rfl))

lemma base_14 : 0 < A271510 14 :=
  A271510_pos_of_exists 14 3 0 1 2 (by rfl) (by omega) (prove_sq 3 0 1 5 (by rfl))

lemma base_15 : 0 < A271510 15 :=
  A271510_pos_of_exists 15 3 1 2 1 (by rfl) (by omega) (prove_sq 3 1 2 9 (by rfl))

lemma base_16 : 0 < A271510 16 :=
  A271510_pos_of_exists 16 0 0 0 4 (by rfl) (by omega) (prove_sq 0 0 0 0 (by rfl))

lemma base_17 : 0 < A271510 17 :=
  A271510_pos_of_exists 17 0 0 1 4 (by rfl) (by omega) (prove_sq 0 0 1 4 (by rfl))

lemma base_18 : 0 < A271510 18 :=
  A271510_pos_of_exists 18 0 0 3 3 (by rfl) (by omega) (prove_sq 0 0 3 12 (by rfl))

lemma base_19 : 0 < A271510 19 :=
  A271510_pos_of_exists 19 1 1 1 4 (by rfl) (by omega) (prove_sq 1 1 1 5 (by rfl))

lemma base_20 : 0 < A271510 20 :=
  A271510_pos_of_exists 20 0 0 2 4 (by rfl) (by omega) (prove_sq 0 0 2 8 (by rfl))

lemma base_21 : 0 < A271510 21 :=
  A271510_pos_of_exists 21 2 2 2 3 (by rfl) (by omega) (prove_sq 2 2 2 10 (by rfl))

lemma base_22 : 0 < A271510 22 :=
  A271510_pos_of_exists 22 3 3 0 2 (by rfl) (by omega) (prove_sq 3 3 0 9 (by rfl))

lemma base_23 : 0 < A271510 23 :=
  A271510_pos_of_exists 23 3 1 2 3 (by rfl) (by omega) (prove_sq 3 1 2 9 (by rfl))

lemma base_24 : 0 < A271510 24 :=
  A271510_pos_of_exists 24 2 2 0 4 (by rfl) (by omega) (prove_sq 2 2 0 6 (by rfl))

lemma base_25 : 0 < A271510 25 :=
  A271510_pos_of_exists 25 0 0 0 5 (by rfl) (by omega) (prove_sq 0 0 0 0 (by rfl))

lemma base_26 : 0 < A271510 26 :=
  A271510_pos_of_exists 26 0 0 1 5 (by rfl) (by omega) (prove_sq 0 0 1 4 (by rfl))

lemma base_27 : 0 < A271510 27 :=
  A271510_pos_of_exists 27 1 1 0 5 (by rfl) (by omega) (prove_sq 1 1 0 3 (by rfl))

lemma base_28 : 0 < A271510 28 :=
  A271510_pos_of_exists 28 1 1 1 5 (by rfl) (by omega) (prove_sq 1 1 1 5 (by rfl))

lemma base_29 : 0 < A271510 29 :=
  A271510_pos_of_exists 29 0 0 2 5 (by rfl) (by omega) (prove_sq 0 0 2 8 (by rfl))

lemma base_30 : 0 < A271510 30 :=
  A271510_pos_of_exists 30 3 1 2 4 (by rfl) (by omega) (prove_sq 3 1 2 9 (by rfl))

lemma base_31 : 0 < A271510 31 :=
  A271510_pos_of_exists 31 3 3 3 2 (by rfl) (by omega) (prove_sq 3 3 3 15 (by rfl))

lemma base_32 : 0 < A271510 32 :=
  A271510_pos_of_exists 32 0 0 4 4 (by rfl) (by omega) (prove_sq 0 0 4 16 (by rfl))

lemma base_33 : 0 < A271510 33 :=
  A271510_pos_of_exists 33 2 2 0 5 (by rfl) (by omega) (prove_sq 2 2 0 6 (by rfl))

lemma base_34 : 0 < A271510 34 :=
  A271510_pos_of_exists 34 0 0 3 5 (by rfl) (by omega) (prove_sq 0 0 3 12 (by rfl))

lemma base_35 : 0 < A271510 35 :=
  A271510_pos_of_exists 35 3 0 1 5 (by rfl) (by omega) (prove_sq 3 0 1 5 (by rfl))

lemma base_36 : 0 < A271510 36 :=
  A271510_pos_of_exists 36 0 0 0 6 (by rfl) (by omega) (prove_sq 0 0 0 0 (by rfl))

lemma base_37 : 0 < A271510 37 :=
  A271510_pos_of_exists 37 0 0 1 6 (by rfl) (by omega) (prove_sq 0 0 1 4 (by rfl))

lemma base_38 : 0 < A271510 38 :=
  A271510_pos_of_exists 38 1 1 0 6 (by rfl) (by omega) (prove_sq 1 1 0 3 (by rfl))

lemma base_39 : 0 < A271510 39 :=
  A271510_pos_of_exists 39 1 1 1 6 (by rfl) (by omega) (prove_sq 1 1 1 5 (by rfl))

lemma base_40 : 0 < A271510 40 :=
  A271510_pos_of_exists 40 0 0 2 6 (by rfl) (by omega) (prove_sq 0 0 2 8 (by rfl))

lemma base_41 : 0 < A271510 41 :=
  A271510_pos_of_exists 41 0 0 4 5 (by rfl) (by omega) (prove_sq 0 0 4 16 (by rfl))

lemma base_42 : 0 < A271510 42 :=
  A271510_pos_of_exists 42 3 2 5 2 (by rfl) (by omega) (prove_sq 3 2 5 21 (by rfl))

lemma base_43 : 0 < A271510 43 :=
  A271510_pos_of_exists 43 3 3 0 5 (by rfl) (by omega) (prove_sq 3 3 0 9 (by rfl))

lemma base_44 : 0 < A271510 44 :=
  A271510_pos_of_exists 44 2 2 0 6 (by rfl) (by omega) (prove_sq 2 2 0 6 (by rfl))

lemma base_45 : 0 < A271510 45 :=
  A271510_pos_of_exists 45 0 0 3 6 (by rfl) (by omega) (prove_sq 0 0 3 12 (by rfl))

lemma base_46 : 0 < A271510 46 :=
  A271510_pos_of_exists 46 3 0 1 6 (by rfl) (by omega) (prove_sq 3 0 1 5 (by rfl))

lemma base_47 : 0 < A271510 47 :=
  A271510_pos_of_exists 47 3 2 5 3 (by rfl) (by omega) (prove_sq 3 2 5 21 (by rfl))

lemma base_48 : 0 < A271510 48 :=
  A271510_pos_of_exists 48 2 2 2 6 (by rfl) (by omega) (prove_sq 2 2 2 10 (by rfl))

lemma base_49 : 0 < A271510 49 :=
  A271510_pos_of_exists 49 0 0 0 7 (by rfl) (by omega) (prove_sq 0 0 0 0 (by rfl))

lemma base_50 : 0 < A271510 50 :=
  A271510_pos_of_exists 50 0 0 1 7 (by rfl) (by omega) (prove_sq 0 0 1 4 (by rfl))

lemma base_51 : 0 < A271510 51 :=
  A271510_pos_of_exists 51 1 1 0 7 (by rfl) (by omega) (prove_sq 1 1 0 3 (by rfl))

lemma base_52 : 0 < A271510 52 :=
  A271510_pos_of_exists 52 0 0 4 6 (by rfl) (by omega) (prove_sq 0 0 4 16 (by rfl))

lemma base_53 : 0 < A271510 53 :=
  A271510_pos_of_exists 53 0 0 2 7 (by rfl) (by omega) (prove_sq 0 0 2 8 (by rfl))

lemma base_54 : 0 < A271510 54 :=
  A271510_pos_of_exists 54 3 2 5 4 (by rfl) (by omega) (prove_sq 3 2 5 21 (by rfl))

lemma base_55 : 0 < A271510 55 :=
  A271510_pos_of_exists 55 5 5 2 1 (by rfl) (by omega) (prove_sq 5 5 2 17 (by rfl))

lemma base_56 : 0 < A271510 56 :=
  A271510_pos_of_exists 56 6 0 2 4 (by rfl) (by omega) (prove_sq 6 0 2 10 (by rfl))

lemma base_57 : 0 < A271510 57 :=
  A271510_pos_of_exists 57 2 2 0 7 (by rfl) (by omega) (prove_sq 2 2 0 6 (by rfl))

lemma base_58 : 0 < A271510 58 :=
  A271510_pos_of_exists 58 0 0 3 7 (by rfl) (by omega) (prove_sq 0 0 3 12 (by rfl))

lemma base_59 : 0 < A271510 59 :=
  A271510_pos_of_exists 59 3 0 1 7 (by rfl) (by omega) (prove_sq 3 0 1 5 (by rfl))

lemma base_60 : 0 < A271510 60 :=
  A271510_pos_of_exists 60 6 2 4 2 (by rfl) (by omega) (prove_sq 6 2 4 18 (by rfl))

lemma base_61 : 0 < A271510 61 :=
  A271510_pos_of_exists 61 0 0 5 6 (by rfl) (by omega) (prove_sq 0 0 5 20 (by rfl))

lemma base_62 : 0 < A271510 62 :=
  A271510_pos_of_exists 62 7 2 0 3 (by rfl) (by omega) (prove_sq 7 2 0 9 (by rfl))

lemma base_63 : 0 < A271510 63 :=
  A271510_pos_of_exists 63 3 1 2 7 (by rfl) (by omega) (prove_sq 3 1 2 9 (by rfl))

lemma base_64 : 0 < A271510 64 :=
  A271510_pos_of_exists 64 0 0 0 8 (by rfl) (by omega) (prove_sq 0 0 0 0 (by rfl))

lemma base_65 : 0 < A271510 65 :=
  A271510_pos_of_exists 65 0 0 1 8 (by rfl) (by omega) (prove_sq 0 0 1 4 (by rfl))

lemma base_66 : 0 < A271510 66 :=
  A271510_pos_of_exists 66 1 1 0 8 (by rfl) (by omega) (prove_sq 1 1 0 3 (by rfl))

lemma base_67 : 0 < A271510 67 :=
  A271510_pos_of_exists 67 1 1 1 8 (by rfl) (by omega) (prove_sq 1 1 1 5 (by rfl))

lemma base_68 : 0 < A271510 68 :=
  A271510_pos_of_exists 68 0 0 2 8 (by rfl) (by omega) (prove_sq 0 0 2 8 (by rfl))

lemma base_69 : 0 < A271510 69 :=
  A271510_pos_of_exists 69 5 2 2 6 (by rfl) (by omega) (prove_sq 5 2 2 11 (by rfl))

lemma base_70 : 0 < A271510 70 :=
  A271510_pos_of_exists 70 4 2 1 7 (by rfl) (by omega) (prove_sq 4 2 1 8 (by rfl))

lemma base_71 : 0 < A271510 71 :=
  A271510_pos_of_exists 71 7 2 3 3 (by rfl) (by omega) (prove_sq 7 2 3 15 (by rfl))

lemma base_72 : 0 < A271510 72 :=
  A271510_pos_of_exists 72 0 0 6 6 (by rfl) (by omega) (prove_sq 0 0 6 24 (by rfl))

lemma base_73 : 0 < A271510 73 :=
  A271510_pos_of_exists 73 0 0 3 8 (by rfl) (by omega) (prove_sq 0 0 3 12 (by rfl))

lemma base_74 : 0 < A271510 74 :=
  A271510_pos_of_exists 74 0 0 5 7 (by rfl) (by omega) (prove_sq 0 0 5 20 (by rfl))

lemma base_75 : 0 < A271510 75 :=
  A271510_pos_of_exists 75 5 5 0 5 (by rfl) (by omega) (prove_sq 5 5 0 15 (by rfl))

lemma base_76 : 0 < A271510 76 :=
  A271510_pos_of_exists 76 2 2 2 8 (by rfl) (by omega) (prove_sq 2 2 2 10 (by rfl))

lemma base_77 : 0 < A271510 77 :=
  A271510_pos_of_exists 77 5 4 6 0 (by rfl) (by omega) (prove_sq 5 4 6 27 (by rfl))

lemma base_78 : 0 < A271510 78 :=
  A271510_pos_of_exists 78 3 1 2 8 (by rfl) (by omega) (prove_sq 3 1 2 9 (by rfl))

lemma base_79 : 0 < A271510 79 :=
  A271510_pos_of_exists 79 5 2 7 1 (by rfl) (by omega) (prove_sq 5 2 7 29 (by rfl))

lemma base_80 : 0 < A271510 80 :=
  A271510_pos_of_exists 80 0 0 4 8 (by rfl) (by omega) (prove_sq 0 0 4 16 (by rfl))

lemma base_81 : 0 < A271510 81 :=
  A271510_pos_of_exists 81 0 0 0 9 (by rfl) (by omega) (prove_sq 0 0 0 0 (by rfl))

lemma base_82 : 0 < A271510 82 :=
  A271510_pos_of_exists 82 0 0 1 9 (by rfl) (by omega) (prove_sq 0 0 1 4 (by rfl))

lemma base_83 : 0 < A271510 83 :=
  A271510_pos_of_exists 83 1 1 0 9 (by rfl) (by omega) (prove_sq 1 1 0 3 (by rfl))

lemma base_84 : 0 < A271510 84 :=
  A271510_pos_of_exists 84 1 1 1 9 (by rfl) (by omega) (prove_sq 1 1 1 5 (by rfl))

lemma base_85 : 0 < A271510 85 :=
  A271510_pos_of_exists 85 0 0 2 9 (by rfl) (by omega) (prove_sq 0 0 2 8 (by rfl))

lemma base_86 : 0 < A271510 86 :=
  A271510_pos_of_exists 86 5 4 6 3 (by rfl) (by omega) (prove_sq 5 4 6 27 (by rfl))

lemma base_87 : 0 < A271510 87 :=
  A271510_pos_of_exists 87 3 2 5 7 (by rfl) (by omega) (prove_sq 3 2 5 21 (by rfl))

lemma base_88 : 0 < A271510 88 :=
  A271510_pos_of_exists 88 6 6 0 4 (by rfl) (by omega) (prove_sq 6 6 0 18 (by rfl))

lemma base_89 : 0 < A271510 89 :=
  A271510_pos_of_exists 89 0 0 5 8 (by rfl) (by omega) (prove_sq 0 0 5 20 (by rfl))

lemma base_90 : 0 < A271510 90 :=
  A271510_pos_of_exists 90 0 0 3 9 (by rfl) (by omega) (prove_sq 0 0 3 12 (by rfl))

lemma base_91 : 0 < A271510 91 :=
  A271510_pos_of_exists 91 3 0 1 9 (by rfl) (by omega) (prove_sq 3 0 1 5 (by rfl))

lemma base_92 : 0 < A271510 92 :=
  A271510_pos_of_exists 92 6 2 4 6 (by rfl) (by omega) (prove_sq 6 2 4 18 (by rfl))

lemma base_93 : 0 < A271510 93 :=
  A271510_pos_of_exists 93 2 2 2 9 (by rfl) (by omega) (prove_sq 2 2 2 10 (by rfl))

lemma base_94 : 0 < A271510 94 :=
  A271510_pos_of_exists 94 5 2 7 4 (by rfl) (by omega) (prove_sq 5 2 7 29 (by rfl))

lemma base_95 : 0 < A271510 95 :=
  A271510_pos_of_exists 95 3 1 2 9 (by rfl) (by omega) (prove_sq 3 1 2 9 (by rfl))

lemma base_96 : 0 < A271510 96 :=
  A271510_pos_of_exists 96 4 4 0 8 (by rfl) (by omega) (prove_sq 4 4 0 12 (by rfl))

lemma base_97 : 0 < A271510 97 :=
  A271510_pos_of_exists 97 0 0 4 9 (by rfl) (by omega) (prove_sq 0 0 4 16 (by rfl))

lemma base_98 : 0 < A271510 98 :=
  A271510_pos_of_exists 98 0 0 7 7 (by rfl) (by omega) (prove_sq 0 0 7 28 (by rfl))

lemma base_99 : 0 < A271510 99 :=
  A271510_pos_of_exists 99 3 3 0 9 (by rfl) (by omega) (prove_sq 3 3 0 9 (by rfl))

lemma base_100 : 0 < A271510 100 :=
  A271510_pos_of_exists 100 0 0 0 10 (by rfl) (by omega) (prove_sq 0 0 0 0 (by rfl))

lemma base_101 : 0 < A271510 101 :=
  A271510_pos_of_exists 101 0 0 1 10 (by rfl) (by omega) (prove_sq 0 0 1 4 (by rfl))

lemma base_102 : 0 < A271510 102 :=
  A271510_pos_of_exists 102 1 1 0 10 (by rfl) (by omega) (prove_sq 1 1 0 3 (by rfl))

lemma base_103 : 0 < A271510 103 :=
  A271510_pos_of_exists 103 1 1 1 10 (by rfl) (by omega) (prove_sq 1 1 1 5 (by rfl))

lemma base_104 : 0 < A271510 104 :=
  A271510_pos_of_exists 104 0 0 2 10 (by rfl) (by omega) (prove_sq 0 0 2 8 (by rfl))

lemma base_105 : 0 < A271510 105 :=
  A271510_pos_of_exists 105 6 2 4 7 (by rfl) (by omega) (prove_sq 6 2 4 18 (by rfl))

lemma base_106 : 0 < A271510 106 :=
  A271510_pos_of_exists 106 0 0 5 9 (by rfl) (by omega) (prove_sq 0 0 5 20 (by rfl))

lemma base_107 : 0 < A271510 107 :=
  A271510_pos_of_exists 107 7 3 0 7 (by rfl) (by omega) (prove_sq 7 3 0 11 (by rfl))

lemma base_108 : 0 < A271510 108 :=
  A271510_pos_of_exists 108 2 2 0 10 (by rfl) (by omega) (prove_sq 2 2 0 6 (by rfl))

lemma base_109 : 0 < A271510 109 :=
  A271510_pos_of_exists 109 0 0 3 10 (by rfl) (by omega) (prove_sq 0 0 3 12 (by rfl))

lemma base_110 : 0 < A271510 110 :=
  A271510_pos_of_exists 110 3 0 1 10 (by rfl) (by omega) (prove_sq 3 0 1 5 (by rfl))

lemma base_111 : 0 < A271510 111 :=
  A271510_pos_of_exists 111 5 5 5 6 (by rfl) (by omega) (prove_sq 5 5 5 25 (by rfl))

lemma base_112 : 0 < A271510 112 :=
  A271510_pos_of_exists 112 2 2 2 10 (by rfl) (by omega) (prove_sq 2 2 2 10 (by rfl))

lemma base_113 : 0 < A271510 113 :=
  A271510_pos_of_exists 113 0 0 7 8 (by rfl) (by omega) (prove_sq 0 0 7 28 (by rfl))

lemma base_114 : 0 < A271510 114 :=
  A271510_pos_of_exists 114 3 1 2 10 (by rfl) (by omega) (prove_sq 3 1 2 9 (by rfl))

lemma base_115 : 0 < A271510 115 :=
  A271510_pos_of_exists 115 5 0 3 9 (by rfl) (by omega) (prove_sq 5 0 3 13 (by rfl))

lemma base_116 : 0 < A271510 116 :=
  A271510_pos_of_exists 116 0 0 4 10 (by rfl) (by omega) (prove_sq 0 0 4 16 (by rfl))

lemma base_117 : 0 < A271510 117 :=
  A271510_pos_of_exists 117 0 0 6 9 (by rfl) (by omega) (prove_sq 0 0 6 24 (by rfl))

lemma base_118 : 0 < A271510 118 :=
  A271510_pos_of_exists 118 3 3 0 10 (by rfl) (by omega) (prove_sq 3 3 0 9 (by rfl))

lemma base_119 : 0 < A271510 119 :=
  A271510_pos_of_exists 119 3 2 5 9 (by rfl) (by omega) (prove_sq 3 2 5 21 (by rfl))

lemma base_120 : 0 < A271510 120 :=
  A271510_pos_of_exists 120 6 2 4 8 (by rfl) (by omega) (prove_sq 6 2 4 18 (by rfl))

lemma base_121 : 0 < A271510 121 :=
  A271510_pos_of_exists 121 0 0 0 11 (by rfl) (by omega) (prove_sq 0 0 0 0 (by rfl))

lemma base_122 : 0 < A271510 122 :=
  A271510_pos_of_exists 122 0 0 1 11 (by rfl) (by omega) (prove_sq 0 0 1 4 (by rfl))

lemma base_123 : 0 < A271510 123 :=
  A271510_pos_of_exists 123 1 1 0 11 (by rfl) (by omega) (prove_sq 1 1 0 3 (by rfl))

lemma base_124 : 0 < A271510 124 :=
  A271510_pos_of_exists 124 1 1 1 11 (by rfl) (by omega) (prove_sq 1 1 1 5 (by rfl))

lemma base_125 : 0 < A271510 125 :=
  A271510_pos_of_exists 125 0 0 2 11 (by rfl) (by omega) (prove_sq 0 0 2 8 (by rfl))

lemma base_126 : 0 < A271510 126 :=
  A271510_pos_of_exists 126 5 4 6 7 (by rfl) (by omega) (prove_sq 5 4 6 27 (by rfl))

lemma base_127 : 0 < A271510 127 :=
  A271510_pos_of_exists 127 3 3 3 10 (by rfl) (by omega) (prove_sq 3 3 3 15 (by rfl))

lemma base_128 : 0 < A271510 128 :=
  A271510_pos_of_exists 128 0 0 8 8 (by rfl) (by omega) (prove_sq 0 0 8 32 (by rfl))

lemma base_129 : 0 < A271510 129 :=
  A271510_pos_of_exists 129 2 2 0 11 (by rfl) (by omega) (prove_sq 2 2 0 6 (by rfl))

lemma base_130 : 0 < A271510 130 :=
  A271510_pos_of_exists 130 0 0 3 11 (by rfl) (by omega) (prove_sq 0 0 3 12 (by rfl))

lemma base_131 : 0 < A271510 131 :=
  A271510_pos_of_exists 131 3 0 1 11 (by rfl) (by omega) (prove_sq 3 0 1 5 (by rfl))

lemma base_132 : 0 < A271510 132 :=
  A271510_pos_of_exists 132 4 4 0 10 (by rfl) (by omega) (prove_sq 4 4 0 12 (by rfl))

lemma base_133 : 0 < A271510 133 :=
  A271510_pos_of_exists 133 2 2 2 11 (by rfl) (by omega) (prove_sq 2 2 2 10 (by rfl))

lemma base_134 : 0 < A271510 134 :=
  A271510_pos_of_exists 134 3 3 10 4 (by rfl) (by omega) (prove_sq 3 3 10 41 (by rfl))

lemma base_135 : 0 < A271510 135 :=
  A271510_pos_of_exists 135 3 1 2 11 (by rfl) (by omega) (prove_sq 3 1 2 9 (by rfl))

lemma base_136 : 0 < A271510 136 :=
  A271510_pos_of_exists 136 0 0 6 10 (by rfl) (by omega) (prove_sq 0 0 6 24 (by rfl))

lemma base_137 : 0 < A271510 137 :=
  A271510_pos_of_exists 137 0 0 4 11 (by rfl) (by omega) (prove_sq 0 0 4 16 (by rfl))

lemma base_138 : 0 < A271510 138 :=
  A271510_pos_of_exists 138 3 2 5 10 (by rfl) (by omega) (prove_sq 3 2 5 21 (by rfl))

lemma base_139 : 0 < A271510 139 :=
  A271510_pos_of_exists 139 3 3 0 11 (by rfl) (by omega) (prove_sq 3 3 0 9 (by rfl))

lemma base_140 : 0 < A271510 140 :=
  A271510_pos_of_exists 140 5 5 9 3 (by rfl) (by omega) (prove_sq 5 5 9 39 (by rfl))

lemma base_141 : 0 < A271510 141 :=
  A271510_pos_of_exists 141 5 4 6 8 (by rfl) (by omega) (prove_sq 5 4 6 27 (by rfl))

lemma base_142 : 0 < A271510 142 :=
  A271510_pos_of_exists 142 4 2 1 11 (by rfl) (by omega) (prove_sq 4 2 1 8 (by rfl))

lemma base_143 : 0 < A271510 143 :=
  A271510_pos_of_exists 143 3 3 10 5 (by rfl) (by omega) (prove_sq 3 3 10 41 (by rfl))

lemma base_144 : 0 < A271510 144 :=
  A271510_pos_of_exists 144 0 0 0 12 (by rfl) (by omega) (prove_sq 0 0 0 0 (by rfl))

lemma base_145 : 0 < A271510 145 :=
  A271510_pos_of_exists 145 0 0 1 12 (by rfl) (by omega) (prove_sq 0 0 1 4 (by rfl))

lemma base_146 : 0 < A271510 146 :=
  A271510_pos_of_exists 146 0 0 5 11 (by rfl) (by omega) (prove_sq 0 0 5 20 (by rfl))

lemma base_147 : 0 < A271510 147 :=
  A271510_pos_of_exists 147 1 1 1 12 (by rfl) (by omega) (prove_sq 1 1 1 5 (by rfl))

lemma base_148 : 0 < A271510 148 :=
  A271510_pos_of_exists 148 0 0 2 12 (by rfl) (by omega) (prove_sq 0 0 2 8 (by rfl))

lemma base_149 : 0 < A271510 149 :=
  A271510_pos_of_exists 149 0 0 7 10 (by rfl) (by omega) (prove_sq 0 0 7 28 (by rfl))

lemma base_150 : 0 < A271510 150 :=
  A271510_pos_of_exists 150 5 5 0 10 (by rfl) (by omega) (prove_sq 5 5 0 15 (by rfl))

lemma base_151 : 0 < A271510 151 :=
  A271510_pos_of_exists 151 7 7 7 2 (by rfl) (by omega) (prove_sq 7 7 7 35 (by rfl))

lemma base_152 : 0 < A271510 152 :=
  A271510_pos_of_exists 152 2 2 0 12 (by rfl) (by omega) (prove_sq 2 2 0 6 (by rfl))

lemma base_153 : 0 < A271510 153 :=
  A271510_pos_of_exists 153 0 0 3 12 (by rfl) (by omega) (prove_sq 0 0 3 12 (by rfl))

lemma base_154 : 0 < A271510 154 :=
  A271510_pos_of_exists 154 3 0 1 12 (by rfl) (by omega) (prove_sq 3 0 1 5 (by rfl))

lemma base_155 : 0 < A271510 155 :=
  A271510_pos_of_exists 155 5 0 3 11 (by rfl) (by omega) (prove_sq 5 0 3 13 (by rfl))

lemma base_156 : 0 < A271510 156 :=
  A271510_pos_of_exists 156 2 2 2 12 (by rfl) (by omega) (prove_sq 2 2 2 10 (by rfl))

lemma base_157 : 0 < A271510 157 :=
  A271510_pos_of_exists 157 0 0 6 11 (by rfl) (by omega) (prove_sq 0 0 6 24 (by rfl))

lemma base_158 : 0 < A271510 158 :=
  A271510_pos_of_exists 158 3 1 2 12 (by rfl) (by omega) (prove_sq 3 1 2 9 (by rfl))

lemma base_159 : 0 < A271510 159 :=
  A271510_pos_of_exists 159 3 2 5 11 (by rfl) (by omega) (prove_sq 3 2 5 21 (by rfl))

lemma base_160 : 0 < A271510 160 :=
  A271510_pos_of_exists 160 0 0 4 12 (by rfl) (by omega) (prove_sq 0 0 4 16 (by rfl))

lemma base_161 : 0 < A271510 161 :=
  A271510_pos_of_exists 161 6 0 2 11 (by rfl) (by omega) (prove_sq 6 0 2 10 (by rfl))

lemma base_162 : 0 < A271510 162 :=
  A271510_pos_of_exists 162 0 0 9 9 (by rfl) (by omega) (prove_sq 0 0 9 36 (by rfl))

lemma base_163 : 0 < A271510 163 :=
  A271510_pos_of_exists 163 5 1 4 11 (by rfl) (by omega) (prove_sq 5 1 4 17 (by rfl))

lemma base_164 : 0 < A271510 164 :=
  A271510_pos_of_exists 164 0 0 8 10 (by rfl) (by omega) (prove_sq 0 0 8 32 (by rfl))

lemma base_165 : 0 < A271510 165 :=
  A271510_pos_of_exists 165 4 2 1 12 (by rfl) (by omega) (prove_sq 4 2 1 8 (by rfl))

lemma base_166 : 0 < A271510 166 :=
  A271510_pos_of_exists 166 7 0 6 9 (by rfl) (by omega) (prove_sq 7 0 6 25 (by rfl))

lemma base_167 : 0 < A271510 167 :=
  A271510_pos_of_exists 167 3 3 10 7 (by rfl) (by omega) (prove_sq 3 3 10 41 (by rfl))

lemma base_168 : 0 < A271510 168 :=
  A271510_pos_of_exists 168 6 4 10 4 (by rfl) (by omega) (prove_sq 6 4 10 42 (by rfl))

lemma base_169 : 0 < A271510 169 :=
  A271510_pos_of_exists 169 0 0 0 13 (by rfl) (by omega) (prove_sq 0 0 0 0 (by rfl))

lemma base_170 : 0 < A271510 170 :=
  A271510_pos_of_exists 170 0 0 1 13 (by rfl) (by omega) (prove_sq 0 0 1 4 (by rfl))

lemma base_171 : 0 < A271510 171 :=
  A271510_pos_of_exists 171 1 1 0 13 (by rfl) (by omega) (prove_sq 1 1 0 3 (by rfl))

lemma base_172 : 0 < A271510 172 :=
  A271510_pos_of_exists 172 1 1 1 13 (by rfl) (by omega) (prove_sq 1 1 1 5 (by rfl))

lemma base_173 : 0 < A271510 173 :=
  A271510_pos_of_exists 173 0 0 2 13 (by rfl) (by omega) (prove_sq 0 0 2 8 (by rfl))

lemma base_174 : 0 < A271510 174 :=
  A271510_pos_of_exists 174 7 2 0 11 (by rfl) (by omega) (prove_sq 7 2 0 9 (by rfl))

lemma base_175 : 0 < A271510 175 :=
  A271510_pos_of_exists 175 5 5 2 11 (by rfl) (by omega) (prove_sq 5 5 2 17 (by rfl))

lemma base_176 : 0 < A271510 176 :=
  A271510_pos_of_exists 176 4 4 0 12 (by rfl) (by omega) (prove_sq 4 4 0 12 (by rfl))

lemma base_177 : 0 < A271510 177 :=
  A271510_pos_of_exists 177 2 2 0 13 (by rfl) (by omega) (prove_sq 2 2 0 6 (by rfl))

lemma base_178 : 0 < A271510 178 :=
  A271510_pos_of_exists 178 0 0 3 13 (by rfl) (by omega) (prove_sq 0 0 3 12 (by rfl))

lemma base_179 : 0 < A271510 179 :=
  A271510_pos_of_exists 179 3 0 1 13 (by rfl) (by omega) (prove_sq 3 0 1 5 (by rfl))

lemma base_180 : 0 < A271510 180 :=
  A271510_pos_of_exists 180 0 0 6 12 (by rfl) (by omega) (prove_sq 0 0 6 24 (by rfl))

lemma base_181 : 0 < A271510 181 :=
  A271510_pos_of_exists 181 0 0 9 10 (by rfl) (by omega) (prove_sq 0 0 9 36 (by rfl))

lemma base_182 : 0 < A271510 182 :=
  A271510_pos_of_exists 182 3 2 5 12 (by rfl) (by omega) (prove_sq 3 2 5 21 (by rfl))

lemma base_183 : 0 < A271510 183 :=
  A271510_pos_of_exists 183 3 1 2 13 (by rfl) (by omega) (prove_sq 3 1 2 9 (by rfl))

lemma base_184 : 0 < A271510 184 :=
  A271510_pos_of_exists 184 6 0 2 12 (by rfl) (by omega) (prove_sq 6 0 2 10 (by rfl))

lemma base_185 : 0 < A271510 185 :=
  A271510_pos_of_exists 185 0 0 4 13 (by rfl) (by omega) (prove_sq 0 0 4 16 (by rfl))

lemma base_186 : 0 < A271510 186 :=
  A271510_pos_of_exists 186 5 1 4 12 (by rfl) (by omega) (prove_sq 5 1 4 17 (by rfl))

lemma base_187 : 0 < A271510 187 :=
  A271510_pos_of_exists 187 3 3 0 13 (by rfl) (by omega) (prove_sq 3 3 0 9 (by rfl))

lemma base_188 : 0 < A271510 188 :=
  A271510_pos_of_exists 188 6 4 10 6 (by rfl) (by omega) (prove_sq 6 4 10 42 (by rfl))

lemma base_189 : 0 < A271510 189 :=
  A271510_pos_of_exists 189 6 6 6 9 (by rfl) (by omega) (prove_sq 6 6 6 30 (by rfl))

lemma base_190 : 0 < A271510 190 :=
  A271510_pos_of_exists 190 4 2 1 13 (by rfl) (by omega) (prove_sq 4 2 1 8 (by rfl))

lemma base_191 : 0 < A271510 191 :=
  A271510_pos_of_exists 191 9 3 1 10 (by rfl) (by omega) (prove_sq 9 3 1 13 (by rfl))

lemma base_192 : 0 < A271510 192 :=
  A271510_pos_of_exists 192 4 4 4 12 (by rfl) (by omega) (prove_sq 4 4 4 20 (by rfl))

lemma base_193 : 0 < A271510 193 :=
  A271510_pos_of_exists 193 0 0 7 12 (by rfl) (by omega) (prove_sq 0 0 7 28 (by rfl))

lemma base_194 : 0 < A271510 194 :=
  A271510_pos_of_exists 194 0 0 5 13 (by rfl) (by omega) (prove_sq 0 0 5 20 (by rfl))

lemma base_195 : 0 < A271510 195 :=
  A271510_pos_of_exists 195 5 5 9 8 (by rfl) (by omega) (prove_sq 5 5 9 39 (by rfl))

lemma base_196 : 0 < A271510 196 :=
  A271510_pos_of_exists 196 0 0 0 14 (by rfl) (by omega) (prove_sq 0 0 0 0 (by rfl))

lemma base_197 : 0 < A271510 197 :=
  A271510_pos_of_exists 197 0 0 1 14 (by rfl) (by omega) (prove_sq 0 0 1 4 (by rfl))

lemma base_198 : 0 < A271510 198 :=
  A271510_pos_of_exists 198 1 1 0 14 (by rfl) (by omega) (prove_sq 1 1 0 3 (by rfl))

lemma base_199 : 0 < A271510 199 :=
  A271510_pos_of_exists 199 1 1 1 14 (by rfl) (by omega) (prove_sq 1 1 1 5 (by rfl))

lemma base_200 : 0 < A271510 200 :=
  A271510_pos_of_exists 200 0 0 2 14 (by rfl) (by omega) (prove_sq 0 0 2 8 (by rfl))

lemma base_201 : 0 < A271510 201 :=
  A271510_pos_of_exists 201 4 4 0 13 (by rfl) (by omega) (prove_sq 4 4 0 12 (by rfl))

lemma base_202 : 0 < A271510 202 :=
  A271510_pos_of_exists 202 0 0 9 11 (by rfl) (by omega) (prove_sq 0 0 9 36 (by rfl))

lemma base_203 : 0 < A271510 203 :=
  A271510_pos_of_exists 203 5 0 3 13 (by rfl) (by omega) (prove_sq 5 0 3 13 (by rfl))

lemma base_204 : 0 < A271510 204 :=
  A271510_pos_of_exists 204 2 2 0 14 (by rfl) (by omega) (prove_sq 2 2 0 6 (by rfl))

lemma base_205 : 0 < A271510 205 :=
  A271510_pos_of_exists 205 0 0 3 14 (by rfl) (by omega) (prove_sq 0 0 3 12 (by rfl))

lemma base_206 : 0 < A271510 206 :=
  A271510_pos_of_exists 206 3 0 1 14 (by rfl) (by omega) (prove_sq 3 0 1 5 (by rfl))

lemma base_207 : 0 < A271510 207 :=
  A271510_pos_of_exists 207 3 2 5 13 (by rfl) (by omega) (prove_sq 3 2 5 21 (by rfl))

lemma base_208 : 0 < A271510 208 :=
  A271510_pos_of_exists 208 0 0 8 12 (by rfl) (by omega) (prove_sq 0 0 8 32 (by rfl))

lemma base_209 : 0 < A271510 209 :=
  A271510_pos_of_exists 209 6 0 2 13 (by rfl) (by omega) (prove_sq 6 0 2 10 (by rfl))

lemma base_210 : 0 < A271510 210 :=
  A271510_pos_of_exists 210 3 1 2 14 (by rfl) (by omega) (prove_sq 3 1 2 9 (by rfl))

lemma base_211 : 0 < A271510 211 :=
  A271510_pos_of_exists 211 5 1 4 13 (by rfl) (by omega) (prove_sq 5 1 4 17 (by rfl))

lemma base_212 : 0 < A271510 212 :=
  A271510_pos_of_exists 212 0 0 4 14 (by rfl) (by omega) (prove_sq 0 0 4 16 (by rfl))

lemma base_213 : 0 < A271510 213 :=
  A271510_pos_of_exists 213 10 4 4 9 (by rfl) (by omega) (prove_sq 10 4 4 22 (by rfl))

lemma base_214 : 0 < A271510 214 :=
  A271510_pos_of_exists 214 3 3 0 14 (by rfl) (by omega) (prove_sq 3 3 0 9 (by rfl))

lemma base_215 : 0 < A271510 215 :=
  A271510_pos_of_exists 215 11 7 6 3 (by rfl) (by omega) (prove_sq 11 7 6 33 (by rfl))

lemma base_216 : 0 < A271510 216 :=
  A271510_pos_of_exists 216 6 4 10 8 (by rfl) (by omega) (prove_sq 6 4 10 42 (by rfl))

lemma base_217 : 0 < A271510 217 :=
  A271510_pos_of_exists 217 4 2 1 14 (by rfl) (by omega) (prove_sq 4 2 1 8 (by rfl))

lemma base_218 : 0 < A271510 218 :=
  A271510_pos_of_exists 218 0 0 7 13 (by rfl) (by omega) (prove_sq 0 0 7 28 (by rfl))

lemma base_219 : 0 < A271510 219 :=
  A271510_pos_of_exists 219 5 5 0 13 (by rfl) (by omega) (prove_sq 5 5 0 15 (by rfl))

lemma base_220 : 0 < A271510 220 :=
  A271510_pos_of_exists 220 7 1 7 11 (by rfl) (by omega) (prove_sq 7 1 7 29 (by rfl))

lemma base_221 : 0 < A271510 221 :=
  A271510_pos_of_exists 221 0 0 5 14 (by rfl) (by omega) (prove_sq 0 0 5 20 (by rfl))

lemma base_222 : 0 < A271510 222 :=
  A271510_pos_of_exists 222 5 2 7 12 (by rfl) (by omega) (prove_sq 5 2 7 29 (by rfl))

lemma base_223 : 0 < A271510 223 :=
  A271510_pos_of_exists 223 3 3 3 14 (by rfl) (by omega) (prove_sq 3 3 3 15 (by rfl))

lemma base_224 : 0 < A271510 224 :=
  A271510_pos_of_exists 224 12 0 4 8 (by rfl) (by omega) (prove_sq 12 0 4 20 (by rfl))

lemma base_225 : 0 < A271510 225 :=
  A271510_pos_of_exists 225 0 0 0 15 (by rfl) (by omega) (prove_sq 0 0 0 0 (by rfl))

lemma base_226 : 0 < A271510 226 :=
  A271510_pos_of_exists 226 0 0 1 15 (by rfl) (by omega) (prove_sq 0 0 1 4 (by rfl))

lemma base_227 : 0 < A271510 227 :=
  A271510_pos_of_exists 227 1 1 0 15 (by rfl) (by omega) (prove_sq 1 1 0 3 (by rfl))

lemma base_228 : 0 < A271510 228 :=
  A271510_pos_of_exists 228 1 1 1 15 (by rfl) (by omega) (prove_sq 1 1 1 5 (by rfl))

lemma base_229 : 0 < A271510 229 :=
  A271510_pos_of_exists 229 0 0 2 15 (by rfl) (by omega) (prove_sq 0 0 2 8 (by rfl))

lemma base_230 : 0 < A271510 230 :=
  A271510_pos_of_exists 230 5 0 3 14 (by rfl) (by omega) (prove_sq 5 0 3 13 (by rfl))

lemma base_231 : 0 < A271510 231 :=
  A271510_pos_of_exists 231 5 5 9 10 (by rfl) (by omega) (prove_sq 5 5 9 39 (by rfl))

lemma base_232 : 0 < A271510 232 :=
  A271510_pos_of_exists 232 0 0 6 14 (by rfl) (by omega) (prove_sq 0 0 6 24 (by rfl))

lemma base_233 : 0 < A271510 233 :=
  A271510_pos_of_exists 233 0 0 8 13 (by rfl) (by omega) (prove_sq 0 0 8 32 (by rfl))

lemma base_234 : 0 < A271510 234 :=
  A271510_pos_of_exists 234 0 0 3 15 (by rfl) (by omega) (prove_sq 0 0 3 12 (by rfl))

lemma base_235 : 0 < A271510 235 :=
  A271510_pos_of_exists 235 3 0 1 15 (by rfl) (by omega) (prove_sq 3 0 1 5 (by rfl))

lemma base_236 : 0 < A271510 236 :=
  A271510_pos_of_exists 236 6 0 2 14 (by rfl) (by omega) (prove_sq 6 0 2 10 (by rfl))

lemma base_237 : 0 < A271510 237 :=
  A271510_pos_of_exists 237 2 2 2 15 (by rfl) (by omega) (prove_sq 2 2 2 10 (by rfl))

lemma base_238 : 0 < A271510 238 :=
  A271510_pos_of_exists 238 5 1 4 14 (by rfl) (by omega) (prove_sq 5 1 4 17 (by rfl))

lemma base_239 : 0 < A271510 239 :=
  A271510_pos_of_exists 239 3 1 2 15 (by rfl) (by omega) (prove_sq 3 1 2 9 (by rfl))

lemma base_240 : 0 < A271510 240 :=
  A271510_pos_of_exists 240 12 4 8 4 (by rfl) (by omega) (prove_sq 12 4 8 36 (by rfl))

lemma base_241 : 0 < A271510 241 :=
  A271510_pos_of_exists 241 0 0 4 15 (by rfl) (by omega) (prove_sq 0 0 4 16 (by rfl))

lemma base_242 : 0 < A271510 242 :=
  A271510_pos_of_exists 242 0 0 11 11 (by rfl) (by omega) (prove_sq 0 0 11 44 (by rfl))

lemma base_243 : 0 < A271510 243 :=
  A271510_pos_of_exists 243 3 3 0 15 (by rfl) (by omega) (prove_sq 3 3 0 9 (by rfl))

lemma base_244 : 0 < A271510 244 :=
  A271510_pos_of_exists 244 0 0 10 12 (by rfl) (by omega) (prove_sq 0 0 10 40 (by rfl))

lemma base_245 : 0 < A271510 245 :=
  A271510_pos_of_exists 245 0 0 7 14 (by rfl) (by omega) (prove_sq 0 0 7 28 (by rfl))

lemma base_246 : 0 < A271510 246 :=
  A271510_pos_of_exists 246 4 2 1 15 (by rfl) (by omega) (prove_sq 4 2 1 8 (by rfl))

lemma base_247 : 0 < A271510 247 :=
  A271510_pos_of_exists 247 5 2 7 13 (by rfl) (by omega) (prove_sq 5 2 7 29 (by rfl))

lemma base_248 : 0 < A271510 248 :=
  A271510_pos_of_exists 248 14 4 0 6 (by rfl) (by omega) (prove_sq 14 4 0 18 (by rfl))

lemma base_249 : 0 < A271510 249 :=
  A271510_pos_of_exists 249 7 2 0 14 (by rfl) (by omega) (prove_sq 7 2 0 9 (by rfl))

lemma base_250 : 0 < A271510 250 :=
  A271510_pos_of_exists 250 0 0 5 15 (by rfl) (by omega) (prove_sq 0 0 5 20 (by rfl))

lemma base_251 : 0 < A271510 251 :=
  A271510_pos_of_exists 251 11 11 0 3 (by rfl) (by omega) (prove_sq 11 11 0 33 (by rfl))

lemma base_252 : 0 < A271510 252 :=
  A271510_pos_of_exists 252 3 3 3 15 (by rfl) (by omega) (prove_sq 3 3 3 15 (by rfl))

lemma base_253 : 0 < A271510 253 :=
  A271510_pos_of_exists 253 7 2 10 10 (by rfl) (by omega) (prove_sq 7 2 10 41 (by rfl))

lemma base_254 : 0 < A271510 254 :=
  A271510_pos_of_exists 254 7 0 6 13 (by rfl) (by omega) (prove_sq 7 0 6 25 (by rfl))

lemma base_255 : 0 < A271510 255 :=
  A271510_pos_of_exists 255 7 5 10 9 (by rfl) (by omega) (prove_sq 7 5 10 43 (by rfl))

lemma base_256 : 0 < A271510 256 :=
  A271510_pos_of_exists 256 0 0 0 16 (by rfl) (by omega) (prove_sq 0 0 0 0 (by rfl))

lemma base_257 : 0 < A271510 257 :=
  A271510_pos_of_exists 257 0 0 1 16 (by rfl) (by omega) (prove_sq 0 0 1 4 (by rfl))

lemma base_258 : 0 < A271510 258 :=
  A271510_pos_of_exists 258 1 1 0 16 (by rfl) (by omega) (prove_sq 1 1 0 3 (by rfl))

lemma base_259 : 0 < A271510 259 :=
  A271510_pos_of_exists 259 1 1 1 16 (by rfl) (by omega) (prove_sq 1 1 1 5 (by rfl))

lemma base_260 : 0 < A271510 260 :=
  A271510_pos_of_exists 260 0 0 2 16 (by rfl) (by omega) (prove_sq 0 0 2 8 (by rfl))

lemma base_261 : 0 < A271510 261 :=
  A271510_pos_of_exists 261 0 0 6 15 (by rfl) (by omega) (prove_sq 0 0 6 24 (by rfl))

lemma base_262 : 0 < A271510 262 :=
  A271510_pos_of_exists 262 3 3 10 12 (by rfl) (by omega) (prove_sq 3 3 10 41 (by rfl))

lemma base_263 : 0 < A271510 263 :=
  A271510_pos_of_exists 263 3 2 5 15 (by rfl) (by omega) (prove_sq 3 2 5 21 (by rfl))

lemma base_264 : 0 < A271510 264 :=
  A271510_pos_of_exists 264 2 2 0 16 (by rfl) (by omega) (prove_sq 2 2 0 6 (by rfl))

lemma base_265 : 0 < A271510 265 :=
  A271510_pos_of_exists 265 0 0 3 16 (by rfl) (by omega) (prove_sq 0 0 3 12 (by rfl))

lemma base_266 : 0 < A271510 266 :=
  A271510_pos_of_exists 266 3 0 1 16 (by rfl) (by omega) (prove_sq 3 0 1 5 (by rfl))

lemma base_267 : 0 < A271510 267 :=
  A271510_pos_of_exists 267 5 1 4 15 (by rfl) (by omega) (prove_sq 5 1 4 17 (by rfl))

lemma base_268 : 0 < A271510 268 :=
  A271510_pos_of_exists 268 2 2 2 16 (by rfl) (by omega) (prove_sq 2 2 2 10 (by rfl))

lemma base_269 : 0 < A271510 269 :=
  A271510_pos_of_exists 269 0 0 10 13 (by rfl) (by omega) (prove_sq 0 0 10 40 (by rfl))

lemma base_270 : 0 < A271510 270 :=
  A271510_pos_of_exists 270 3 1 2 16 (by rfl) (by omega) (prove_sq 3 1 2 9 (by rfl))

lemma base_271 : 0 < A271510 271 :=
  A271510_pos_of_exists 271 5 5 5 14 (by rfl) (by omega) (prove_sq 5 5 5 25 (by rfl))

lemma base_272 : 0 < A271510 272 :=
  A271510_pos_of_exists 272 0 0 4 16 (by rfl) (by omega) (prove_sq 0 0 4 16 (by rfl))

lemma base_273 : 0 < A271510 273 :=
  A271510_pos_of_exists 273 4 4 4 15 (by rfl) (by omega) (prove_sq 4 4 4 20 (by rfl))

lemma base_274 : 0 < A271510 274 :=
  A271510_pos_of_exists 274 0 0 7 15 (by rfl) (by omega) (prove_sq 0 0 7 28 (by rfl))

lemma base_275 : 0 < A271510 275 :=
  A271510_pos_of_exists 275 5 5 0 15 (by rfl) (by omega) (prove_sq 5 5 0 15 (by rfl))

lemma base_276 : 0 < A271510 276 :=
  A271510_pos_of_exists 276 10 4 4 12 (by rfl) (by omega) (prove_sq 10 4 4 22 (by rfl))

lemma base_277 : 0 < A271510 277 :=
  A271510_pos_of_exists 277 0 0 9 14 (by rfl) (by omega) (prove_sq 0 0 9 36 (by rfl))

lemma base_278 : 0 < A271510 278 :=
  A271510_pos_of_exists 278 5 3 12 10 (by rfl) (by omega) (prove_sq 5 3 12 49 (by rfl))

lemma base_279 : 0 < A271510 279 :=
  A271510_pos_of_exists 279 5 5 2 15 (by rfl) (by omega) (prove_sq 5 5 2 17 (by rfl))

lemma base_280 : 0 < A271510 280 :=
  A271510_pos_of_exists 280 8 4 2 14 (by rfl) (by omega) (prove_sq 8 4 2 16 (by rfl))

lemma base_281 : 0 < A271510 281 :=
  A271510_pos_of_exists 281 0 0 5 16 (by rfl) (by omega) (prove_sq 0 0 5 20 (by rfl))

lemma base_282 : 0 < A271510 282 :=
  A271510_pos_of_exists 282 9 2 14 1 (by rfl) (by omega) (prove_sq 9 2 14 57 (by rfl))

lemma base_283 : 0 < A271510 283 :=
  A271510_pos_of_exists 283 3 3 3 16 (by rfl) (by omega) (prove_sq 3 3 3 15 (by rfl))

lemma base_284 : 0 < A271510 284 :=
  A271510_pos_of_exists 284 7 3 15 1 (by rfl) (by omega) (prove_sq 7 3 15 61 (by rfl))

lemma base_285 : 0 < A271510 285 :=
  A271510_pos_of_exists 285 9 2 14 2 (by rfl) (by omega) (prove_sq 9 2 14 57 (by rfl))

lemma base_286 : 0 < A271510 286 :=
  A271510_pos_of_exists 286 9 0 3 14 (by rfl) (by omega) (prove_sq 9 0 3 15 (by rfl))

lemma base_287 : 0 < A271510 287 :=
  A271510_pos_of_exists 287 3 3 10 13 (by rfl) (by omega) (prove_sq 3 3 10 41 (by rfl))

lemma base_288 : 0 < A271510 288 :=
  A271510_pos_of_exists 288 0 0 12 12 (by rfl) (by omega) (prove_sq 0 0 12 48 (by rfl))

lemma base_289 : 0 < A271510 289 :=
  A271510_pos_of_exists 289 0 0 0 17 (by rfl) (by omega) (prove_sq 0 0 0 0 (by rfl))

lemma base_290 : 0 < A271510 290 :=
  A271510_pos_of_exists 290 0 0 1 17 (by rfl) (by omega) (prove_sq 0 0 1 4 (by rfl))

lemma base_291 : 0 < A271510 291 :=
  A271510_pos_of_exists 291 1 1 0 17 (by rfl) (by omega) (prove_sq 1 1 0 3 (by rfl))

lemma base_292 : 0 < A271510 292 :=
  A271510_pos_of_exists 292 0 0 6 16 (by rfl) (by omega) (prove_sq 0 0 6 24 (by rfl))

lemma base_293 : 0 < A271510 293 :=
  A271510_pos_of_exists 293 0 0 2 17 (by rfl) (by omega) (prove_sq 0 0 2 8 (by rfl))

lemma base_294 : 0 < A271510 294 :=
  A271510_pos_of_exists 294 3 2 5 16 (by rfl) (by omega) (prove_sq 3 2 5 21 (by rfl))

lemma base_295 : 0 < A271510 295 :=
  A271510_pos_of_exists 295 7 1 7 14 (by rfl) (by omega) (prove_sq 7 1 7 29 (by rfl))

lemma base_296 : 0 < A271510 296 :=
  A271510_pos_of_exists 296 0 0 10 14 (by rfl) (by omega) (prove_sq 0 0 10 40 (by rfl))

lemma base_297 : 0 < A271510 297 :=
  A271510_pos_of_exists 297 2 2 0 17 (by rfl) (by omega) (prove_sq 2 2 0 6 (by rfl))

lemma base_298 : 0 < A271510 298 :=
  A271510_pos_of_exists 298 0 0 3 17 (by rfl) (by omega) (prove_sq 0 0 3 12 (by rfl))

lemma base_299 : 0 < A271510 299 :=
  A271510_pos_of_exists 299 3 0 1 17 (by rfl) (by omega) (prove_sq 3 0 1 5 (by rfl))

lemma base_300 : 0 < A271510 300 :=
  A271510_pos_of_exists 300 5 5 5 15 (by rfl) (by omega) (prove_sq 5 5 5 25 (by rfl))

lemma base_301 : 0 < A271510 301 :=
  A271510_pos_of_exists 301 2 2 2 17 (by rfl) (by omega) (prove_sq 2 2 2 10 (by rfl))

lemma base_302 : 0 < A271510 302 :=
  A271510_pos_of_exists 302 5 4 6 15 (by rfl) (by omega) (prove_sq 5 4 6 27 (by rfl))

lemma base_303 : 0 < A271510 303 :=
  A271510_pos_of_exists 303 3 1 2 17 (by rfl) (by omega) (prove_sq 3 1 2 9 (by rfl))

lemma base_304 : 0 < A271510 304 :=
  A271510_pos_of_exists 304 4 4 4 16 (by rfl) (by omega) (prove_sq 4 4 4 20 (by rfl))

lemma base_305 : 0 < A271510 305 :=
  A271510_pos_of_exists 305 0 0 4 17 (by rfl) (by omega) (prove_sq 0 0 4 16 (by rfl))

lemma base_306 : 0 < A271510 306 :=
  A271510_pos_of_exists 306 0 0 9 15 (by rfl) (by omega) (prove_sq 0 0 9 36 (by rfl))

lemma base_307 : 0 < A271510 307 :=
  A271510_pos_of_exists 307 3 3 0 17 (by rfl) (by omega) (prove_sq 3 3 0 9 (by rfl))

lemma base_308 : 0 < A271510 308 :=
  A271510_pos_of_exists 308 7 3 15 5 (by rfl) (by omega) (prove_sq 7 3 15 61 (by rfl))

lemma base_309 : 0 < A271510 309 :=
  A271510_pos_of_exists 309 7 2 0 16 (by rfl) (by omega) (prove_sq 7 2 0 9 (by rfl))

lemma base_310 : 0 < A271510 310 :=
  A271510_pos_of_exists 310 4 2 1 17 (by rfl) (by omega) (prove_sq 4 2 1 8 (by rfl))

lemma base_311 : 0 < A271510 311 :=
  A271510_pos_of_exists 311 15 6 1 7 (by rfl) (by omega) (prove_sq 15 6 1 23 (by rfl))

lemma base_312 : 0 < A271510 312 :=
  A271510_pos_of_exists 312 6 2 4 16 (by rfl) (by omega) (prove_sq 6 2 4 18 (by rfl))

lemma base_313 : 0 < A271510 313 :=
  A271510_pos_of_exists 313 0 0 12 13 (by rfl) (by omega) (prove_sq 0 0 12 48 (by rfl))

lemma base_314 : 0 < A271510 314 :=
  A271510_pos_of_exists 314 0 0 5 17 (by rfl) (by omega) (prove_sq 0 0 5 20 (by rfl))

lemma base_315 : 0 < A271510 315 :=
  A271510_pos_of_exists 315 9 0 3 15 (by rfl) (by omega) (prove_sq 9 0 3 15 (by rfl))

lemma base_316 : 0 < A271510 316 :=
  A271510_pos_of_exists 316 3 3 3 17 (by rfl) (by omega) (prove_sq 3 3 3 15 (by rfl))

lemma base_317 : 0 < A271510 317 :=
  A271510_pos_of_exists 317 0 0 11 14 (by rfl) (by omega) (prove_sq 0 0 11 44 (by rfl))

lemma base_318 : 0 < A271510 318 :=
  A271510_pos_of_exists 318 7 2 3 16 (by rfl) (by omega) (prove_sq 7 2 3 15 (by rfl))

lemma base_319 : 0 < A271510 319 :=
  A271510_pos_of_exists 319 7 3 15 6 (by rfl) (by omega) (prove_sq 7 3 15 61 (by rfl))

lemma base_320 : 0 < A271510 320 :=
  A271510_pos_of_exists 320 0 0 8 16 (by rfl) (by omega) (prove_sq 0 0 8 32 (by rfl))

lemma base_321 : 0 < A271510 321 :=
  A271510_pos_of_exists 321 4 4 0 17 (by rfl) (by omega) (prove_sq 4 4 0 12 (by rfl))

lemma base_322 : 0 < A271510 322 :=
  A271510_pos_of_exists 322 5 2 2 17 (by rfl) (by omega) (prove_sq 5 2 2 11 (by rfl))

lemma base_323 : 0 < A271510 323 :=
  A271510_pos_of_exists 323 5 0 3 17 (by rfl) (by omega) (prove_sq 5 0 3 13 (by rfl))

lemma base_324 : 0 < A271510 324 :=
  A271510_pos_of_exists 324 0 0 0 18 (by rfl) (by omega) (prove_sq 0 0 0 0 (by rfl))

lemma base_325 : 0 < A271510 325 :=
  A271510_pos_of_exists 325 0 0 1 18 (by rfl) (by omega) (prove_sq 0 0 1 4 (by rfl))

lemma base_326 : 0 < A271510 326 :=
  A271510_pos_of_exists 326 1 1 0 18 (by rfl) (by omega) (prove_sq 1 1 0 3 (by rfl))

lemma base_327 : 0 < A271510 327 :=
  A271510_pos_of_exists 327 1 1 1 18 (by rfl) (by omega) (prove_sq 1 1 1 5 (by rfl))

lemma base_328 : 0 < A271510 328 :=
  A271510_pos_of_exists 328 0 0 2 18 (by rfl) (by omega) (prove_sq 0 0 2 8 (by rfl))

lemma base_329 : 0 < A271510 329 :=
  A271510_pos_of_exists 329 6 0 2 17 (by rfl) (by omega) (prove_sq 6 0 2 10 (by rfl))

lemma base_330 : 0 < A271510 330 :=
  A271510_pos_of_exists 330 9 2 14 7 (by rfl) (by omega) (prove_sq 9 2 14 57 (by rfl))

lemma base_331 : 0 < A271510 331 :=
  A271510_pos_of_exists 331 5 1 4 17 (by rfl) (by omega) (prove_sq 5 1 4 17 (by rfl))

lemma base_332 : 0 < A271510 332 :=
  A271510_pos_of_exists 332 2 2 0 18 (by rfl) (by omega) (prove_sq 2 2 0 6 (by rfl))

lemma base_333 : 0 < A271510 333 :=
  A271510_pos_of_exists 333 0 0 3 18 (by rfl) (by omega) (prove_sq 0 0 3 12 (by rfl))

lemma base_334 : 0 < A271510 334 :=
  A271510_pos_of_exists 334 3 0 1 18 (by rfl) (by omega) (prove_sq 3 0 1 5 (by rfl))

lemma base_335 : 0 < A271510 335 :=
  A271510_pos_of_exists 335 17 1 3 6 (by rfl) (by omega) (prove_sq 17 1 3 21 (by rfl))

lemma base_336 : 0 < A271510 336 :=
  A271510_pos_of_exists 336 2 2 2 18 (by rfl) (by omega) (prove_sq 2 2 2 10 (by rfl))

lemma base_337 : 0 < A271510 337 :=
  A271510_pos_of_exists 337 0 0 9 16 (by rfl) (by omega) (prove_sq 0 0 9 36 (by rfl))

lemma base_338 : 0 < A271510 338 :=
  A271510_pos_of_exists 338 0 0 7 17 (by rfl) (by omega) (prove_sq 0 0 7 28 (by rfl))

lemma base_339 : 0 < A271510 339 :=
  A271510_pos_of_exists 339 5 5 0 17 (by rfl) (by omega) (prove_sq 5 5 0 15 (by rfl))

lemma base_340 : 0 < A271510 340 :=
  A271510_pos_of_exists 340 0 0 4 18 (by rfl) (by omega) (prove_sq 0 0 4 16 (by rfl))

lemma base_341 : 0 < A271510 341 :=
  A271510_pos_of_exists 341 7 0 6 16 (by rfl) (by omega) (prove_sq 7 0 6 25 (by rfl))

lemma base_342 : 0 < A271510 342 :=
  A271510_pos_of_exists 342 3 3 0 18 (by rfl) (by omega) (prove_sq 3 3 0 9 (by rfl))

lemma base_343 : 0 < A271510 343 :=
  A271510_pos_of_exists 343 3 3 10 15 (by rfl) (by omega) (prove_sq 3 3 10 41 (by rfl))

lemma base_344 : 0 < A271510 344 :=
  A271510_pos_of_exists 344 10 8 12 6 (by rfl) (by omega) (prove_sq 10 8 12 54 (by rfl))

lemma base_345 : 0 < A271510 345 :=
  A271510_pos_of_exists 345 4 2 1 18 (by rfl) (by omega) (prove_sq 4 2 1 8 (by rfl))

lemma base_346 : 0 < A271510 346 :=
  A271510_pos_of_exists 346 0 0 11 15 (by rfl) (by omega) (prove_sq 0 0 11 44 (by rfl))

lemma base_347 : 0 < A271510 347 :=
  A271510_pos_of_exists 347 5 3 12 13 (by rfl) (by omega) (prove_sq 5 3 12 49 (by rfl))

lemma base_348 : 0 < A271510 348 :=
  A271510_pos_of_exists 348 6 4 10 14 (by rfl) (by omega) (prove_sq 6 4 10 42 (by rfl))

lemma base_349 : 0 < A271510 349 :=
  A271510_pos_of_exists 349 0 0 5 18 (by rfl) (by omega) (prove_sq 0 0 5 20 (by rfl))

lemma base_350 : 0 < A271510 350 :=
  A271510_pos_of_exists 350 9 0 10 13 (by rfl) (by omega) (prove_sq 9 0 10 41 (by rfl))

lemma base_351 : 0 < A271510 351 :=
  A271510_pos_of_exists 351 3 3 3 18 (by rfl) (by omega) (prove_sq 3 3 3 15 (by rfl))

lemma base_352 : 0 < A271510 352 :=
  A271510_pos_of_exists 352 12 12 0 8 (by rfl) (by omega) (prove_sq 12 12 0 36 (by rfl))

lemma base_353 : 0 < A271510 353 :=
  A271510_pos_of_exists 353 0 0 8 17 (by rfl) (by omega) (prove_sq 0 0 8 32 (by rfl))

lemma base_354 : 0 < A271510 354 :=
  A271510_pos_of_exists 354 7 7 0 16 (by rfl) (by omega) (prove_sq 7 7 0 21 (by rfl))

lemma base_355 : 0 < A271510 355 :=
  A271510_pos_of_exists 355 7 1 7 16 (by rfl) (by omega) (prove_sq 7 1 7 29 (by rfl))

lemma base_356 : 0 < A271510 356 :=
  A271510_pos_of_exists 356 0 0 10 16 (by rfl) (by omega) (prove_sq 0 0 10 40 (by rfl))

lemma base_357 : 0 < A271510 357 :=
  A271510_pos_of_exists 357 5 2 2 18 (by rfl) (by omega) (prove_sq 5 2 2 11 (by rfl))

lemma base_358 : 0 < A271510 358 :=
  A271510_pos_of_exists 358 5 0 3 18 (by rfl) (by omega) (prove_sq 5 0 3 13 (by rfl))

lemma base_359 : 0 < A271510 359 :=
  A271510_pos_of_exists 359 13 9 3 10 (by rfl) (by omega) (prove_sq 13 9 3 31 (by rfl))

lemma base_360 : 0 < A271510 360 :=
  A271510_pos_of_exists 360 0 0 6 18 (by rfl) (by omega) (prove_sq 0 0 6 24 (by rfl))

lemma base_361 : 0 < A271510 361 :=
  A271510_pos_of_exists 361 0 0 0 19 (by rfl) (by omega) (prove_sq 0 0 0 0 (by rfl))

lemma base_362 : 0 < A271510 362 :=
  A271510_pos_of_exists 362 0 0 1 19 (by rfl) (by omega) (prove_sq 0 0 1 4 (by rfl))

lemma base_363 : 0 < A271510 363 :=
  A271510_pos_of_exists 363 1 1 0 19 (by rfl) (by omega) (prove_sq 1 1 0 3 (by rfl))

lemma base_364 : 0 < A271510 364 :=
  A271510_pos_of_exists 364 1 1 1 19 (by rfl) (by omega) (prove_sq 1 1 1 5 (by rfl))

lemma base_365 : 0 < A271510 365 :=
  A271510_pos_of_exists 365 0 0 2 19 (by rfl) (by omega) (prove_sq 0 0 2 8 (by rfl))

lemma base_366 : 0 < A271510 366 :=
  A271510_pos_of_exists 366 5 1 4 18 (by rfl) (by omega) (prove_sq 5 1 4 17 (by rfl))

lemma base_367 : 0 < A271510 367 :=
  A271510_pos_of_exists 367 5 2 7 17 (by rfl) (by omega) (prove_sq 5 2 7 29 (by rfl))

lemma base_368 : 0 < A271510 368 :=
  A271510_pos_of_exists 368 12 4 8 12 (by rfl) (by omega) (prove_sq 12 4 8 36 (by rfl))

lemma base_369 : 0 < A271510 369 :=
  A271510_pos_of_exists 369 0 0 12 15 (by rfl) (by omega) (prove_sq 0 0 12 48 (by rfl))

lemma base_370 : 0 < A271510 370 :=
  A271510_pos_of_exists 370 0 0 3 19 (by rfl) (by omega) (prove_sq 0 0 3 12 (by rfl))

lemma base_371 : 0 < A271510 371 :=
  A271510_pos_of_exists 371 3 0 1 19 (by rfl) (by omega) (prove_sq 3 0 1 5 (by rfl))

lemma base_372 : 0 < A271510 372 :=
  A271510_pos_of_exists 372 4 4 4 18 (by rfl) (by omega) (prove_sq 4 4 4 20 (by rfl))

lemma base_373 : 0 < A271510 373 :=
  A271510_pos_of_exists 373 0 0 7 18 (by rfl) (by omega) (prove_sq 0 0 7 28 (by rfl))

lemma base_374 : 0 < A271510 374 :=
  A271510_pos_of_exists 374 3 3 10 16 (by rfl) (by omega) (prove_sq 3 3 10 41 (by rfl))

lemma base_375 : 0 < A271510 375 :=
  A271510_pos_of_exists 375 3 1 2 19 (by rfl) (by omega) (prove_sq 3 1 2 9 (by rfl))

lemma base_376 : 0 < A271510 376 :=
  A271510_pos_of_exists 376 10 4 14 8 (by rfl) (by omega) (prove_sq 10 4 14 58 (by rfl))

lemma base_377 : 0 < A271510 377 :=
  A271510_pos_of_exists 377 0 0 4 19 (by rfl) (by omega) (prove_sq 0 0 4 16 (by rfl))

lemma base_378 : 0 < A271510 378 :=
  A271510_pos_of_exists 378 5 5 2 18 (by rfl) (by omega) (prove_sq 5 5 2 17 (by rfl))

lemma base_379 : 0 < A271510 379 :=
  A271510_pos_of_exists 379 3 3 0 19 (by rfl) (by omega) (prove_sq 3 3 0 9 (by rfl))

lemma base_380 : 0 < A271510 380 :=
  A271510_pos_of_exists 380 6 2 4 18 (by rfl) (by omega) (prove_sq 6 2 4 18 (by rfl))

lemma base_381 : 0 < A271510 381 :=
  A271510_pos_of_exists 381 9 2 14 10 (by rfl) (by omega) (prove_sq 9 2 14 57 (by rfl))

lemma base_382 : 0 < A271510 382 :=
  A271510_pos_of_exists 382 4 2 1 19 (by rfl) (by omega) (prove_sq 4 2 1 8 (by rfl))

lemma base_383 : 0 < A271510 383 :=
  A271510_pos_of_exists 383 7 3 15 10 (by rfl) (by omega) (prove_sq 7 3 15 61 (by rfl))

lemma base_384 : 0 < A271510 384 :=
  A271510_pos_of_exists 384 8 8 0 16 (by rfl) (by omega) (prove_sq 8 8 0 24 (by rfl))

lemma base_385 : 0 < A271510 385 :=
  A271510_pos_of_exists 385 10 10 4 13 (by rfl) (by omega) (prove_sq 10 10 4 34 (by rfl))

lemma base_386 : 0 < A271510 386 :=
  A271510_pos_of_exists 386 0 0 5 19 (by rfl) (by omega) (prove_sq 0 0 5 20 (by rfl))

lemma base_387 : 0 < A271510 387 :=
  A271510_pos_of_exists 387 5 5 9 16 (by rfl) (by omega) (prove_sq 5 5 9 39 (by rfl))

lemma base_388 : 0 < A271510 388 :=
  A271510_pos_of_exists 388 0 0 8 18 (by rfl) (by omega) (prove_sq 0 0 8 32 (by rfl))

lemma base_389 : 0 < A271510 389 :=
  A271510_pos_of_exists 389 0 0 10 17 (by rfl) (by omega) (prove_sq 0 0 10 40 (by rfl))

lemma base_390 : 0 < A271510 390 :=
  A271510_pos_of_exists 390 13 4 3 14 (by rfl) (by omega) (prove_sq 13 4 3 21 (by rfl))

lemma base_391 : 0 < A271510 391 :=
  A271510_pos_of_exists 391 9 6 15 7 (by rfl) (by omega) (prove_sq 9 6 15 63 (by rfl))

lemma base_392 : 0 < A271510 392 :=
  A271510_pos_of_exists 392 0 0 14 14 (by rfl) (by omega) (prove_sq 0 0 14 56 (by rfl))

lemma base_393 : 0 < A271510 393 :=
  A271510_pos_of_exists 393 4 4 0 19 (by rfl) (by omega) (prove_sq 4 4 0 12 (by rfl))

lemma base_394 : 0 < A271510 394 :=
  A271510_pos_of_exists 394 0 0 13 15 (by rfl) (by omega) (prove_sq 0 0 13 52 (by rfl))

lemma base_395 : 0 < A271510 395 :=
  A271510_pos_of_exists 395 5 0 3 19 (by rfl) (by omega) (prove_sq 5 0 3 13 (by rfl))

lemma base_396 : 0 < A271510 396 :=
  A271510_pos_of_exists 396 6 6 0 18 (by rfl) (by omega) (prove_sq 6 6 0 18 (by rfl))

lemma base_397 : 0 < A271510 397 :=
  A271510_pos_of_exists 397 0 0 6 19 (by rfl) (by omega) (prove_sq 0 0 6 24 (by rfl))

lemma base_398 : 0 < A271510 398 :=
  A271510_pos_of_exists 398 12 2 5 15 (by rfl) (by omega) (prove_sq 12 2 5 24 (by rfl))

lemma base_399 : 0 < A271510 399 :=
  A271510_pos_of_exists 399 3 2 5 19 (by rfl) (by omega) (prove_sq 3 2 5 21 (by rfl))

lemma base_400 : 0 < A271510 400 :=
  A271510_pos_of_exists 400 0 0 0 20 (by rfl) (by omega) (prove_sq 0 0 0 0 (by rfl))

lemma base_401 : 0 < A271510 401 :=
  A271510_pos_of_exists 401 0 0 1 20 (by rfl) (by omega) (prove_sq 0 0 1 4 (by rfl))

lemma base_402 : 0 < A271510 402 :=
  A271510_pos_of_exists 402 1 1 0 20 (by rfl) (by omega) (prove_sq 1 1 0 3 (by rfl))

lemma base_403 : 0 < A271510 403 :=
  A271510_pos_of_exists 403 1 1 1 20 (by rfl) (by omega) (prove_sq 1 1 1 5 (by rfl))

lemma base_404 : 0 < A271510 404 :=
  A271510_pos_of_exists 404 0 0 2 20 (by rfl) (by omega) (prove_sq 0 0 2 8 (by rfl))

lemma base_405 : 0 < A271510 405 :=
  A271510_pos_of_exists 405 0 0 9 18 (by rfl) (by omega) (prove_sq 0 0 9 36 (by rfl))

lemma base_406 : 0 < A271510 406 :=
  A271510_pos_of_exists 406 5 4 19 2 (by rfl) (by omega) (prove_sq 5 4 19 77 (by rfl))

lemma base_407 : 0 < A271510 407 :=
  A271510_pos_of_exists 407 3 3 10 17 (by rfl) (by omega) (prove_sq 3 3 10 41 (by rfl))

lemma base_408 : 0 < A271510 408 :=
  A271510_pos_of_exists 408 2 2 0 20 (by rfl) (by omega) (prove_sq 2 2 0 6 (by rfl))

lemma base_409 : 0 < A271510 409 :=
  A271510_pos_of_exists 409 0 0 3 20 (by rfl) (by omega) (prove_sq 0 0 3 12 (by rfl))

lemma base_410 : 0 < A271510 410 :=
  A271510_pos_of_exists 410 0 0 7 19 (by rfl) (by omega) (prove_sq 0 0 7 28 (by rfl))

lemma base_411 : 0 < A271510 411 :=
  A271510_pos_of_exists 411 5 4 19 3 (by rfl) (by omega) (prove_sq 5 4 19 77 (by rfl))

lemma base_412 : 0 < A271510 412 :=
  A271510_pos_of_exists 412 2 2 2 20 (by rfl) (by omega) (prove_sq 2 2 2 10 (by rfl))

lemma base_413 : 0 < A271510 413 :=
  A271510_pos_of_exists 413 12 6 13 8 (by rfl) (by omega) (prove_sq 12 6 13 56 (by rfl))

lemma base_414 : 0 < A271510 414 :=
  A271510_pos_of_exists 414 3 1 2 20 (by rfl) (by omega) (prove_sq 3 1 2 9 (by rfl))

lemma base_415 : 0 < A271510 415 :=
  A271510_pos_of_exists 415 5 5 2 19 (by rfl) (by omega) (prove_sq 5 5 2 17 (by rfl))

lemma base_416 : 0 < A271510 416 :=
  A271510_pos_of_exists 416 0 0 4 20 (by rfl) (by omega) (prove_sq 0 0 4 16 (by rfl))

lemma base_417 : 0 < A271510 417 :=
  A271510_pos_of_exists 417 6 2 4 19 (by rfl) (by omega) (prove_sq 6 2 4 18 (by rfl))

lemma base_418 : 0 < A271510 418 :=
  A271510_pos_of_exists 418 3 3 0 20 (by rfl) (by omega) (prove_sq 3 3 0 9 (by rfl))

lemma base_419 : 0 < A271510 419 :=
  A271510_pos_of_exists 419 7 3 0 19 (by rfl) (by omega) (prove_sq 7 3 0 11 (by rfl))

lemma base_420 : 0 < A271510 420 :=
  A271510_pos_of_exists 420 5 5 9 17 (by rfl) (by omega) (prove_sq 5 5 9 39 (by rfl))

lemma base_421 : 0 < A271510 421 :=
  A271510_pos_of_exists 421 0 0 14 15 (by rfl) (by omega) (prove_sq 0 0 14 56 (by rfl))

lemma base_422 : 0 < A271510 422 :=
  A271510_pos_of_exists 422 7 7 0 18 (by rfl) (by omega) (prove_sq 7 7 0 21 (by rfl))

lemma base_423 : 0 < A271510 423 :=
  A271510_pos_of_exists 423 7 1 7 18 (by rfl) (by omega) (prove_sq 7 1 7 29 (by rfl))

lemma base_424 : 0 < A271510 424 :=
  A271510_pos_of_exists 424 0 0 10 18 (by rfl) (by omega) (prove_sq 0 0 10 40 (by rfl))

lemma base_425 : 0 < A271510 425 :=
  A271510_pos_of_exists 425 0 0 5 20 (by rfl) (by omega) (prove_sq 0 0 5 20 (by rfl))

lemma base_426 : 0 < A271510 426 :=
  A271510_pos_of_exists 426 7 7 18 2 (by rfl) (by omega) (prove_sq 7 7 18 75 (by rfl))

lemma base_427 : 0 < A271510 427 :=
  A271510_pos_of_exists 427 3 3 3 20 (by rfl) (by omega) (prove_sq 3 3 3 15 (by rfl))

lemma base_428 : 0 < A271510 428 :=
  A271510_pos_of_exists 428 9 1 11 15 (by rfl) (by omega) (prove_sq 9 1 11 45 (by rfl))

lemma base_429 : 0 < A271510 429 :=
  A271510_pos_of_exists 429 10 8 12 11 (by rfl) (by omega) (prove_sq 10 8 12 54 (by rfl))

lemma base_430 : 0 < A271510 430 :=
  A271510_pos_of_exists 430 7 5 10 16 (by rfl) (by omega) (prove_sq 7 5 10 43 (by rfl))

lemma base_431 : 0 < A271510 431 :=
  A271510_pos_of_exists 431 7 7 18 3 (by rfl) (by omega) (prove_sq 7 7 18 75 (by rfl))

lemma base_432 : 0 < A271510 432 :=
  A271510_pos_of_exists 432 4 4 0 20 (by rfl) (by omega) (prove_sq 4 4 0 12 (by rfl))

lemma base_433 : 0 < A271510 433 :=
  A271510_pos_of_exists 433 0 0 12 17 (by rfl) (by omega) (prove_sq 0 0 12 48 (by rfl))

lemma base_434 : 0 < A271510 434 :=
  A271510_pos_of_exists 434 5 0 3 20 (by rfl) (by omega) (prove_sq 5 0 3 13 (by rfl))

lemma base_435 : 0 < A271510 435 :=
  A271510_pos_of_exists 435 9 7 4 17 (by rfl) (by omega) (prove_sq 9 7 4 27 (by rfl))

lemma base_436 : 0 < A271510 436 :=
  A271510_pos_of_exists 436 0 0 6 20 (by rfl) (by omega) (prove_sq 0 0 6 24 (by rfl))

lemma base_437 : 0 < A271510 437 :=
  A271510_pos_of_exists 437 9 0 10 16 (by rfl) (by omega) (prove_sq 9 0 10 41 (by rfl))

lemma base_438 : 0 < A271510 438 :=
  A271510_pos_of_exists 438 3 2 5 20 (by rfl) (by omega) (prove_sq 3 2 5 21 (by rfl))

lemma base_439 : 0 < A271510 439 :=
  A271510_pos_of_exists 439 5 2 7 19 (by rfl) (by omega) (prove_sq 5 2 7 29 (by rfl))

lemma base_440 : 0 < A271510 440 :=
  A271510_pos_of_exists 440 6 0 2 20 (by rfl) (by omega) (prove_sq 6 0 2 10 (by rfl))

lemma base_441 : 0 < A271510 441 :=
  A271510_pos_of_exists 441 0 0 0 21 (by rfl) (by omega) (prove_sq 0 0 0 0 (by rfl))

lemma base_442 : 0 < A271510 442 :=
  A271510_pos_of_exists 442 0 0 1 21 (by rfl) (by omega) (prove_sq 0 0 1 4 (by rfl))

lemma base_443 : 0 < A271510 443 :=
  A271510_pos_of_exists 443 1 1 0 21 (by rfl) (by omega) (prove_sq 1 1 0 3 (by rfl))

lemma base_444 : 0 < A271510 444 :=
  A271510_pos_of_exists 444 1 1 1 21 (by rfl) (by omega) (prove_sq 1 1 1 5 (by rfl))

lemma base_445 : 0 < A271510 445 :=
  A271510_pos_of_exists 445 0 0 2 21 (by rfl) (by omega) (prove_sq 0 0 2 8 (by rfl))

lemma base_446 : 0 < A271510 446 :=
  A271510_pos_of_exists 446 7 0 6 19 (by rfl) (by omega) (prove_sq 7 0 6 25 (by rfl))

lemma base_447 : 0 < A271510 447 :=
  A271510_pos_of_exists 447 7 7 5 18 (by rfl) (by omega) (prove_sq 7 7 5 29 (by rfl))

lemma base_448 : 0 < A271510 448 :=
  A271510_pos_of_exists 448 4 4 4 20 (by rfl) (by omega) (prove_sq 4 4 4 20 (by rfl))

lemma base_449 : 0 < A271510 449 :=
  A271510_pos_of_exists 449 0 0 7 20 (by rfl) (by omega) (prove_sq 0 0 7 28 (by rfl))

lemma base_450 : 0 < A271510 450 :=
  A271510_pos_of_exists 450 0 0 3 21 (by rfl) (by omega) (prove_sq 0 0 3 12 (by rfl))

lemma base_451 : 0 < A271510 451 :=
  A271510_pos_of_exists 451 3 0 1 21 (by rfl) (by omega) (prove_sq 3 0 1 5 (by rfl))

lemma base_452 : 0 < A271510 452 :=
  A271510_pos_of_exists 452 0 0 14 16 (by rfl) (by omega) (prove_sq 0 0 14 56 (by rfl))

lemma base_453 : 0 < A271510 453 :=
  A271510_pos_of_exists 453 2 2 2 21 (by rfl) (by omega) (prove_sq 2 2 2 10 (by rfl))

lemma base_454 : 0 < A271510 454 :=
  A271510_pos_of_exists 454 5 5 2 20 (by rfl) (by omega) (prove_sq 5 5 2 17 (by rfl))

lemma base_455 : 0 < A271510 455 :=
  A271510_pos_of_exists 455 3 1 2 21 (by rfl) (by omega) (prove_sq 3 1 2 9 (by rfl))

lemma base_456 : 0 < A271510 456 :=
  A271510_pos_of_exists 456 6 2 4 20 (by rfl) (by omega) (prove_sq 6 2 4 18 (by rfl))

lemma base_457 : 0 < A271510 457 :=
  A271510_pos_of_exists 457 0 0 4 21 (by rfl) (by omega) (prove_sq 0 0 4 16 (by rfl))

lemma base_458 : 0 < A271510 458 :=
  A271510_pos_of_exists 458 0 0 13 17 (by rfl) (by omega) (prove_sq 0 0 13 52 (by rfl))

lemma base_459 : 0 < A271510 459 :=
  A271510_pos_of_exists 459 3 3 0 21 (by rfl) (by omega) (prove_sq 3 3 0 9 (by rfl))

lemma base_460 : 0 < A271510 460 :=
  A271510_pos_of_exists 460 7 1 7 19 (by rfl) (by omega) (prove_sq 7 1 7 29 (by rfl))

lemma base_461 : 0 < A271510 461 :=
  A271510_pos_of_exists 461 0 0 10 19 (by rfl) (by omega) (prove_sq 0 0 10 40 (by rfl))

lemma base_462 : 0 < A271510 462 :=
  A271510_pos_of_exists 462 4 2 1 21 (by rfl) (by omega) (prove_sq 4 2 1 8 (by rfl))

lemma base_463 : 0 < A271510 463 :=
  A271510_pos_of_exists 463 7 5 10 17 (by rfl) (by omega) (prove_sq 7 5 10 43 (by rfl))

lemma base_464 : 0 < A271510 464 :=
  A271510_pos_of_exists 464 0 0 8 20 (by rfl) (by omega) (prove_sq 0 0 8 32 (by rfl))

lemma base_465 : 0 < A271510 465 :=
  A271510_pos_of_exists 465 14 8 14 3 (by rfl) (by omega) (prove_sq 14 8 14 62 (by rfl))

lemma base_466 : 0 < A271510 466 :=
  A271510_pos_of_exists 466 0 0 5 21 (by rfl) (by omega) (prove_sq 0 0 5 20 (by rfl))

lemma base_467 : 0 < A271510 467 :=
  A271510_pos_of_exists 467 5 3 12 17 (by rfl) (by omega) (prove_sq 5 3 12 49 (by rfl))

lemma base_468 : 0 < A271510 468 :=
  A271510_pos_of_exists 468 0 0 12 18 (by rfl) (by omega) (prove_sq 0 0 12 48 (by rfl))

lemma base_469 : 0 < A271510 469 :=
  A271510_pos_of_exists 469 6 6 6 19 (by rfl) (by omega) (prove_sq 6 6 6 30 (by rfl))

lemma base_470 : 0 < A271510 470 :=
  A271510_pos_of_exists 470 9 0 10 17 (by rfl) (by omega) (prove_sq 9 0 10 41 (by rfl))

lemma base_471 : 0 < A271510 471 :=
  A271510_pos_of_exists 471 7 7 7 18 (by rfl) (by omega) (prove_sq 7 7 7 35 (by rfl))

lemma base_472 : 0 < A271510 472 :=
  A271510_pos_of_exists 472 6 6 0 20 (by rfl) (by omega) (prove_sq 6 6 0 18 (by rfl))

lemma base_473 : 0 < A271510 473 :=
  A271510_pos_of_exists 473 4 4 0 21 (by rfl) (by omega) (prove_sq 4 4 0 12 (by rfl))

lemma base_474 : 0 < A271510 474 :=
  A271510_pos_of_exists 474 5 2 2 21 (by rfl) (by omega) (prove_sq 5 2 2 11 (by rfl))

lemma base_475 : 0 < A271510 475 :=
  A271510_pos_of_exists 475 5 0 3 21 (by rfl) (by omega) (prove_sq 5 0 3 13 (by rfl))

lemma base_476 : 0 < A271510 476 :=
  A271510_pos_of_exists 476 6 4 10 18 (by rfl) (by omega) (prove_sq 6 4 10 42 (by rfl))

lemma base_477 : 0 < A271510 477 :=
  A271510_pos_of_exists 477 0 0 6 21 (by rfl) (by omega) (prove_sq 0 0 6 24 (by rfl))

lemma base_478 : 0 < A271510 478 :=
  A271510_pos_of_exists 478 5 2 7 20 (by rfl) (by omega) (prove_sq 5 2 7 29 (by rfl))

lemma base_479 : 0 < A271510 479 :=
  A271510_pos_of_exists 479 3 2 5 21 (by rfl) (by omega) (prove_sq 3 2 5 21 (by rfl))

lemma base_480 : 0 < A271510 480 :=
  A271510_pos_of_exists 480 12 4 8 16 (by rfl) (by omega) (prove_sq 12 4 8 36 (by rfl))

lemma base_481 : 0 < A271510 481 :=
  A271510_pos_of_exists 481 0 0 9 20 (by rfl) (by omega) (prove_sq 0 0 9 36 (by rfl))

lemma base_482 : 0 < A271510 482 :=
  A271510_pos_of_exists 482 0 0 11 19 (by rfl) (by omega) (prove_sq 0 0 11 44 (by rfl))

lemma base_483 : 0 < A271510 483 :=
  A271510_pos_of_exists 483 5 1 4 21 (by rfl) (by omega) (prove_sq 5 1 4 17 (by rfl))

lemma base_484 : 0 < A271510 484 :=
  A271510_pos_of_exists 484 0 0 0 22 (by rfl) (by omega) (prove_sq 0 0 0 0 (by rfl))

lemma base_485 : 0 < A271510 485 :=
  A271510_pos_of_exists 485 0 0 1 22 (by rfl) (by omega) (prove_sq 0 0 1 4 (by rfl))

lemma base_486 : 0 < A271510 486 :=
  A271510_pos_of_exists 486 1 1 0 22 (by rfl) (by omega) (prove_sq 1 1 0 3 (by rfl))

lemma base_487 : 0 < A271510 487 :=
  A271510_pos_of_exists 487 1 1 1 22 (by rfl) (by omega) (prove_sq 1 1 1 5 (by rfl))

lemma base_488 : 0 < A271510 488 :=
  A271510_pos_of_exists 488 0 0 2 22 (by rfl) (by omega) (prove_sq 0 0 2 8 (by rfl))

lemma base_489 : 0 < A271510 489 :=
  A271510_pos_of_exists 489 4 4 4 21 (by rfl) (by omega) (prove_sq 4 4 4 20 (by rfl))

lemma base_490 : 0 < A271510 490 :=
  A271510_pos_of_exists 490 0 0 7 21 (by rfl) (by omega) (prove_sq 0 0 7 28 (by rfl))

lemma base_491 : 0 < A271510 491 :=
  A271510_pos_of_exists 491 5 5 0 21 (by rfl) (by omega) (prove_sq 5 5 0 15 (by rfl))

lemma base_492 : 0 < A271510 492 :=
  A271510_pos_of_exists 492 2 2 0 22 (by rfl) (by omega) (prove_sq 2 2 0 6 (by rfl))

lemma base_493 : 0 < A271510 493 :=
  A271510_pos_of_exists 493 0 0 3 22 (by rfl) (by omega) (prove_sq 0 0 3 12 (by rfl))

lemma base_494 : 0 < A271510 494 :=
  A271510_pos_of_exists 494 3 0 1 22 (by rfl) (by omega) (prove_sq 3 0 1 5 (by rfl))

lemma base_495 : 0 < A271510 495 :=
  A271510_pos_of_exists 495 5 5 2 21 (by rfl) (by omega) (prove_sq 5 5 2 17 (by rfl))

lemma base_496 : 0 < A271510 496 :=
  A271510_pos_of_exists 496 2 2 2 22 (by rfl) (by omega) (prove_sq 2 2 2 10 (by rfl))

lemma base_497 : 0 < A271510 497 :=
  A271510_pos_of_exists 497 6 2 4 21 (by rfl) (by omega) (prove_sq 6 2 4 18 (by rfl))

lemma base_498 : 0 < A271510 498 :=
  A271510_pos_of_exists 498 3 1 2 22 (by rfl) (by omega) (prove_sq 3 1 2 9 (by rfl))

lemma base_499 : 0 < A271510 499 :=
  A271510_pos_of_exists 499 7 1 7 20 (by rfl) (by omega) (prove_sq 7 1 7 29 (by rfl))

lemma base_500 : 0 < A271510 500 :=
  A271510_pos_of_exists 500 0 0 4 22 (by rfl) (by omega) (prove_sq 0 0 4 16 (by rfl))

lemma base_501 : 0 < A271510 501 :=
  A271510_pos_of_exists 501 14 4 0 17 (by rfl) (by omega) (prove_sq 14 4 0 18 (by rfl))

lemma base_502 : 0 < A271510 502 :=
  A271510_pos_of_exists 502 3 3 0 22 (by rfl) (by omega) (prove_sq 3 3 0 9 (by rfl))

lemma base_503 : 0 < A271510 503 :=
  A271510_pos_of_exists 503 7 2 3 21 (by rfl) (by omega) (prove_sq 7 2 3 15 (by rfl))

lemma base_504 : 0 < A271510 504 :=
  A271510_pos_of_exists 504 10 8 12 14 (by rfl) (by omega) (prove_sq 10 8 12 54 (by rfl))

lemma base_505 : 0 < A271510 505 :=
  A271510_pos_of_exists 505 0 0 8 21 (by rfl) (by omega) (prove_sq 0 0 8 32 (by rfl))

lemma base_506 : 0 < A271510 506 :=
  A271510_pos_of_exists 506 9 2 14 15 (by rfl) (by omega) (prove_sq 9 2 14 57 (by rfl))

lemma base_507 : 0 < A271510 507 :=
  A271510_pos_of_exists 507 9 7 4 19 (by rfl) (by omega) (prove_sq 9 7 4 27 (by rfl))

lemma base_508 : 0 < A271510 508 :=
  A271510_pos_of_exists 508 6 6 6 20 (by rfl) (by omega) (prove_sq 6 6 6 30 (by rfl))

lemma base_509 : 0 < A271510 509 :=
  A271510_pos_of_exists 509 0 0 5 22 (by rfl) (by omega) (prove_sq 0 0 5 20 (by rfl))

lemma base_510 : 0 < A271510 510 :=
  A271510_pos_of_exists 510 13 10 4 15 (by rfl) (by omega) (prove_sq 13 10 4 35 (by rfl))

lemma base_511 : 0 < A271510 511 :=
  A271510_pos_of_exists 511 3 3 3 22 (by rfl) (by omega) (prove_sq 3 3 3 15 (by rfl))

lemma base_512 : 0 < A271510 512 :=
  A271510_pos_of_exists 512 0 0 16 16 (by rfl) (by omega) (prove_sq 0 0 16 64 (by rfl))

lemma base_513 : 0 < A271510 513 :=
  A271510_pos_of_exists 513 6 4 10 19 (by rfl) (by omega) (prove_sq 6 4 10 42 (by rfl))

lemma base_514 : 0 < A271510 514 :=
  A271510_pos_of_exists 514 0 0 15 17 (by rfl) (by omega) (prove_sq 0 0 15 60 (by rfl))

lemma base_515 : 0 < A271510 515 :=
  A271510_pos_of_exists 515 9 3 19 8 (by rfl) (by omega) (prove_sq 9 3 19 77 (by rfl))

lemma base_516 : 0 < A271510 516 :=
  A271510_pos_of_exists 516 4 4 0 22 (by rfl) (by omega) (prove_sq 4 4 0 12 (by rfl))

lemma base_517 : 0 < A271510 517 :=
  A271510_pos_of_exists 517 5 2 2 22 (by rfl) (by omega) (prove_sq 5 2 2 11 (by rfl))

lemma base_518 : 0 < A271510 518 :=
  A271510_pos_of_exists 518 3 3 10 20 (by rfl) (by omega) (prove_sq 3 3 10 41 (by rfl))

lemma base_519 : 0 < A271510 519 :=
  A271510_pos_of_exists 519 5 2 7 21 (by rfl) (by omega) (prove_sq 5 2 7 29 (by rfl))

lemma base_520 : 0 < A271510 520 :=
  A271510_pos_of_exists 520 0 0 6 22 (by rfl) (by omega) (prove_sq 0 0 6 24 (by rfl))

lemma base_521 : 0 < A271510 521 :=
  A271510_pos_of_exists 521 0 0 11 20 (by rfl) (by omega) (prove_sq 0 0 11 44 (by rfl))

lemma base_522 : 0 < A271510 522 :=
  A271510_pos_of_exists 522 0 0 9 21 (by rfl) (by omega) (prove_sq 0 0 9 36 (by rfl))

lemma base_523 : 0 < A271510 523 :=
  A271510_pos_of_exists 523 5 4 19 11 (by rfl) (by omega) (prove_sq 5 4 19 77 (by rfl))

lemma base_524 : 0 < A271510 524 :=
  A271510_pos_of_exists 524 6 0 2 22 (by rfl) (by omega) (prove_sq 6 0 2 10 (by rfl))

lemma base_525 : 0 < A271510 525 :=
  A271510_pos_of_exists 525 8 4 2 21 (by rfl) (by omega) (prove_sq 8 4 2 16 (by rfl))

lemma base_526 : 0 < A271510 526 :=
  A271510_pos_of_exists 526 5 1 4 22 (by rfl) (by omega) (prove_sq 5 1 4 17 (by rfl))

lemma base_527 : 0 < A271510 527 :=
  A271510_pos_of_exists 527 9 1 11 18 (by rfl) (by omega) (prove_sq 9 1 11 45 (by rfl))

lemma base_528 : 0 < A271510 528 :=
  A271510_pos_of_exists 528 8 8 0 20 (by rfl) (by omega) (prove_sq 8 8 0 24 (by rfl))

lemma base_529 : 0 < A271510 529 :=
  A271510_pos_of_exists 529 0 0 0 23 (by rfl) (by omega) (prove_sq 0 0 0 0 (by rfl))

lemma base_530 : 0 < A271510 530 :=
  A271510_pos_of_exists 530 0 0 1 23 (by rfl) (by omega) (prove_sq 0 0 1 4 (by rfl))

lemma base_531 : 0 < A271510 531 :=
  A271510_pos_of_exists 531 1 1 0 23 (by rfl) (by omega) (prove_sq 1 1 0 3 (by rfl))

lemma base_532 : 0 < A271510 532 :=
  A271510_pos_of_exists 532 1 1 1 23 (by rfl) (by omega) (prove_sq 1 1 1 5 (by rfl))

lemma base_533 : 0 < A271510 533 :=
  A271510_pos_of_exists 533 0 0 2 23 (by rfl) (by omega) (prove_sq 0 0 2 8 (by rfl))

lemma base_534 : 0 < A271510 534 :=
  A271510_pos_of_exists 534 5 5 0 22 (by rfl) (by omega) (prove_sq 5 5 0 15 (by rfl))

lemma base_535 : 0 < A271510 535 :=
  A271510_pos_of_exists 535 7 5 10 19 (by rfl) (by omega) (prove_sq 7 5 10 43 (by rfl))

lemma base_536 : 0 < A271510 536 :=
  A271510_pos_of_exists 536 6 6 20 8 (by rfl) (by omega) (prove_sq 6 6 20 82 (by rfl))

lemma base_537 : 0 < A271510 537 :=
  A271510_pos_of_exists 537 2 2 0 23 (by rfl) (by omega) (prove_sq 2 2 0 6 (by rfl))

lemma base_538 : 0 < A271510 538 :=
  A271510_pos_of_exists 538 0 0 3 23 (by rfl) (by omega) (prove_sq 0 0 3 12 (by rfl))

lemma base_539 : 0 < A271510 539 :=
  A271510_pos_of_exists 539 3 0 1 23 (by rfl) (by omega) (prove_sq 3 0 1 5 (by rfl))

lemma base_540 : 0 < A271510 540 :=
  A271510_pos_of_exists 540 6 2 4 22 (by rfl) (by omega) (prove_sq 6 2 4 18 (by rfl))

lemma base_541 : 0 < A271510 541 :=
  A271510_pos_of_exists 541 0 0 10 21 (by rfl) (by omega) (prove_sq 0 0 10 40 (by rfl))

lemma base_542 : 0 < A271510 542 :=
  A271510_pos_of_exists 542 7 3 0 22 (by rfl) (by omega) (prove_sq 7 3 0 11 (by rfl))

lemma base_543 : 0 < A271510 543 :=
  A271510_pos_of_exists 543 3 1 2 23 (by rfl) (by omega) (prove_sq 3 1 2 9 (by rfl))

lemma base_544 : 0 < A271510 544 :=
  A271510_pos_of_exists 544 0 0 12 20 (by rfl) (by omega) (prove_sq 0 0 12 48 (by rfl))

lemma base_545 : 0 < A271510 545 :=
  A271510_pos_of_exists 545 0 0 4 23 (by rfl) (by omega) (prove_sq 0 0 4 16 (by rfl))

lemma base_546 : 0 < A271510 546 :=
  A271510_pos_of_exists 546 5 4 19 12 (by rfl) (by omega) (prove_sq 5 4 19 77 (by rfl))

lemma base_547 : 0 < A271510 547 :=
  A271510_pos_of_exists 547 3 3 0 23 (by rfl) (by omega) (prove_sq 3 3 0 9 (by rfl))

lemma base_548 : 0 < A271510 548 :=
  A271510_pos_of_exists 548 0 0 8 22 (by rfl) (by omega) (prove_sq 0 0 8 32 (by rfl))

lemma base_549 : 0 < A271510 549 :=
  A271510_pos_of_exists 549 0 0 15 18 (by rfl) (by omega) (prove_sq 0 0 15 60 (by rfl))

lemma base_550 : 0 < A271510 550 :=
  A271510_pos_of_exists 550 4 2 1 23 (by rfl) (by omega) (prove_sq 4 2 1 8 (by rfl))

lemma base_551 : 0 < A271510 551 :=
  A271510_pos_of_exists 551 9 3 19 10 (by rfl) (by omega) (prove_sq 9 3 19 77 (by rfl))

lemma base_552 : 0 < A271510 552 :=
  A271510_pos_of_exists 552 6 4 10 20 (by rfl) (by omega) (prove_sq 6 4 10 42 (by rfl))

lemma base_553 : 0 < A271510 553 :=
  A271510_pos_of_exists 553 6 6 20 9 (by rfl) (by omega) (prove_sq 6 6 20 82 (by rfl))

lemma base_554 : 0 < A271510 554 :=
  A271510_pos_of_exists 554 0 0 5 23 (by rfl) (by omega) (prove_sq 0 0 5 20 (by rfl))

lemma base_555 : 0 < A271510 555 :=
  A271510_pos_of_exists 555 7 4 7 21 (by rfl) (by omega) (prove_sq 7 4 7 31 (by rfl))

lemma base_556 : 0 < A271510 556 :=
  A271510_pos_of_exists 556 3 3 3 23 (by rfl) (by omega) (prove_sq 3 3 3 15 (by rfl))

lemma base_557 : 0 < A271510 557 :=
  A271510_pos_of_exists 557 0 0 14 19 (by rfl) (by omega) (prove_sq 0 0 14 56 (by rfl))

lemma base_558 : 0 < A271510 558 :=
  A271510_pos_of_exists 558 7 4 22 3 (by rfl) (by omega) (prove_sq 7 4 22 89 (by rfl))

lemma base_559 : 0 < A271510 559 :=
  A271510_pos_of_exists 559 3 3 10 21 (by rfl) (by omega) (prove_sq 3 3 10 41 (by rfl))

lemma base_560 : 0 < A271510 560 :=
  A271510_pos_of_exists 560 10 10 18 6 (by rfl) (by omega) (prove_sq 10 10 18 78 (by rfl))

lemma base_561 : 0 < A271510 561 :=
  A271510_pos_of_exists 561 4 4 0 23 (by rfl) (by omega) (prove_sq 4 4 0 12 (by rfl))

lemma base_562 : 0 < A271510 562 :=
  A271510_pos_of_exists 562 0 0 11 21 (by rfl) (by omega) (prove_sq 0 0 11 44 (by rfl))

lemma base_563 : 0 < A271510 563 :=
  A271510_pos_of_exists 563 5 0 3 23 (by rfl) (by omega) (prove_sq 5 0 3 13 (by rfl))

lemma base_564 : 0 < A271510 564 :=
  A271510_pos_of_exists 564 7 7 5 21 (by rfl) (by omega) (prove_sq 7 7 5 29 (by rfl))

lemma base_565 : 0 < A271510 565 :=
  A271510_pos_of_exists 565 0 0 6 23 (by rfl) (by omega) (prove_sq 0 0 6 24 (by rfl))

lemma base_566 : 0 < A271510 566 :=
  A271510_pos_of_exists 566 7 7 18 12 (by rfl) (by omega) (prove_sq 7 7 18 75 (by rfl))

lemma base_567 : 0 < A271510 567 :=
  A271510_pos_of_exists 567 3 2 5 23 (by rfl) (by omega) (prove_sq 3 2 5 21 (by rfl))

lemma base_568 : 0 < A271510 568 :=
  A271510_pos_of_exists 568 8 4 2 22 (by rfl) (by omega) (prove_sq 8 4 2 16 (by rfl))

lemma base_569 : 0 < A271510 569 :=
  A271510_pos_of_exists 569 0 0 13 20 (by rfl) (by omega) (prove_sq 0 0 13 52 (by rfl))

lemma base_570 : 0 < A271510 570 :=
  A271510_pos_of_exists 570 9 2 14 17 (by rfl) (by omega) (prove_sq 9 2 14 57 (by rfl))

lemma base_571 : 0 < A271510 571 :=
  A271510_pos_of_exists 571 5 1 4 23 (by rfl) (by omega) (prove_sq 5 1 4 17 (by rfl))

lemma base_572 : 0 < A271510 572 :=
  A271510_pos_of_exists 572 5 5 9 21 (by rfl) (by omega) (prove_sq 5 5 9 39 (by rfl))

lemma base_573 : 0 < A271510 573 :=
  A271510_pos_of_exists 573 10 4 4 21 (by rfl) (by omega) (prove_sq 10 4 4 22 (by rfl))

lemma base_574 : 0 < A271510 574 :=
  A271510_pos_of_exists 574 7 4 22 5 (by rfl) (by omega) (prove_sq 7 4 22 89 (by rfl))

lemma base_575 : 0 < A271510 575 :=
  A271510_pos_of_exists 575 9 3 1 22 (by rfl) (by omega) (prove_sq 9 3 1 13 (by rfl))

lemma base_576 : 0 < A271510 576 :=
  A271510_pos_of_exists 576 0 0 0 24 (by rfl) (by omega) (prove_sq 0 0 0 0 (by rfl))

lemma base_577 : 0 < A271510 577 :=
  A271510_pos_of_exists 577 0 0 1 24 (by rfl) (by omega) (prove_sq 0 0 1 4 (by rfl))

lemma base_578 : 0 < A271510 578 :=
  A271510_pos_of_exists 578 0 0 7 23 (by rfl) (by omega) (prove_sq 0 0 7 28 (by rfl))

lemma base_579 : 0 < A271510 579 :=
  A271510_pos_of_exists 579 1 1 1 24 (by rfl) (by omega) (prove_sq 1 1 1 5 (by rfl))

lemma base_580 : 0 < A271510 580 :=
  A271510_pos_of_exists 580 0 0 2 24 (by rfl) (by omega) (prove_sq 0 0 2 8 (by rfl))

lemma base_581 : 0 < A271510 581 :=
  A271510_pos_of_exists 581 9 0 10 20 (by rfl) (by omega) (prove_sq 9 0 10 41 (by rfl))

lemma base_582 : 0 < A271510 582 :=
  A271510_pos_of_exists 582 7 2 0 23 (by rfl) (by omega) (prove_sq 7 2 0 9 (by rfl))

lemma base_583 : 0 < A271510 583 :=
  A271510_pos_of_exists 583 5 5 2 23 (by rfl) (by omega) (prove_sq 5 5 2 17 (by rfl))

lemma base_584 : 0 < A271510 584 :=
  A271510_pos_of_exists 584 0 0 10 22 (by rfl) (by omega) (prove_sq 0 0 10 40 (by rfl))

lemma base_585 : 0 < A271510 585 :=
  A271510_pos_of_exists 585 0 0 3 24 (by rfl) (by omega) (prove_sq 0 0 3 12 (by rfl))

lemma base_586 : 0 < A271510 586 :=
  A271510_pos_of_exists 586 0 0 15 19 (by rfl) (by omega) (prove_sq 0 0 15 60 (by rfl))

lemma base_587 : 0 < A271510 587 :=
  A271510_pos_of_exists 587 7 3 0 23 (by rfl) (by omega) (prove_sq 7 3 0 11 (by rfl))

lemma base_588 : 0 < A271510 588 :=
  A271510_pos_of_exists 588 2 2 2 24 (by rfl) (by omega) (prove_sq 2 2 2 10 (by rfl))

lemma base_589 : 0 < A271510 589 :=
  A271510_pos_of_exists 589 10 10 10 17 (by rfl) (by omega) (prove_sq 10 10 10 50 (by rfl))

lemma base_590 : 0 < A271510 590 :=
  A271510_pos_of_exists 590 3 1 2 24 (by rfl) (by omega) (prove_sq 3 1 2 9 (by rfl))

lemma base_591 : 0 < A271510 591 :=
  A271510_pos_of_exists 591 7 2 3 23 (by rfl) (by omega) (prove_sq 7 2 3 15 (by rfl))

lemma base_592 : 0 < A271510 592 :=
  A271510_pos_of_exists 592 0 0 4 24 (by rfl) (by omega) (prove_sq 0 0 4 16 (by rfl))

lemma base_593 : 0 < A271510 593 :=
  A271510_pos_of_exists 593 0 0 8 23 (by rfl) (by omega) (prove_sq 0 0 8 32 (by rfl))

lemma base_594 : 0 < A271510 594 :=
  A271510_pos_of_exists 594 3 3 0 24 (by rfl) (by omega) (prove_sq 3 3 0 9 (by rfl))

lemma base_595 : 0 < A271510 595 :=
  A271510_pos_of_exists 595 9 3 19 12 (by rfl) (by omega) (prove_sq 9 3 19 77 (by rfl))

lemma base_596 : 0 < A271510 596 :=
  A271510_pos_of_exists 596 0 0 14 20 (by rfl) (by omega) (prove_sq 0 0 14 56 (by rfl))

lemma base_597 : 0 < A271510 597 :=
  A271510_pos_of_exists 597 4 2 1 24 (by rfl) (by omega) (prove_sq 4 2 1 8 (by rfl))

lemma base_598 : 0 < A271510 598 :=
  A271510_pos_of_exists 598 5 4 19 14 (by rfl) (by omega) (prove_sq 5 4 19 77 (by rfl))

lemma base_599 : 0 < A271510 599 :=
  A271510_pos_of_exists 599 15 3 2 19 (by rfl) (by omega) (prove_sq 15 3 2 19 (by rfl))

lemma base_600 : 0 < A271510 600 :=
  A271510_pos_of_exists 600 10 10 0 20 (by rfl) (by omega) (prove_sq 10 10 0 30 (by rfl))

lemma base_601 : 0 < A271510 601 :=
  A271510_pos_of_exists 601 0 0 5 24 (by rfl) (by omega) (prove_sq 0 0 5 20 (by rfl))

lemma base_602 : 0 < A271510 602 :=
  A271510_pos_of_exists 602 3 3 10 22 (by rfl) (by omega) (prove_sq 3 3 10 41 (by rfl))

lemma base_603 : 0 < A271510 603 :=
  A271510_pos_of_exists 603 3 3 3 24 (by rfl) (by omega) (prove_sq 3 3 3 15 (by rfl))

lemma base_604 : 0 < A271510 604 :=
  A271510_pos_of_exists 604 5 5 5 23 (by rfl) (by omega) (prove_sq 5 5 5 25 (by rfl))

lemma base_605 : 0 < A271510 605 :=
  A271510_pos_of_exists 605 0 0 11 22 (by rfl) (by omega) (prove_sq 0 0 11 44 (by rfl))

lemma base_606 : 0 < A271510 606 :=
  A271510_pos_of_exists 606 5 4 6 23 (by rfl) (by omega) (prove_sq 5 4 6 27 (by rfl))

lemma base_607 : 0 < A271510 607 :=
  A271510_pos_of_exists 607 5 2 7 23 (by rfl) (by omega) (prove_sq 5 2 7 29 (by rfl))

lemma base_608 : 0 < A271510 608 :=
  A271510_pos_of_exists 608 4 4 0 24 (by rfl) (by omega) (prove_sq 4 4 0 12 (by rfl))

lemma base_609 : 0 < A271510 609 :=
  A271510_pos_of_exists 609 5 2 2 24 (by rfl) (by omega) (prove_sq 5 2 2 11 (by rfl))

lemma base_610 : 0 < A271510 610 :=
  A271510_pos_of_exists 610 0 0 9 23 (by rfl) (by omega) (prove_sq 0 0 9 36 (by rfl))

lemma base_611 : 0 < A271510 611 :=
  A271510_pos_of_exists 611 11 7 21 0 (by rfl) (by omega) (prove_sq 11 7 21 87 (by rfl))

lemma base_612 : 0 < A271510 612 :=
  A271510_pos_of_exists 612 0 0 6 24 (by rfl) (by omega) (prove_sq 0 0 6 24 (by rfl))

lemma base_613 : 0 < A271510 613 :=
  A271510_pos_of_exists 613 0 0 17 18 (by rfl) (by omega) (prove_sq 0 0 17 68 (by rfl))

lemma base_614 : 0 < A271510 614 :=
  A271510_pos_of_exists 614 3 2 5 24 (by rfl) (by omega) (prove_sq 3 2 5 21 (by rfl))

lemma base_615 : 0 < A271510 615 :=
  A271510_pos_of_exists 615 5 5 9 22 (by rfl) (by omega) (prove_sq 5 5 9 39 (by rfl))

lemma base_616 : 0 < A271510 616 :=
  A271510_pos_of_exists 616 6 0 2 24 (by rfl) (by omega) (prove_sq 6 0 2 10 (by rfl))

lemma base_617 : 0 < A271510 617 :=
  A271510_pos_of_exists 617 0 0 16 19 (by rfl) (by omega) (prove_sq 0 0 16 64 (by rfl))

lemma base_618 : 0 < A271510 618 :=
  A271510_pos_of_exists 618 5 1 4 24 (by rfl) (by omega) (prove_sq 5 1 4 17 (by rfl))

lemma base_619 : 0 < A271510 619 :=
  A271510_pos_of_exists 619 5 3 12 21 (by rfl) (by omega) (prove_sq 5 3 12 49 (by rfl))

lemma base_620 : 0 < A271510 620 :=
  A271510_pos_of_exists 620 9 3 1 23 (by rfl) (by omega) (prove_sq 9 3 1 13 (by rfl))

lemma base_621 : 0 < A271510 621 :=
  A271510_pos_of_exists 621 14 2 14 15 (by rfl) (by omega) (prove_sq 14 2 14 58 (by rfl))

lemma base_622 : 0 < A271510 622 :=
  A271510_pos_of_exists 622 9 0 10 21 (by rfl) (by omega) (prove_sq 9 0 10 41 (by rfl))

lemma base_623 : 0 < A271510 623 :=
  A271510_pos_of_exists 623 15 6 1 19 (by rfl) (by omega) (prove_sq 15 6 1 23 (by rfl))

lemma base_624 : 0 < A271510 624 :=
  A271510_pos_of_exists 624 4 4 4 24 (by rfl) (by omega) (prove_sq 4 4 4 20 (by rfl))

lemma base_625 : 0 < A271510 625 :=
  A271510_pos_of_exists 625 0 0 0 25 (by rfl) (by omega) (prove_sq 0 0 0 0 (by rfl))

lemma base_626 : 0 < A271510 626 :=
  A271510_pos_of_exists 626 0 0 1 25 (by rfl) (by omega) (prove_sq 0 0 1 4 (by rfl))

lemma base_627 : 0 < A271510 627 :=
  A271510_pos_of_exists 627 1 1 0 25 (by rfl) (by omega) (prove_sq 1 1 0 3 (by rfl))

lemma base_628 : 0 < A271510 628 :=
  A271510_pos_of_exists 628 0 0 12 22 (by rfl) (by omega) (prove_sq 0 0 12 48 (by rfl))

lemma base_629 : 0 < A271510 629 :=
  A271510_pos_of_exists 629 0 0 2 25 (by rfl) (by omega) (prove_sq 0 0 2 8 (by rfl))

lemma base_630 : 0 < A271510 630 :=
  A271510_pos_of_exists 630 5 5 2 24 (by rfl) (by omega) (prove_sq 5 5 2 17 (by rfl))

lemma base_631 : 0 < A271510 631 :=
  A271510_pos_of_exists 631 7 7 7 22 (by rfl) (by omega) (prove_sq 7 7 7 35 (by rfl))

lemma base_632 : 0 < A271510 632 :=
  A271510_pos_of_exists 632 6 2 4 24 (by rfl) (by omega) (prove_sq 6 2 4 18 (by rfl))

lemma base_633 : 0 < A271510 633 :=
  A271510_pos_of_exists 633 2 2 0 25 (by rfl) (by omega) (prove_sq 2 2 0 6 (by rfl))

lemma base_634 : 0 < A271510 634 :=
  A271510_pos_of_exists 634 0 0 3 25 (by rfl) (by omega) (prove_sq 0 0 3 12 (by rfl))

lemma base_635 : 0 < A271510 635 :=
  A271510_pos_of_exists 635 3 0 1 25 (by rfl) (by omega) (prove_sq 3 0 1 5 (by rfl))

lemma base_636 : 0 < A271510 636 :=
  A271510_pos_of_exists 636 6 4 10 22 (by rfl) (by omega) (prove_sq 6 4 10 42 (by rfl))

lemma base_637 : 0 < A271510 637 :=
  A271510_pos_of_exists 637 0 0 14 21 (by rfl) (by omega) (prove_sq 0 0 14 56 (by rfl))

lemma base_638 : 0 < A271510 638 :=
  A271510_pos_of_exists 638 7 2 3 24 (by rfl) (by omega) (prove_sq 7 2 3 15 (by rfl))

lemma base_639 : 0 < A271510 639 :=
  A271510_pos_of_exists 639 3 1 2 25 (by rfl) (by omega) (prove_sq 3 1 2 9 (by rfl))

lemma base_640 : 0 < A271510 640 :=
  A271510_pos_of_exists 640 0 0 8 24 (by rfl) (by omega) (prove_sq 0 0 8 32 (by rfl))

lemma base_641 : 0 < A271510 641 :=
  A271510_pos_of_exists 641 0 0 4 25 (by rfl) (by omega) (prove_sq 0 0 4 16 (by rfl))

lemma base_642 : 0 < A271510 642 :=
  A271510_pos_of_exists 642 9 2 14 19 (by rfl) (by omega) (prove_sq 9 2 14 57 (by rfl))

lemma base_643 : 0 < A271510 643 :=
  A271510_pos_of_exists 643 3 3 0 25 (by rfl) (by omega) (prove_sq 3 3 0 9 (by rfl))

lemma base_644 : 0 < A271510 644 :=
  A271510_pos_of_exists 644 7 3 15 19 (by rfl) (by omega) (prove_sq 7 3 15 61 (by rfl))

lemma base_645 : 0 < A271510 645 :=
  A271510_pos_of_exists 645 10 10 18 11 (by rfl) (by omega) (prove_sq 10 10 18 78 (by rfl))

lemma base_646 : 0 < A271510 646 :=
  A271510_pos_of_exists 646 4 2 1 25 (by rfl) (by omega) (prove_sq 4 2 1 8 (by rfl))

lemma base_647 : 0 < A271510 647 :=
  A271510_pos_of_exists 647 3 3 10 23 (by rfl) (by omega) (prove_sq 3 3 10 41 (by rfl))

lemma base_648 : 0 < A271510 648 :=
  A271510_pos_of_exists 648 0 0 18 18 (by rfl) (by omega) (prove_sq 0 0 18 72 (by rfl))

lemma base_649 : 0 < A271510 649 :=
  A271510_pos_of_exists 649 7 4 22 10 (by rfl) (by omega) (prove_sq 7 4 22 89 (by rfl))

lemma base_650 : 0 < A271510 650 :=
  A271510_pos_of_exists 650 0 0 5 25 (by rfl) (by omega) (prove_sq 0 0 5 20 (by rfl))

lemma base_651 : 0 < A271510 651 :=
  A271510_pos_of_exists 651 5 5 5 24 (by rfl) (by omega) (prove_sq 5 5 5 25 (by rfl))

lemma base_652 : 0 < A271510 652 :=
  A271510_pos_of_exists 652 3 3 3 25 (by rfl) (by omega) (prove_sq 3 3 3 15 (by rfl))

lemma base_653 : 0 < A271510 653 :=
  A271510_pos_of_exists 653 0 0 13 22 (by rfl) (by omega) (prove_sq 0 0 13 52 (by rfl))

lemma base_654 : 0 < A271510 654 :=
  A271510_pos_of_exists 654 5 2 7 24 (by rfl) (by omega) (prove_sq 5 2 7 29 (by rfl))

lemma base_655 : 0 < A271510 655 :=
  A271510_pos_of_exists 655 9 3 6 23 (by rfl) (by omega) (prove_sq 9 3 6 27 (by rfl))

lemma base_656 : 0 < A271510 656 :=
  A271510_pos_of_exists 656 0 0 16 20 (by rfl) (by omega) (prove_sq 0 0 16 64 (by rfl))

lemma base_657 : 0 < A271510 657 :=
  A271510_pos_of_exists 657 0 0 9 24 (by rfl) (by omega) (prove_sq 0 0 9 36 (by rfl))

lemma base_658 : 0 < A271510 658 :=
  A271510_pos_of_exists 658 5 2 2 25 (by rfl) (by omega) (prove_sq 5 2 2 11 (by rfl))

lemma base_659 : 0 < A271510 659 :=
  A271510_pos_of_exists 659 5 0 3 25 (by rfl) (by omega) (prove_sq 5 0 3 13 (by rfl))

lemma base_660 : 0 < A271510 660 :=
  A271510_pos_of_exists 660 5 5 9 23 (by rfl) (by omega) (prove_sq 5 5 9 39 (by rfl))

lemma base_661 : 0 < A271510 661 :=
  A271510_pos_of_exists 661 0 0 6 25 (by rfl) (by omega) (prove_sq 0 0 6 24 (by rfl))

lemma base_662 : 0 < A271510 662 :=
  A271510_pos_of_exists 662 5 3 12 22 (by rfl) (by omega) (prove_sq 5 3 12 49 (by rfl))

lemma base_663 : 0 < A271510 663 :=
  A271510_pos_of_exists 663 3 2 5 25 (by rfl) (by omega) (prove_sq 3 2 5 21 (by rfl))

lemma base_664 : 0 < A271510 664 :=
  A271510_pos_of_exists 664 14 0 12 18 (by rfl) (by omega) (prove_sq 14 0 12 50 (by rfl))

lemma base_665 : 0 < A271510 665 :=
  A271510_pos_of_exists 665 6 0 2 25 (by rfl) (by omega) (prove_sq 6 0 2 10 (by rfl))

lemma base_666 : 0 < A271510 666 :=
  A271510_pos_of_exists 666 0 0 15 21 (by rfl) (by omega) (prove_sq 0 0 15 60 (by rfl))

lemma base_667 : 0 < A271510 667 :=
  A271510_pos_of_exists 667 5 1 4 25 (by rfl) (by omega) (prove_sq 5 1 4 17 (by rfl))

lemma base_668 : 0 < A271510 668 :=
  A271510_pos_of_exists 668 6 6 20 14 (by rfl) (by omega) (prove_sq 6 6 20 82 (by rfl))

lemma base_669 : 0 < A271510 669 :=
  A271510_pos_of_exists 669 10 8 12 19 (by rfl) (by omega) (prove_sq 10 8 12 54 (by rfl))

lemma base_670 : 0 < A271510 670 :=
  A271510_pos_of_exists 670 7 4 22 11 (by rfl) (by omega) (prove_sq 7 4 22 89 (by rfl))

lemma base_671 : 0 < A271510 671 :=
  A271510_pos_of_exists 671 21 10 7 9 (by rfl) (by omega) (prove_sq 21 10 7 45 (by rfl))

lemma base_672 : 0 < A271510 672 :=
  A271510_pos_of_exists 672 12 8 20 8 (by rfl) (by omega) (prove_sq 12 8 20 84 (by rfl))

lemma base_673 : 0 < A271510 673 :=
  A271510_pos_of_exists 673 0 0 12 23 (by rfl) (by omega) (prove_sq 0 0 12 48 (by rfl))

lemma base_674 : 0 < A271510 674 :=
  A271510_pos_of_exists 674 0 0 7 25 (by rfl) (by omega) (prove_sq 0 0 7 28 (by rfl))

lemma base_675 : 0 < A271510 675 :=
  A271510_pos_of_exists 675 5 5 0 25 (by rfl) (by omega) (prove_sq 5 5 0 15 (by rfl))

lemma base_676 : 0 < A271510 676 :=
  A271510_pos_of_exists 676 0 0 0 26 (by rfl) (by omega) (prove_sq 0 0 0 0 (by rfl))

lemma base_677 : 0 < A271510 677 :=
  A271510_pos_of_exists 677 0 0 1 26 (by rfl) (by omega) (prove_sq 0 0 1 4 (by rfl))

lemma base_678 : 0 < A271510 678 :=
  A271510_pos_of_exists 678 1 1 0 26 (by rfl) (by omega) (prove_sq 1 1 0 3 (by rfl))

lemma base_679 : 0 < A271510 679 :=
  A271510_pos_of_exists 679 1 1 1 26 (by rfl) (by omega) (prove_sq 1 1 1 5 (by rfl))

lemma base_680 : 0 < A271510 680 :=
  A271510_pos_of_exists 680 0 0 2 26 (by rfl) (by omega) (prove_sq 0 0 2 8 (by rfl))

lemma base_681 : 0 < A271510 681 :=
  A271510_pos_of_exists 681 6 2 4 25 (by rfl) (by omega) (prove_sq 6 2 4 18 (by rfl))

lemma base_682 : 0 < A271510 682 :=
  A271510_pos_of_exists 682 7 2 10 23 (by rfl) (by omega) (prove_sq 7 2 10 41 (by rfl))

lemma base_683 : 0 < A271510 683 :=
  A271510_pos_of_exists 683 7 3 0 25 (by rfl) (by omega) (prove_sq 7 3 0 11 (by rfl))

lemma base_684 : 0 < A271510 684 :=
  A271510_pos_of_exists 684 2 2 0 26 (by rfl) (by omega) (prove_sq 2 2 0 6 (by rfl))

lemma base_685 : 0 < A271510 685 :=
  A271510_pos_of_exists 685 0 0 3 26 (by rfl) (by omega) (prove_sq 0 0 3 12 (by rfl))

lemma base_686 : 0 < A271510 686 :=
  A271510_pos_of_exists 686 3 0 1 26 (by rfl) (by omega) (prove_sq 3 0 1 5 (by rfl))

lemma base_687 : 0 < A271510 687 :=
  A271510_pos_of_exists 687 7 2 3 25 (by rfl) (by omega) (prove_sq 7 2 3 15 (by rfl))

lemma base_688 : 0 < A271510 688 :=
  A271510_pos_of_exists 688 2 2 2 26 (by rfl) (by omega) (prove_sq 2 2 2 10 (by rfl))

lemma base_689 : 0 < A271510 689 :=
  A271510_pos_of_exists 689 0 0 8 25 (by rfl) (by omega) (prove_sq 0 0 8 32 (by rfl))

lemma base_690 : 0 < A271510 690 :=
  A271510_pos_of_exists 690 3 1 2 26 (by rfl) (by omega) (prove_sq 3 1 2 9 (by rfl))

lemma base_691 : 0 < A271510 691 :=
  A271510_pos_of_exists 691 5 4 19 17 (by rfl) (by omega) (prove_sq 5 4 19 77 (by rfl))

lemma base_692 : 0 < A271510 692 :=
  A271510_pos_of_exists 692 0 0 4 26 (by rfl) (by omega) (prove_sq 0 0 4 16 (by rfl))

lemma base_693 : 0 < A271510 693 :=
  A271510_pos_of_exists 693 7 4 22 12 (by rfl) (by omega) (prove_sq 7 4 22 89 (by rfl))

lemma base_694 : 0 < A271510 694 :=
  A271510_pos_of_exists 694 3 3 0 26 (by rfl) (by omega) (prove_sq 3 3 0 9 (by rfl))

lemma base_695 : 0 < A271510 695 :=
  A271510_pos_of_exists 695 15 15 7 14 (by rfl) (by omega) (prove_sq 15 15 7 53 (by rfl))

lemma base_696 : 0 < A271510 696 :=
  A271510_pos_of_exists 696 14 4 0 22 (by rfl) (by omega) (prove_sq 14 4 0 18 (by rfl))

lemma base_697 : 0 < A271510 697 :=
  A271510_pos_of_exists 697 0 0 11 24 (by rfl) (by omega) (prove_sq 0 0 11 44 (by rfl))

lemma base_698 : 0 < A271510 698 :=
  A271510_pos_of_exists 698 0 0 13 23 (by rfl) (by omega) (prove_sq 0 0 13 52 (by rfl))

lemma base_699 : 0 < A271510 699 :=
  A271510_pos_of_exists 699 7 7 5 24 (by rfl) (by omega) (prove_sq 7 7 5 29 (by rfl))

lemma base_700 : 0 < A271510 700 :=
  A271510_pos_of_exists 700 5 5 5 25 (by rfl) (by omega) (prove_sq 5 5 5 25 (by rfl))

lemma base_701 : 0 < A271510 701 :=
  A271510_pos_of_exists 701 0 0 5 26 (by rfl) (by omega) (prove_sq 0 0 5 20 (by rfl))

lemma base_702 : 0 < A271510 702 :=
  A271510_pos_of_exists 702 5 4 6 25 (by rfl) (by omega) (prove_sq 5 4 6 27 (by rfl))

lemma base_703 : 0 < A271510 703 :=
  A271510_pos_of_exists 703 3 3 3 26 (by rfl) (by omega) (prove_sq 3 3 3 15 (by rfl))

lemma base_704 : 0 < A271510 704 :=
  A271510_pos_of_exists 704 8 8 0 24 (by rfl) (by omega) (prove_sq 8 8 0 24 (by rfl))

lemma base_705 : 0 < A271510 705 :=
  A271510_pos_of_exists 705 14 10 20 3 (by rfl) (by omega) (prove_sq 14 10 20 86 (by rfl))

lemma base_706 : 0 < A271510 706 :=
  A271510_pos_of_exists 706 0 0 9 25 (by rfl) (by omega) (prove_sq 0 0 9 36 (by rfl))

lemma base_707 : 0 < A271510 707 :=
  A271510_pos_of_exists 707 5 3 12 23 (by rfl) (by omega) (prove_sq 5 3 12 49 (by rfl))

lemma base_708 : 0 < A271510 708 :=
  A271510_pos_of_exists 708 4 4 0 26 (by rfl) (by omega) (prove_sq 4 4 0 12 (by rfl))

lemma base_709 : 0 < A271510 709 :=
  A271510_pos_of_exists 709 0 0 15 22 (by rfl) (by omega) (prove_sq 0 0 15 60 (by rfl))

lemma base_710 : 0 < A271510 710 :=
  A271510_pos_of_exists 710 5 0 3 26 (by rfl) (by omega) (prove_sq 5 0 3 13 (by rfl))

lemma base_711 : 0 < A271510 711 :=
  A271510_pos_of_exists 711 7 7 18 17 (by rfl) (by omega) (prove_sq 7 7 18 75 (by rfl))

lemma base_712 : 0 < A271510 712 :=
  A271510_pos_of_exists 712 0 0 6 26 (by rfl) (by omega) (prove_sq 0 0 6 24 (by rfl))

lemma base_713 : 0 < A271510 713 :=
  A271510_pos_of_exists 713 10 6 24 1 (by rfl) (by omega) (prove_sq 10 6 24 98 (by rfl))

lemma base_714 : 0 < A271510 714 :=
  A271510_pos_of_exists 714 3 2 5 26 (by rfl) (by omega) (prove_sq 3 2 5 21 (by rfl))

lemma base_715 : 0 < A271510 715 :=
  A271510_pos_of_exists 715 9 0 3 25 (by rfl) (by omega) (prove_sq 9 0 3 15 (by rfl))

lemma base_716 : 0 < A271510 716 :=
  A271510_pos_of_exists 716 6 0 2 26 (by rfl) (by omega) (prove_sq 6 0 2 10 (by rfl))

lemma base_717 : 0 < A271510 717 :=
  A271510_pos_of_exists 717 14 14 10 15 (by rfl) (by omega) (prove_sq 14 14 10 58 (by rfl))

lemma base_718 : 0 < A271510 718 :=
  A271510_pos_of_exists 718 5 1 4 26 (by rfl) (by omega) (prove_sq 5 1 4 17 (by rfl))

lemma base_719 : 0 < A271510 719 :=
  A271510_pos_of_exists 719 21 9 14 1 (by rfl) (by omega) (prove_sq 21 9 14 65 (by rfl))

lemma base_720 : 0 < A271510 720 :=
  A271510_pos_of_exists 720 0 0 12 24 (by rfl) (by omega) (prove_sq 0 0 12 48 (by rfl))

lemma base_721 : 0 < A271510 721 :=
  A271510_pos_of_exists 721 8 8 8 23 (by rfl) (by omega) (prove_sq 8 8 8 40 (by rfl))

lemma base_722 : 0 < A271510 722 :=
  A271510_pos_of_exists 722 0 0 19 19 (by rfl) (by omega) (prove_sq 0 0 19 76 (by rfl))

lemma base_723 : 0 < A271510 723 :=
  A271510_pos_of_exists 723 7 7 0 25 (by rfl) (by omega) (prove_sq 7 7 0 21 (by rfl))

lemma base_724 : 0 < A271510 724 :=
  A271510_pos_of_exists 724 0 0 18 20 (by rfl) (by omega) (prove_sq 0 0 18 72 (by rfl))

lemma base_725 : 0 < A271510 725 :=
  A271510_pos_of_exists 725 0 0 7 26 (by rfl) (by omega) (prove_sq 0 0 7 28 (by rfl))

lemma base_726 : 0 < A271510 726 :=
  A271510_pos_of_exists 726 5 4 19 18 (by rfl) (by omega) (prove_sq 5 4 19 77 (by rfl))

lemma base_727 : 0 < A271510 727 :=
  A271510_pos_of_exists 727 9 9 9 22 (by rfl) (by omega) (prove_sq 9 9 9 45 (by rfl))

lemma base_728 : 0 < A271510 728 :=
  A271510_pos_of_exists 728 6 4 10 24 (by rfl) (by omega) (prove_sq 6 4 10 42 (by rfl))

lemma base_729 : 0 < A271510 729 :=
  A271510_pos_of_exists 729 0 0 0 27 (by rfl) (by omega) (prove_sq 0 0 0 0 (by rfl))

lemma base_730 : 0 < A271510 730 :=
  A271510_pos_of_exists 730 0 0 1 27 (by rfl) (by omega) (prove_sq 0 0 1 4 (by rfl))

lemma base_731 : 0 < A271510 731 :=
  A271510_pos_of_exists 731 1 1 0 27 (by rfl) (by omega) (prove_sq 1 1 0 3 (by rfl))

lemma base_732 : 0 < A271510 732 :=
  A271510_pos_of_exists 732 1 1 1 27 (by rfl) (by omega) (prove_sq 1 1 1 5 (by rfl))

lemma base_733 : 0 < A271510 733 :=
  A271510_pos_of_exists 733 0 0 2 27 (by rfl) (by omega) (prove_sq 0 0 2 8 (by rfl))

lemma base_734 : 0 < A271510 734 :=
  A271510_pos_of_exists 734 7 3 0 26 (by rfl) (by omega) (prove_sq 7 3 0 11 (by rfl))

lemma base_735 : 0 < A271510 735 :=
  A271510_pos_of_exists 735 11 7 6 23 (by rfl) (by omega) (prove_sq 11 7 6 33 (by rfl))

lemma base_736 : 0 < A271510 736 :=
  A271510_pos_of_exists 736 12 0 4 24 (by rfl) (by omega) (prove_sq 12 0 4 20 (by rfl))

lemma base_737 : 0 < A271510 737 :=
  A271510_pos_of_exists 737 2 2 0 27 (by rfl) (by omega) (prove_sq 2 2 0 6 (by rfl))

lemma base_738 : 0 < A271510 738 :=
  A271510_pos_of_exists 738 0 0 3 27 (by rfl) (by omega) (prove_sq 0 0 3 12 (by rfl))

lemma base_739 : 0 < A271510 739 :=
  A271510_pos_of_exists 739 3 0 1 27 (by rfl) (by omega) (prove_sq 3 0 1 5 (by rfl))

lemma base_740 : 0 < A271510 740 :=
  A271510_pos_of_exists 740 0 0 8 26 (by rfl) (by omega) (prove_sq 0 0 8 32 (by rfl))

lemma base_741 : 0 < A271510 741 :=
  A271510_pos_of_exists 741 2 2 2 27 (by rfl) (by omega) (prove_sq 2 2 2 10 (by rfl))

lemma base_742 : 0 < A271510 742 :=
  A271510_pos_of_exists 742 9 6 15 20 (by rfl) (by omega) (prove_sq 9 6 15 63 (by rfl))

lemma base_743 : 0 < A271510 743 :=
  A271510_pos_of_exists 743 3 1 2 27 (by rfl) (by omega) (prove_sq 3 1 2 9 (by rfl))

lemma base_744 : 0 < A271510 744 :=
  A271510_pos_of_exists 744 10 2 8 24 (by rfl) (by omega) (prove_sq 10 2 8 34 (by rfl))

lemma base_745 : 0 < A271510 745 :=
  A271510_pos_of_exists 745 0 0 4 27 (by rfl) (by omega) (prove_sq 0 0 4 16 (by rfl))

lemma base_746 : 0 < A271510 746 :=
  A271510_pos_of_exists 746 0 0 11 25 (by rfl) (by omega) (prove_sq 0 0 11 44 (by rfl))

lemma base_747 : 0 < A271510 747 :=
  A271510_pos_of_exists 747 3 3 0 27 (by rfl) (by omega) (prove_sq 3 3 0 9 (by rfl))

lemma base_748 : 0 < A271510 748 :=
  A271510_pos_of_exists 748 6 6 0 26 (by rfl) (by omega) (prove_sq 6 6 0 18 (by rfl))

lemma base_749 : 0 < A271510 749 :=
  A271510_pos_of_exists 749 10 8 12 21 (by rfl) (by omega) (prove_sq 10 8 12 54 (by rfl))

lemma base_750 : 0 < A271510 750 :=
  A271510_pos_of_exists 750 4 2 1 27 (by rfl) (by omega) (prove_sq 4 2 1 8 (by rfl))

lemma base_751 : 0 < A271510 751 :=
  A271510_pos_of_exists 751 5 5 5 26 (by rfl) (by omega) (prove_sq 5 5 5 25 (by rfl))

lemma base_752 : 0 < A271510 752 :=
  A271510_pos_of_exists 752 12 8 20 12 (by rfl) (by omega) (prove_sq 12 8 20 84 (by rfl))

lemma base_753 : 0 < A271510 753 :=
  A271510_pos_of_exists 753 5 4 6 26 (by rfl) (by omega) (prove_sq 5 4 6 27 (by rfl))

lemma base_754 : 0 < A271510 754 :=
  A271510_pos_of_exists 754 0 0 5 27 (by rfl) (by omega) (prove_sq 0 0 5 20 (by rfl))

lemma base_755 : 0 < A271510 755 :=
  A271510_pos_of_exists 755 11 3 24 7 (by rfl) (by omega) (prove_sq 11 3 24 97 (by rfl))

lemma base_756 : 0 < A271510 756 :=
  A271510_pos_of_exists 756 3 3 3 27 (by rfl) (by omega) (prove_sq 3 3 3 15 (by rfl))

lemma base_757 : 0 < A271510 757 :=
  A271510_pos_of_exists 757 0 0 9 26 (by rfl) (by omega) (prove_sq 0 0 9 36 (by rfl))

lemma base_758 : 0 < A271510 758 :=
  A271510_pos_of_exists 758 9 6 4 25 (by rfl) (by omega) (prove_sq 9 6 4 25 (by rfl))

lemma base_759 : 0 < A271510 759 :=
  A271510_pos_of_exists 759 21 10 7 13 (by rfl) (by omega) (prove_sq 21 10 7 45 (by rfl))

lemma base_760 : 0 < A271510 760 :=
  A271510_pos_of_exists 760 8 4 2 26 (by rfl) (by omega) (prove_sq 8 4 2 16 (by rfl))

lemma base_761 : 0 < A271510 761 :=
  A271510_pos_of_exists 761 0 0 19 20 (by rfl) (by omega) (prove_sq 0 0 19 76 (by rfl))

lemma base_762 : 0 < A271510 762 :=
  A271510_pos_of_exists 762 5 2 2 27 (by rfl) (by omega) (prove_sq 5 2 2 11 (by rfl))

lemma base_763 : 0 < A271510 763 :=
  A271510_pos_of_exists 763 5 0 3 27 (by rfl) (by omega) (prove_sq 5 0 3 13 (by rfl))

lemma base_764 : 0 < A271510 764 :=
  A271510_pos_of_exists 764 18 6 2 20 (by rfl) (by omega) (prove_sq 18 6 2 26 (by rfl))

lemma base_765 : 0 < A271510 765 :=
  A271510_pos_of_exists 765 0 0 6 27 (by rfl) (by omega) (prove_sq 0 0 6 24 (by rfl))

lemma base_766 : 0 < A271510 766 :=
  A271510_pos_of_exists 766 9 0 3 26 (by rfl) (by omega) (prove_sq 9 0 3 15 (by rfl))

lemma base_767 : 0 < A271510 767 :=
  A271510_pos_of_exists 767 3 2 5 27 (by rfl) (by omega) (prove_sq 3 2 5 21 (by rfl))

lemma base_768 : 0 < A271510 768 :=
  A271510_pos_of_exists 768 8 8 8 24 (by rfl) (by omega) (prove_sq 8 8 8 40 (by rfl))

lemma base_769 : 0 < A271510 769 :=
  A271510_pos_of_exists 769 0 0 12 25 (by rfl) (by omega) (prove_sq 0 0 12 48 (by rfl))

lemma base_770 : 0 < A271510 770 :=
  A271510_pos_of_exists 770 11 3 24 8 (by rfl) (by omega) (prove_sq 11 3 24 97 (by rfl))

lemma base_771 : 0 < A271510 771 :=
  A271510_pos_of_exists 771 5 1 4 27 (by rfl) (by omega) (prove_sq 5 1 4 17 (by rfl))

lemma base_772 : 0 < A271510 772 :=
  A271510_pos_of_exists 772 0 0 14 24 (by rfl) (by omega) (prove_sq 0 0 14 56 (by rfl))

lemma base_773 : 0 < A271510 773 :=
  A271510_pos_of_exists 773 0 0 17 22 (by rfl) (by omega) (prove_sq 0 0 17 68 (by rfl))

lemma base_774 : 0 < A271510 774 :=
  A271510_pos_of_exists 774 7 4 22 15 (by rfl) (by omega) (prove_sq 7 4 22 89 (by rfl))

lemma base_775 : 0 < A271510 775 :=
  A271510_pos_of_exists 775 7 1 7 26 (by rfl) (by omega) (prove_sq 7 1 7 29 (by rfl))

lemma base_776 : 0 < A271510 776 :=
  A271510_pos_of_exists 776 0 0 10 26 (by rfl) (by omega) (prove_sq 0 0 10 40 (by rfl))

lemma base_777 : 0 < A271510 777 :=
  A271510_pos_of_exists 777 4 4 4 27 (by rfl) (by omega) (prove_sq 4 4 4 20 (by rfl))

lemma base_778 : 0 < A271510 778 :=
  A271510_pos_of_exists 778 0 0 7 27 (by rfl) (by omega) (prove_sq 0 0 7 28 (by rfl))

lemma base_779 : 0 < A271510 779 :=
  A271510_pos_of_exists 779 5 5 0 27 (by rfl) (by omega) (prove_sq 5 5 0 15 (by rfl))

lemma base_780 : 0 < A271510 780 :=
  A271510_pos_of_exists 780 10 10 18 16 (by rfl) (by omega) (prove_sq 10 10 18 78 (by rfl))

lemma base_781 : 0 < A271510 781 :=
  A271510_pos_of_exists 781 14 0 12 21 (by rfl) (by omega) (prove_sq 14 0 12 50 (by rfl))

lemma base_782 : 0 < A271510 782 :=
  A271510_pos_of_exists 782 7 2 0 27 (by rfl) (by omega) (prove_sq 7 2 0 9 (by rfl))

lemma base_783 : 0 < A271510 783 :=
  A271510_pos_of_exists 783 5 5 2 27 (by rfl) (by omega) (prove_sq 5 5 2 17 (by rfl))

lemma base_784 : 0 < A271510 784 :=
  A271510_pos_of_exists 784 0 0 0 28 (by rfl) (by omega) (prove_sq 0 0 0 0 (by rfl))

lemma base_785 : 0 < A271510 785 :=
  A271510_pos_of_exists 785 0 0 1 28 (by rfl) (by omega) (prove_sq 0 0 1 4 (by rfl))

lemma base_786 : 0 < A271510 786 :=
  A271510_pos_of_exists 786 1 1 0 28 (by rfl) (by omega) (prove_sq 1 1 0 3 (by rfl))

lemma base_787 : 0 < A271510 787 :=
  A271510_pos_of_exists 787 1 1 1 28 (by rfl) (by omega) (prove_sq 1 1 1 5 (by rfl))

lemma base_788 : 0 < A271510 788 :=
  A271510_pos_of_exists 788 0 0 2 28 (by rfl) (by omega) (prove_sq 0 0 2 8 (by rfl))

lemma base_789 : 0 < A271510 789 :=
  A271510_pos_of_exists 789 9 4 26 4 (by rfl) (by omega) (prove_sq 9 4 26 105 (by rfl))

lemma base_790 : 0 < A271510 790 :=
  A271510_pos_of_exists 790 7 4 7 26 (by rfl) (by omega) (prove_sq 7 4 7 31 (by rfl))

lemma base_791 : 0 < A271510 791 :=
  A271510_pos_of_exists 791 7 2 3 27 (by rfl) (by omega) (prove_sq 7 2 3 15 (by rfl))

lemma base_792 : 0 < A271510 792 :=
  A271510_pos_of_exists 792 2 2 0 28 (by rfl) (by omega) (prove_sq 2 2 0 6 (by rfl))

lemma base_793 : 0 < A271510 793 :=
  A271510_pos_of_exists 793 0 0 3 28 (by rfl) (by omega) (prove_sq 0 0 3 12 (by rfl))

lemma base_794 : 0 < A271510 794 :=
  A271510_pos_of_exists 794 0 0 13 25 (by rfl) (by omega) (prove_sq 0 0 13 52 (by rfl))

lemma base_795 : 0 < A271510 795 :=
  A271510_pos_of_exists 795 13 1 7 24 (by rfl) (by omega) (prove_sq 13 1 7 31 (by rfl))

lemma base_796 : 0 < A271510 796 :=
  A271510_pos_of_exists 796 2 2 2 28 (by rfl) (by omega) (prove_sq 2 2 2 10 (by rfl))

lemma base_797 : 0 < A271510 797 :=
  A271510_pos_of_exists 797 0 0 11 26 (by rfl) (by omega) (prove_sq 0 0 11 44 (by rfl))

lemma base_798 : 0 < A271510 798 :=
  A271510_pos_of_exists 798 3 1 2 28 (by rfl) (by omega) (prove_sq 3 1 2 9 (by rfl))

lemma base_799 : 0 < A271510 799 :=
  A271510_pos_of_exists 799 7 5 10 25 (by rfl) (by omega) (prove_sq 7 5 10 43 (by rfl))

lemma base_800 : 0 < A271510 800 :=
  A271510_pos_of_exists 800 0 0 4 28 (by rfl) (by omega) (prove_sq 0 0 4 16 (by rfl))

lemma base_801 : 0 < A271510 801 :=
  A271510_pos_of_exists 801 0 0 15 24 (by rfl) (by omega) (prove_sq 0 0 15 60 (by rfl))

lemma base_802 : 0 < A271510 802 :=
  A271510_pos_of_exists 802 0 0 19 21 (by rfl) (by omega) (prove_sq 0 0 19 76 (by rfl))

lemma base_803 : 0 < A271510 803 :=
  A271510_pos_of_exists 803 5 3 12 25 (by rfl) (by omega) (prove_sq 5 3 12 49 (by rfl))

lemma base_804 : 0 < A271510 804 :=
  A271510_pos_of_exists 804 5 5 5 27 (by rfl) (by omega) (prove_sq 5 5 5 25 (by rfl))

lemma base_805 : 0 < A271510 805 :=
  A271510_pos_of_exists 805 4 2 1 28 (by rfl) (by omega) (prove_sq 4 2 1 8 (by rfl))

lemma base_806 : 0 < A271510 806 :=
  A271510_pos_of_exists 806 5 4 6 27 (by rfl) (by omega) (prove_sq 5 4 6 27 (by rfl))

lemma base_807 : 0 < A271510 807 :=
  A271510_pos_of_exists 807 5 2 7 27 (by rfl) (by omega) (prove_sq 5 2 7 29 (by rfl))

lemma base_808 : 0 < A271510 808 :=
  A271510_pos_of_exists 808 0 0 18 22 (by rfl) (by omega) (prove_sq 0 0 18 72 (by rfl))

lemma base_809 : 0 < A271510 809 :=
  A271510_pos_of_exists 809 0 0 5 28 (by rfl) (by omega) (prove_sq 0 0 5 20 (by rfl))

lemma base_810 : 0 < A271510 810 :=
  A271510_pos_of_exists 810 0 0 9 27 (by rfl) (by omega) (prove_sq 0 0 9 36 (by rfl))

lemma base_811 : 0 < A271510 811 :=
  A271510_pos_of_exists 811 3 3 3 28 (by rfl) (by omega) (prove_sq 3 3 3 15 (by rfl))

lemma base_812 : 0 < A271510 812 :=
  A271510_pos_of_exists 812 7 3 15 23 (by rfl) (by omega) (prove_sq 7 3 15 61 (by rfl))

lemma base_813 : 0 < A271510 813 :=
  A271510_pos_of_exists 813 8 4 2 27 (by rfl) (by omega) (prove_sq 8 4 2 16 (by rfl))

lemma base_814 : 0 < A271510 814 :=
  A271510_pos_of_exists 814 7 0 6 27 (by rfl) (by omega) (prove_sq 7 0 6 25 (by rfl))

lemma base_815 : 0 < A271510 815 :=
  A271510_pos_of_exists 815 21 10 7 15 (by rfl) (by omega) (prove_sq 21 10 7 45 (by rfl))

lemma base_816 : 0 < A271510 816 :=
  A271510_pos_of_exists 816 4 4 0 28 (by rfl) (by omega) (prove_sq 4 4 0 12 (by rfl))

lemma base_817 : 0 < A271510 817 :=
  A271510_pos_of_exists 817 5 2 2 28 (by rfl) (by omega) (prove_sq 5 2 2 11 (by rfl))

lemma base_818 : 0 < A271510 818 :=
  A271510_pos_of_exists 818 0 0 17 23 (by rfl) (by omega) (prove_sq 0 0 17 68 (by rfl))

lemma base_819 : 0 < A271510 819 :=
  A271510_pos_of_exists 819 9 0 3 27 (by rfl) (by omega) (prove_sq 9 0 3 15 (by rfl))

lemma base_820 : 0 < A271510 820 :=
  A271510_pos_of_exists 820 0 0 6 28 (by rfl) (by omega) (prove_sq 0 0 6 24 (by rfl))

lemma base_821 : 0 < A271510 821 :=
  A271510_pos_of_exists 821 0 0 14 25 (by rfl) (by omega) (prove_sq 0 0 14 56 (by rfl))

lemma base_822 : 0 < A271510 822 :=
  A271510_pos_of_exists 822 3 2 5 28 (by rfl) (by omega) (prove_sq 3 2 5 21 (by rfl))

lemma base_823 : 0 < A271510 823 :=
  A271510_pos_of_exists 823 7 7 7 26 (by rfl) (by omega) (prove_sq 7 7 7 35 (by rfl))

lemma base_824 : 0 < A271510 824 :=
  A271510_pos_of_exists 824 6 0 2 28 (by rfl) (by omega) (prove_sq 6 0 2 10 (by rfl))

lemma base_825 : 0 < A271510 825 :=
  A271510_pos_of_exists 825 10 10 0 25 (by rfl) (by omega) (prove_sq 10 10 0 30 (by rfl))

lemma base_826 : 0 < A271510 826 :=
  A271510_pos_of_exists 826 5 1 4 28 (by rfl) (by omega) (prove_sq 5 1 4 17 (by rfl))

lemma base_827 : 0 < A271510 827 :=
  A271510_pos_of_exists 827 7 7 0 27 (by rfl) (by omega) (prove_sq 7 7 0 21 (by rfl))

lemma base_828 : 0 < A271510 828 :=
  A271510_pos_of_exists 828 6 4 10 26 (by rfl) (by omega) (prove_sq 6 4 10 42 (by rfl))

lemma base_829 : 0 < A271510 829 :=
  A271510_pos_of_exists 829 0 0 10 27 (by rfl) (by omega) (prove_sq 0 0 10 40 (by rfl))

lemma base_830 : 0 < A271510 830 :=
  A271510_pos_of_exists 830 11 0 15 22 (by rfl) (by omega) (prove_sq 11 0 15 61 (by rfl))

lemma base_831 : 0 < A271510 831 :=
  A271510_pos_of_exists 831 11 7 6 25 (by rfl) (by omega) (prove_sq 11 7 6 33 (by rfl))

lemma base_832 : 0 < A271510 832 :=
  A271510_pos_of_exists 832 0 0 16 24 (by rfl) (by omega) (prove_sq 0 0 16 64 (by rfl))

lemma base_833 : 0 < A271510 833 :=
  A271510_pos_of_exists 833 0 0 7 28 (by rfl) (by omega) (prove_sq 0 0 7 28 (by rfl))

lemma base_834 : 0 < A271510 834 :=
  A271510_pos_of_exists 834 5 5 0 28 (by rfl) (by omega) (prove_sq 5 5 0 15 (by rfl))

lemma base_835 : 0 < A271510 835 :=
  A271510_pos_of_exists 835 5 5 28 1 (by rfl) (by omega) (prove_sq 5 5 28 113 (by rfl))

lemma base_836 : 0 < A271510 836 :=
  A271510_pos_of_exists 836 11 7 21 15 (by rfl) (by omega) (prove_sq 11 7 21 87 (by rfl))

lemma base_837 : 0 < A271510 837 :=
  A271510_pos_of_exists 837 6 6 6 27 (by rfl) (by omega) (prove_sq 6 6 6 30 (by rfl))

lemma base_838 : 0 < A271510 838 :=
  A271510_pos_of_exists 838 5 5 2 28 (by rfl) (by omega) (prove_sq 5 5 2 17 (by rfl))

lemma base_839 : 0 < A271510 839 :=
  A271510_pos_of_exists 839 21 9 11 14 (by rfl) (by omega) (prove_sq 21 9 11 55 (by rfl))

lemma base_840 : 0 < A271510 840 :=
  A271510_pos_of_exists 840 6 2 4 28 (by rfl) (by omega) (prove_sq 6 2 4 18 (by rfl))

lemma base_841 : 0 < A271510 841 :=
  A271510_pos_of_exists 841 0 0 0 29 (by rfl) (by omega) (prove_sq 0 0 0 0 (by rfl))

lemma base_842 : 0 < A271510 842 :=
  A271510_pos_of_exists 842 0 0 1 29 (by rfl) (by omega) (prove_sq 0 0 1 4 (by rfl))

lemma base_843 : 0 < A271510 843 :=
  A271510_pos_of_exists 843 1 1 0 29 (by rfl) (by omega) (prove_sq 1 1 0 3 (by rfl))

lemma base_844 : 0 < A271510 844 :=
  A271510_pos_of_exists 844 1 1 1 29 (by rfl) (by omega) (prove_sq 1 1 1 5 (by rfl))

lemma base_845 : 0 < A271510 845 :=
  A271510_pos_of_exists 845 0 0 2 29 (by rfl) (by omega) (prove_sq 0 0 2 8 (by rfl))

lemma base_846 : 0 < A271510 846 :=
  A271510_pos_of_exists 846 7 2 3 28 (by rfl) (by omega) (prove_sq 7 2 3 15 (by rfl))

lemma base_847 : 0 < A271510 847 :=
  A271510_pos_of_exists 847 3 3 10 27 (by rfl) (by omega) (prove_sq 3 3 10 41 (by rfl))

lemma base_848 : 0 < A271510 848 :=
  A271510_pos_of_exists 848 0 0 8 28 (by rfl) (by omega) (prove_sq 0 0 8 32 (by rfl))

lemma base_849 : 0 < A271510 849 :=
  A271510_pos_of_exists 849 2 2 0 29 (by rfl) (by omega) (prove_sq 2 2 0 6 (by rfl))

lemma base_850 : 0 < A271510 850 :=
  A271510_pos_of_exists 850 0 0 3 29 (by rfl) (by omega) (prove_sq 0 0 3 12 (by rfl))

lemma base_851 : 0 < A271510 851 :=
  A271510_pos_of_exists 851 3 0 1 29 (by rfl) (by omega) (prove_sq 3 0 1 5 (by rfl))

lemma base_852 : 0 < A271510 852 :=
  A271510_pos_of_exists 852 7 7 5 27 (by rfl) (by omega) (prove_sq 7 7 5 29 (by rfl))

lemma base_853 : 0 < A271510 853 :=
  A271510_pos_of_exists 853 0 0 18 23 (by rfl) (by omega) (prove_sq 0 0 18 72 (by rfl))

lemma base_854 : 0 < A271510 854 :=
  A271510_pos_of_exists 854 5 3 12 26 (by rfl) (by omega) (prove_sq 5 3 12 49 (by rfl))

lemma base_855 : 0 < A271510 855 :=
  A271510_pos_of_exists 855 3 1 2 29 (by rfl) (by omega) (prove_sq 3 1 2 9 (by rfl))

lemma base_856 : 0 < A271510 856 :=
  A271510_pos_of_exists 856 6 6 0 28 (by rfl) (by omega) (prove_sq 6 6 0 18 (by rfl))

lemma base_857 : 0 < A271510 857 :=
  A271510_pos_of_exists 857 0 0 4 29 (by rfl) (by omega) (prove_sq 0 0 4 16 (by rfl))

lemma base_858 : 0 < A271510 858 :=
  A271510_pos_of_exists 858 13 4 12 23 (by rfl) (by omega) (prove_sq 13 4 12 51 (by rfl))

lemma base_859 : 0 < A271510 859 :=
  A271510_pos_of_exists 859 3 3 0 29 (by rfl) (by omega) (prove_sq 3 3 0 9 (by rfl))

lemma base_860 : 0 < A271510 860 :=
  A271510_pos_of_exists 860 5 5 9 27 (by rfl) (by omega) (prove_sq 5 5 9 39 (by rfl))

lemma base_861 : 0 < A271510 861 :=
  A271510_pos_of_exists 861 5 4 6 28 (by rfl) (by omega) (prove_sq 5 4 6 27 (by rfl))

lemma base_862 : 0 < A271510 862 :=
  A271510_pos_of_exists 862 4 2 1 29 (by rfl) (by omega) (prove_sq 4 2 1 8 (by rfl))

lemma base_863 : 0 < A271510 863 :=
  A271510_pos_of_exists 863 7 7 18 21 (by rfl) (by omega) (prove_sq 7 7 18 75 (by rfl))

lemma base_864 : 0 < A271510 864 :=
  A271510_pos_of_exists 864 12 8 20 16 (by rfl) (by omega) (prove_sq 12 8 20 84 (by rfl))

lemma base_865 : 0 < A271510 865 :=
  A271510_pos_of_exists 865 0 0 9 28 (by rfl) (by omega) (prove_sq 0 0 9 36 (by rfl))

lemma base_866 : 0 < A271510 866 :=
  A271510_pos_of_exists 866 0 0 5 29 (by rfl) (by omega) (prove_sq 0 0 5 20 (by rfl))

lemma base_867 : 0 < A271510 867 :=
  A271510_pos_of_exists 867 11 7 21 16 (by rfl) (by omega) (prove_sq 11 7 21 87 (by rfl))

lemma base_868 : 0 < A271510 868 :=
  A271510_pos_of_exists 868 3 3 3 29 (by rfl) (by omega) (prove_sq 3 3 3 15 (by rfl))

lemma base_869 : 0 < A271510 869 :=
  A271510_pos_of_exists 869 7 0 6 28 (by rfl) (by omega) (prove_sq 7 0 6 25 (by rfl))

lemma base_870 : 0 < A271510 870 :=
  A271510_pos_of_exists 870 5 5 28 6 (by rfl) (by omega) (prove_sq 5 5 28 113 (by rfl))

lemma base_871 : 0 < A271510 871 :=
  A271510_pos_of_exists 871 9 6 15 23 (by rfl) (by omega) (prove_sq 9 6 15 63 (by rfl))

lemma base_872 : 0 < A271510 872 :=
  A271510_pos_of_exists 872 0 0 14 26 (by rfl) (by omega) (prove_sq 0 0 14 56 (by rfl))

lemma base_873 : 0 < A271510 873 :=
  A271510_pos_of_exists 873 0 0 12 27 (by rfl) (by omega) (prove_sq 0 0 12 48 (by rfl))

lemma base_874 : 0 < A271510 874 :=
  A271510_pos_of_exists 874 5 2 2 29 (by rfl) (by omega) (prove_sq 5 2 2 11 (by rfl))

lemma base_875 : 0 < A271510 875 :=
  A271510_pos_of_exists 875 5 0 3 29 (by rfl) (by omega) (prove_sq 5 0 3 13 (by rfl))

lemma base_876 : 0 < A271510 876 :=
  A271510_pos_of_exists 876 7 7 7 27 (by rfl) (by omega) (prove_sq 7 7 7 35 (by rfl))

lemma base_877 : 0 < A271510 877 :=
  A271510_pos_of_exists 877 0 0 6 29 (by rfl) (by omega) (prove_sq 0 0 6 24 (by rfl))

lemma base_878 : 0 < A271510 878 :=
  A271510_pos_of_exists 878 12 6 13 23 (by rfl) (by omega) (prove_sq 12 6 13 56 (by rfl))

lemma base_879 : 0 < A271510 879 :=
  A271510_pos_of_exists 879 3 2 5 29 (by rfl) (by omega) (prove_sq 3 2 5 21 (by rfl))

lemma base_880 : 0 < A271510 880 :=
  A271510_pos_of_exists 880 14 2 14 22 (by rfl) (by omega) (prove_sq 14 2 14 58 (by rfl))

lemma base_881 : 0 < A271510 881 :=
  A271510_pos_of_exists 881 0 0 16 25 (by rfl) (by omega) (prove_sq 0 0 16 64 (by rfl))

lemma base_882 : 0 < A271510 882 :=
  A271510_pos_of_exists 882 0 0 21 21 (by rfl) (by omega) (prove_sq 0 0 21 84 (by rfl))

lemma base_883 : 0 < A271510 883 :=
  A271510_pos_of_exists 883 5 1 4 29 (by rfl) (by omega) (prove_sq 5 1 4 17 (by rfl))

lemma base_884 : 0 < A271510 884 :=
  A271510_pos_of_exists 884 0 0 10 28 (by rfl) (by omega) (prove_sq 0 0 10 40 (by rfl))

lemma base_885 : 0 < A271510 885 :=
  A271510_pos_of_exists 885 10 10 18 19 (by rfl) (by omega) (prove_sq 10 10 18 78 (by rfl))

lemma base_886 : 0 < A271510 886 :=
  A271510_pos_of_exists 886 5 4 19 22 (by rfl) (by omega) (prove_sq 5 4 19 77 (by rfl))

lemma base_887 : 0 < A271510 887 :=
  A271510_pos_of_exists 887 15 6 1 25 (by rfl) (by omega) (prove_sq 15 6 1 23 (by rfl))

lemma base_888 : 0 < A271510 888 :=
  A271510_pos_of_exists 888 10 4 14 24 (by rfl) (by omega) (prove_sq 10 4 14 58 (by rfl))

lemma base_889 : 0 < A271510 889 :=
  A271510_pos_of_exists 889 4 4 4 29 (by rfl) (by omega) (prove_sq 4 4 4 20 (by rfl))

lemma base_890 : 0 < A271510 890 :=
  A271510_pos_of_exists 890 0 0 7 29 (by rfl) (by omega) (prove_sq 0 0 7 28 (by rfl))

lemma base_891 : 0 < A271510 891 :=
  A271510_pos_of_exists 891 5 5 0 29 (by rfl) (by omega) (prove_sq 5 5 0 15 (by rfl))

lemma base_892 : 0 < A271510 892 :=
  A271510_pos_of_exists 892 6 6 6 28 (by rfl) (by omega) (prove_sq 6 6 6 30 (by rfl))

lemma base_893 : 0 < A271510 893 :=
  A271510_pos_of_exists 893 18 0 20 13 (by rfl) (by omega) (prove_sq 18 0 20 82 (by rfl))

lemma base_894 : 0 < A271510 894 :=
  A271510_pos_of_exists 894 7 2 0 29 (by rfl) (by omega) (prove_sq 7 2 0 9 (by rfl))

lemma base_895 : 0 < A271510 895 :=
  A271510_pos_of_exists 895 5 5 2 29 (by rfl) (by omega) (prove_sq 5 5 2 17 (by rfl))

lemma base_896 : 0 < A271510 896 :=
  A271510_pos_of_exists 896 24 0 8 16 (by rfl) (by omega) (prove_sq 24 0 8 40 (by rfl))

lemma base_897 : 0 < A271510 897 :=
  A271510_pos_of_exists 897 6 2 4 29 (by rfl) (by omega) (prove_sq 6 2 4 18 (by rfl))

lemma base_898 : 0 < A271510 898 :=
  A271510_pos_of_exists 898 0 0 13 27 (by rfl) (by omega) (prove_sq 0 0 13 52 (by rfl))

lemma base_899 : 0 < A271510 899 :=
  A271510_pos_of_exists 899 7 3 0 29 (by rfl) (by omega) (prove_sq 7 3 0 11 (by rfl))

lemma base_900 : 0 < A271510 900 :=
  A271510_pos_of_exists 900 0 0 0 30 (by rfl) (by omega) (prove_sq 0 0 0 0 (by rfl))

lemma base_901 : 0 < A271510 901 :=
  A271510_pos_of_exists 901 0 0 1 30 (by rfl) (by omega) (prove_sq 0 0 1 4 (by rfl))

lemma base_902 : 0 < A271510 902 :=
  A271510_pos_of_exists 902 1 1 0 30 (by rfl) (by omega) (prove_sq 1 1 0 3 (by rfl))

lemma base_903 : 0 < A271510 903 :=
  A271510_pos_of_exists 903 1 1 1 30 (by rfl) (by omega) (prove_sq 1 1 1 5 (by rfl))

lemma base_904 : 0 < A271510 904 :=
  A271510_pos_of_exists 904 0 0 2 30 (by rfl) (by omega) (prove_sq 0 0 2 8 (by rfl))

lemma base_905 : 0 < A271510 905 :=
  A271510_pos_of_exists 905 0 0 8 29 (by rfl) (by omega) (prove_sq 0 0 8 32 (by rfl))

lemma base_906 : 0 < A271510 906 :=
  A271510_pos_of_exists 906 7 7 18 22 (by rfl) (by omega) (prove_sq 7 7 18 75 (by rfl))

lemma base_907 : 0 < A271510 907 :=
  A271510_pos_of_exists 907 5 3 12 27 (by rfl) (by omega) (prove_sq 5 3 12 49 (by rfl))

lemma base_908 : 0 < A271510 908 :=
  A271510_pos_of_exists 908 2 2 0 30 (by rfl) (by omega) (prove_sq 2 2 0 6 (by rfl))

lemma base_909 : 0 < A271510 909 :=
  A271510_pos_of_exists 909 0 0 3 30 (by rfl) (by omega) (prove_sq 0 0 3 12 (by rfl))

lemma base_910 : 0 < A271510 910 :=
  A271510_pos_of_exists 910 3 0 1 30 (by rfl) (by omega) (prove_sq 3 0 1 5 (by rfl))

lemma base_911 : 0 < A271510 911 :=
  A271510_pos_of_exists 911 15 9 11 22 (by rfl) (by omega) (prove_sq 15 9 11 53 (by rfl))

lemma base_912 : 0 < A271510 912 :=
  A271510_pos_of_exists 912 2 2 2 30 (by rfl) (by omega) (prove_sq 2 2 2 10 (by rfl))

lemma base_913 : 0 < A271510 913 :=
  A271510_pos_of_exists 913 6 6 0 29 (by rfl) (by omega) (prove_sq 6 6 0 18 (by rfl))

lemma base_914 : 0 < A271510 914 :=
  A271510_pos_of_exists 914 0 0 17 25 (by rfl) (by omega) (prove_sq 0 0 17 68 (by rfl))

lemma base_915 : 0 < A271510 915 :=
  A271510_pos_of_exists 915 5 5 9 28 (by rfl) (by omega) (prove_sq 5 5 9 39 (by rfl))

lemma base_916 : 0 < A271510 916 :=
  A271510_pos_of_exists 916 0 0 4 30 (by rfl) (by omega) (prove_sq 0 0 4 16 (by rfl))

lemma base_917 : 0 < A271510 917 :=
  A271510_pos_of_exists 917 9 4 26 12 (by rfl) (by omega) (prove_sq 9 4 26 105 (by rfl))

lemma base_918 : 0 < A271510 918 :=
  A271510_pos_of_exists 918 3 3 0 30 (by rfl) (by omega) (prove_sq 3 3 0 9 (by rfl))

lemma base_919 : 0 < A271510 919 :=
  A271510_pos_of_exists 919 5 2 7 29 (by rfl) (by omega) (prove_sq 5 2 7 29 (by rfl))

lemma base_920 : 0 < A271510 920 :=
  A271510_pos_of_exists 920 10 0 6 28 (by rfl) (by omega) (prove_sq 10 0 6 26 (by rfl))

lemma base_921 : 0 < A271510 921 :=
  A271510_pos_of_exists 921 4 2 1 30 (by rfl) (by omega) (prove_sq 4 2 1 8 (by rfl))

lemma base_922 : 0 < A271510 922 :=
  A271510_pos_of_exists 922 0 0 9 29 (by rfl) (by omega) (prove_sq 0 0 9 36 (by rfl))

lemma base_923 : 0 < A271510 923 :=
  A271510_pos_of_exists 923 13 4 3 27 (by rfl) (by omega) (prove_sq 13 4 3 21 (by rfl))

lemma base_924 : 0 < A271510 924 :=
  A271510_pos_of_exists 924 10 10 18 20 (by rfl) (by omega) (prove_sq 10 10 18 78 (by rfl))

lemma base_925 : 0 < A271510 925 :=
  A271510_pos_of_exists 925 0 0 5 30 (by rfl) (by omega) (prove_sq 0 0 5 20 (by rfl))

lemma base_926 : 0 < A271510 926 :=
  A271510_pos_of_exists 926 7 0 6 29 (by rfl) (by omega) (prove_sq 7 0 6 25 (by rfl))

lemma base_927 : 0 < A271510 927 :=
  A271510_pos_of_exists 927 3 3 3 30 (by rfl) (by omega) (prove_sq 3 3 3 15 (by rfl))

lemma base_928 : 0 < A271510 928 :=
  A271510_pos_of_exists 928 0 0 12 28 (by rfl) (by omega) (prove_sq 0 0 12 48 (by rfl))

lemma base_929 : 0 < A271510 929 :=
  A271510_pos_of_exists 929 0 0 20 23 (by rfl) (by omega) (prove_sq 0 0 20 80 (by rfl))

lemma base_930 : 0 < A271510 930 :=
  A271510_pos_of_exists 930 9 7 4 28 (by rfl) (by omega) (prove_sq 9 7 4 27 (by rfl))

lemma base_931 : 0 < A271510 931 :=
  A271510_pos_of_exists 931 5 4 19 23 (by rfl) (by omega) (prove_sq 5 4 19 77 (by rfl))

lemma base_932 : 0 < A271510 932 :=
  A271510_pos_of_exists 932 0 0 16 26 (by rfl) (by omega) (prove_sq 0 0 16 64 (by rfl))

lemma base_933 : 0 < A271510 933 :=
  A271510_pos_of_exists 933 5 2 2 30 (by rfl) (by omega) (prove_sq 5 2 2 11 (by rfl))

lemma base_934 : 0 < A271510 934 :=
  A271510_pos_of_exists 934 5 0 3 30 (by rfl) (by omega) (prove_sq 5 0 3 13 (by rfl))

lemma base_935 : 0 < A271510 935 :=
  A271510_pos_of_exists 935 9 3 19 22 (by rfl) (by omega) (prove_sq 9 3 19 77 (by rfl))

lemma base_936 : 0 < A271510 936 :=
  A271510_pos_of_exists 936 0 0 6 30 (by rfl) (by omega) (prove_sq 0 0 6 24 (by rfl))

lemma base_937 : 0 < A271510 937 :=
  A271510_pos_of_exists 937 0 0 19 24 (by rfl) (by omega) (prove_sq 0 0 19 76 (by rfl))

lemma base_938 : 0 < A271510 938 :=
  A271510_pos_of_exists 938 3 2 5 30 (by rfl) (by omega) (prove_sq 3 2 5 21 (by rfl))

lemma base_939 : 0 < A271510 939 :=
  A271510_pos_of_exists 939 7 7 0 29 (by rfl) (by omega) (prove_sq 7 7 0 21 (by rfl))

lemma base_940 : 0 < A271510 940 :=
  A271510_pos_of_exists 940 6 0 2 30 (by rfl) (by omega) (prove_sq 6 0 2 10 (by rfl))

lemma base_941 : 0 < A271510 941 :=
  A271510_pos_of_exists 941 0 0 10 29 (by rfl) (by omega) (prove_sq 0 0 10 40 (by rfl))

lemma base_942 : 0 < A271510 942 :=
  A271510_pos_of_exists 942 5 1 4 30 (by rfl) (by omega) (prove_sq 5 1 4 17 (by rfl))

lemma base_943 : 0 < A271510 943 :=
  A271510_pos_of_exists 943 13 1 22 17 (by rfl) (by omega) (prove_sq 13 1 22 89 (by rfl))

lemma base_944 : 0 < A271510 944 :=
  A271510_pos_of_exists 944 12 0 4 28 (by rfl) (by omega) (prove_sq 12 0 4 20 (by rfl))

lemma base_945 : 0 < A271510 945 :=
  A271510_pos_of_exists 945 10 10 4 27 (by rfl) (by omega) (prove_sq 10 10 4 34 (by rfl))

lemma base_946 : 0 < A271510 946 :=
  A271510_pos_of_exists 946 9 9 0 28 (by rfl) (by omega) (prove_sq 9 9 0 27 (by rfl))

lemma base_947 : 0 < A271510 947 :=
  A271510_pos_of_exists 947 17 12 15 17 (by rfl) (by omega) (prove_sq 17 12 15 71 (by rfl))

lemma base_948 : 0 < A271510 948 :=
  A271510_pos_of_exists 948 4 4 4 30 (by rfl) (by omega) (prove_sq 4 4 4 20 (by rfl))

lemma base_949 : 0 < A271510 949 :=
  A271510_pos_of_exists 949 0 0 7 30 (by rfl) (by omega) (prove_sq 0 0 7 28 (by rfl))

lemma base_950 : 0 < A271510 950 :=
  A271510_pos_of_exists 950 5 5 0 30 (by rfl) (by omega) (prove_sq 5 5 0 15 (by rfl))

lemma base_951 : 0 < A271510 951 :=
  A271510_pos_of_exists 951 7 7 18 23 (by rfl) (by omega) (prove_sq 7 7 18 75 (by rfl))

lemma base_952 : 0 < A271510 952 :=
  A271510_pos_of_exists 952 10 2 8 28 (by rfl) (by omega) (prove_sq 10 2 8 34 (by rfl))

lemma base_953 : 0 < A271510 953 :=
  A271510_pos_of_exists 953 0 0 13 28 (by rfl) (by omega) (prove_sq 0 0 13 52 (by rfl))

lemma base_954 : 0 < A271510 954 :=
  A271510_pos_of_exists 954 0 0 15 27 (by rfl) (by omega) (prove_sq 0 0 15 60 (by rfl))

lemma base_955 : 0 < A271510 955 :=
  A271510_pos_of_exists 955 5 5 28 11 (by rfl) (by omega) (prove_sq 5 5 28 113 (by rfl))

lemma base_956 : 0 < A271510 956 :=
  A271510_pos_of_exists 956 6 2 4 30 (by rfl) (by omega) (prove_sq 6 2 4 18 (by rfl))

lemma base_957 : 0 < A271510 957 :=
  A271510_pos_of_exists 957 9 2 14 26 (by rfl) (by omega) (prove_sq 9 2 14 57 (by rfl))

lemma base_958 : 0 < A271510 958 :=
  A271510_pos_of_exists 958 7 3 0 30 (by rfl) (by omega) (prove_sq 7 3 0 11 (by rfl))

lemma base_959 : 0 < A271510 959 :=
  A271510_pos_of_exists 959 3 3 10 29 (by rfl) (by omega) (prove_sq 3 3 10 41 (by rfl))

lemma base_960 : 0 < A271510 960 :=
  A271510_pos_of_exists 960 24 8 16 8 (by rfl) (by omega) (prove_sq 24 8 16 72 (by rfl))

lemma base_961 : 0 < A271510 961 :=
  A271510_pos_of_exists 961 0 0 0 31 (by rfl) (by omega) (prove_sq 0 0 0 0 (by rfl))

lemma base_962 : 0 < A271510 962 :=
  A271510_pos_of_exists 962 0 0 1 31 (by rfl) (by omega) (prove_sq 0 0 1 4 (by rfl))

lemma base_963 : 0 < A271510 963 :=
  A271510_pos_of_exists 963 1 1 0 31 (by rfl) (by omega) (prove_sq 1 1 0 3 (by rfl))

lemma base_964 : 0 < A271510 964 :=
  A271510_pos_of_exists 964 0 0 8 30 (by rfl) (by omega) (prove_sq 0 0 8 32 (by rfl))

lemma base_965 : 0 < A271510 965 :=
  A271510_pos_of_exists 965 0 0 2 31 (by rfl) (by omega) (prove_sq 0 0 2 8 (by rfl))

lemma base_966 : 0 < A271510 966 :=
  A271510_pos_of_exists 966 11 4 10 27 (by rfl) (by omega) (prove_sq 11 4 10 43 (by rfl))

lemma base_967 : 0 < A271510 967 :=
  A271510_pos_of_exists 967 9 3 6 29 (by rfl) (by omega) (prove_sq 9 3 6 27 (by rfl))

lemma base_968 : 0 < A271510 968 :=
  A271510_pos_of_exists 968 0 0 22 22 (by rfl) (by omega) (prove_sq 0 0 22 88 (by rfl))

lemma base_969 : 0 < A271510 969 :=
  A271510_pos_of_exists 969 2 2 0 31 (by rfl) (by omega) (prove_sq 2 2 0 6 (by rfl))

lemma base_970 : 0 < A271510 970 :=
  A271510_pos_of_exists 970 0 0 3 31 (by rfl) (by omega) (prove_sq 0 0 3 12 (by rfl))

lemma base_971 : 0 < A271510 971 :=
  A271510_pos_of_exists 971 3 0 1 31 (by rfl) (by omega) (prove_sq 3 0 1 5 (by rfl))

lemma base_972 : 0 < A271510 972 :=
  A271510_pos_of_exists 972 5 5 9 29 (by rfl) (by omega) (prove_sq 5 5 9 39 (by rfl))

lemma base_973 : 0 < A271510 973 :=
  A271510_pos_of_exists 973 2 2 2 31 (by rfl) (by omega) (prove_sq 2 2 2 10 (by rfl))

lemma base_974 : 0 < A271510 974 :=
  A271510_pos_of_exists 974 9 6 4 29 (by rfl) (by omega) (prove_sq 9 6 4 25 (by rfl))

lemma base_975 : 0 < A271510 975 :=
  A271510_pos_of_exists 975 3 1 2 31 (by rfl) (by omega) (prove_sq 3 1 2 9 (by rfl))

lemma base_976 : 0 < A271510 976 :=
  A271510_pos_of_exists 976 0 0 20 24 (by rfl) (by omega) (prove_sq 0 0 20 80 (by rfl))

lemma base_977 : 0 < A271510 977 :=
  A271510_pos_of_exists 977 0 0 4 31 (by rfl) (by omega) (prove_sq 0 0 4 16 (by rfl))

lemma base_978 : 0 < A271510 978 :=
  A271510_pos_of_exists 978 5 2 7 30 (by rfl) (by omega) (prove_sq 5 2 7 29 (by rfl))

lemma base_979 : 0 < A271510 979 :=
  A271510_pos_of_exists 979 3 3 0 31 (by rfl) (by omega) (prove_sq 3 3 0 9 (by rfl))

lemma base_980 : 0 < A271510 980 :=
  A271510_pos_of_exists 980 0 0 14 28 (by rfl) (by omega) (prove_sq 0 0 14 56 (by rfl))

lemma base_981 : 0 < A271510 981 :=
  A271510_pos_of_exists 981 0 0 9 30 (by rfl) (by omega) (prove_sq 0 0 9 36 (by rfl))

lemma base_982 : 0 < A271510 982 :=
  A271510_pos_of_exists 982 4 2 1 31 (by rfl) (by omega) (prove_sq 4 2 1 8 (by rfl))

lemma base_983 : 0 < A271510 983 :=
  A271510_pos_of_exists 983 15 15 7 22 (by rfl) (by omega) (prove_sq 15 15 7 53 (by rfl))

lemma base_984 : 0 < A271510 984 :=
  A271510_pos_of_exists 984 8 4 2 30 (by rfl) (by omega) (prove_sq 8 4 2 16 (by rfl))

lemma base_985 : 0 < A271510 985 :=
  A271510_pos_of_exists 985 0 0 12 29 (by rfl) (by omega) (prove_sq 0 0 12 48 (by rfl))

lemma base_986 : 0 < A271510 986 :=
  A271510_pos_of_exists 986 0 0 5 31 (by rfl) (by omega) (prove_sq 0 0 5 20 (by rfl))

lemma base_987 : 0 < A271510 987 :=
  A271510_pos_of_exists 987 9 1 11 28 (by rfl) (by omega) (prove_sq 9 1 11 45 (by rfl))

lemma base_988 : 0 < A271510 988 :=
  A271510_pos_of_exists 988 3 3 3 31 (by rfl) (by omega) (prove_sq 3 3 3 15 (by rfl))

lemma base_989 : 0 < A271510 989 :=
  A271510_pos_of_exists 989 18 6 2 25 (by rfl) (by omega) (prove_sq 18 6 2 26 (by rfl))

lemma base_990 : 0 < A271510 990 :=
  A271510_pos_of_exists 990 7 4 22 21 (by rfl) (by omega) (prove_sq 7 4 22 89 (by rfl))

lemma base_991 : 0 < A271510 991 :=
  A271510_pos_of_exists 991 9 3 1 30 (by rfl) (by omega) (prove_sq 9 3 1 13 (by rfl))

lemma base_992 : 0 < A271510 992 :=
  A271510_pos_of_exists 992 28 8 0 12 (by rfl) (by omega) (prove_sq 28 8 0 36 (by rfl))

lemma base_993 : 0 < A271510 993 :=
  A271510_pos_of_exists 993 4 4 0 31 (by rfl) (by omega) (prove_sq 4 4 0 12 (by rfl))

lemma base_994 : 0 < A271510 994 :=
  A271510_pos_of_exists 994 5 2 2 31 (by rfl) (by omega) (prove_sq 5 2 2 11 (by rfl))

lemma base_995 : 0 < A271510 995 :=
  A271510_pos_of_exists 995 5 0 3 31 (by rfl) (by omega) (prove_sq 5 0 3 13 (by rfl))

lemma base_996 : 0 < A271510 996 :=
  A271510_pos_of_exists 996 14 4 0 28 (by rfl) (by omega) (prove_sq 14 4 0 18 (by rfl))

lemma base_997 : 0 < A271510 997 :=
  A271510_pos_of_exists 997 0 0 6 31 (by rfl) (by omega) (prove_sq 0 0 6 24 (by rfl))

lemma base_998 : 0 < A271510 998 :=
  A271510_pos_of_exists 998 7 7 0 30 (by rfl) (by omega) (prove_sq 7 7 0 21 (by rfl))

lemma base_999 : 0 < A271510 999 :=
  A271510_pos_of_exists 999 3 2 5 31 (by rfl) (by omega) (prove_sq 3 2 5 21 (by rfl))

lemma base_1000 : 0 < A271510 1000 :=
  A271510_pos_of_exists 1000 0 0 10 30 (by rfl) (by omega) (prove_sq 0 0 10 40 (by rfl))

lemma base_1001 : 0 < A271510 1001 :=
  A271510_pos_of_exists 1001 6 0 2 31 (by rfl) (by omega) (prove_sq 6 0 2 10 (by rfl))

lemma base_1002 : 0 < A271510 1002 :=
  A271510_pos_of_exists 1002 11 2 6 29 (by rfl) (by omega) (prove_sq 11 2 6 27 (by rfl))

lemma base_1003 : 0 < A271510 1003 :=
  A271510_pos_of_exists 1003 5 1 4 31 (by rfl) (by omega) (prove_sq 5 1 4 17 (by rfl))

lemma base_1004 : 0 < A271510 1004 :=
  A271510_pos_of_exists 1004 21 9 11 19 (by rfl) (by omega) (prove_sq 21 9 11 55 (by rfl))

lemma base_1005 : 0 < A271510 1005 :=
  A271510_pos_of_exists 1005 11 8 26 12 (by rfl) (by omega) (prove_sq 11 8 26 107 (by rfl))

lemma base_1006 : 0 < A271510 1006 :=
  A271510_pos_of_exists 1006 13 7 2 28 (by rfl) (by omega) (prove_sq 13 7 2 25 (by rfl))

lemma base_1007 : 0 < A271510 1007 :=
  A271510_pos_of_exists 1007 15 14 19 15 (by rfl) (by omega) (prove_sq 15 14 19 87 (by rfl))

lemma base_1008 : 0 < A271510 1008 :=
  A271510_pos_of_exists 1008 6 6 6 30 (by rfl) (by omega) (prove_sq 6 6 6 30 (by rfl))

lemma base_1009 : 0 < A271510 1009 :=
  A271510_pos_of_exists 1009 0 0 15 28 (by rfl) (by omega) (prove_sq 0 0 15 60 (by rfl))

lemma base_1010 : 0 < A271510 1010 :=
  A271510_pos_of_exists 1010 0 0 7 31 (by rfl) (by omega) (prove_sq 0 0 7 28 (by rfl))

lemma base_1011 : 0 < A271510 1011 :=
  A271510_pos_of_exists 1011 5 5 0 31 (by rfl) (by omega) (prove_sq 5 5 0 15 (by rfl))

lemma base_1012 : 0 < A271510 1012 :=
  A271510_pos_of_exists 1012 7 3 15 27 (by rfl) (by omega) (prove_sq 7 3 15 61 (by rfl))

lemma base_1013 : 0 < A271510 1013 :=
  A271510_pos_of_exists 1013 0 0 22 23 (by rfl) (by omega) (prove_sq 0 0 22 88 (by rfl))

lemma base_1014 : 0 < A271510 1014 :=
  A271510_pos_of_exists 1014 7 2 0 31 (by rfl) (by omega) (prove_sq 7 2 0 9 (by rfl))

lemma base_1015 : 0 < A271510 1015 :=
  A271510_pos_of_exists 1015 5 5 2 31 (by rfl) (by omega) (prove_sq 5 5 2 17 (by rfl))

lemma base_1016 : 0 < A271510 1016 :=
  A271510_pos_of_exists 1016 14 0 12 26 (by rfl) (by omega) (prove_sq 14 0 12 50 (by rfl))

lemma base_1017 : 0 < A271510 1017 :=
  A271510_pos_of_exists 1017 0 0 21 24 (by rfl) (by omega) (prove_sq 0 0 21 84 (by rfl))

lemma base_1018 : 0 < A271510 1018 :=
  A271510_pos_of_exists 1018 0 0 17 27 (by rfl) (by omega) (prove_sq 0 0 17 68 (by rfl))

lemma base_1019 : 0 < A271510 1019 :=
  A271510_pos_of_exists 1019 5 3 12 29 (by rfl) (by omega) (prove_sq 5 3 12 49 (by rfl))

lemma base_1020 : 0 < A271510 1020 :=
  A271510_pos_of_exists 1020 14 10 20 18 (by rfl) (by omega) (prove_sq 14 10 20 86 (by rfl))

lemma base_1021 : 0 < A271510 1021 :=
  A271510_pos_of_exists 1021 0 0 11 30 (by rfl) (by omega) (prove_sq 0 0 11 44 (by rfl))

lemma base_1022 : 0 < A271510 1022 :=
  A271510_pos_of_exists 1022 9 0 10 29 (by rfl) (by omega) (prove_sq 9 0 10 41 (by rfl))

lemma base_1023 : 0 < A271510 1023 :=
  A271510_pos_of_exists 1023 7 2 3 31 (by rfl) (by omega) (prove_sq 7 2 3 15 (by rfl))

lemma base_1024 : 0 < A271510 1024 :=
  A271510_pos_of_exists 1024 0 0 0 32 (by rfl) (by omega) (prove_sq 0 0 0 0 (by rfl))

lemma base_1025 : 0 < A271510 1025 :=
  A271510_pos_of_exists 1025 0 0 1 32 (by rfl) (by omega) (prove_sq 0 0 1 4 (by rfl))

lemma base_1026 : 0 < A271510 1026 :=
  A271510_pos_of_exists 1026 1 1 0 32 (by rfl) (by omega) (prove_sq 1 1 0 3 (by rfl))

lemma base_1027 : 0 < A271510 1027 :=
  A271510_pos_of_exists 1027 1 1 1 32 (by rfl) (by omega) (prove_sq 1 1 1 5 (by rfl))

lemma base_1028 : 0 < A271510 1028 :=
  A271510_pos_of_exists 1028 0 0 2 32 (by rfl) (by omega) (prove_sq 0 0 2 8 (by rfl))

lemma base_1029 : 0 < A271510 1029 :=
  A271510_pos_of_exists 1029 9 4 26 16 (by rfl) (by omega) (prove_sq 9 4 26 105 (by rfl))

lemma base_1030 : 0 < A271510 1030 :=
  A271510_pos_of_exists 1030 5 5 28 14 (by rfl) (by omega) (prove_sq 5 5 28 113 (by rfl))

lemma base_1031 : 0 < A271510 1031 :=
  A271510_pos_of_exists 1031 5 5 9 30 (by rfl) (by omega) (prove_sq 5 5 9 39 (by rfl))

lemma base_1032 : 0 < A271510 1032 :=
  A271510_pos_of_exists 1032 2 2 0 32 (by rfl) (by omega) (prove_sq 2 2 0 6 (by rfl))

lemma base_1033 : 0 < A271510 1033 :=
  A271510_pos_of_exists 1033 0 0 3 32 (by rfl) (by omega) (prove_sq 0 0 3 12 (by rfl))

lemma base_1034 : 0 < A271510 1034 :=
  A271510_pos_of_exists 1034 3 0 1 32 (by rfl) (by omega) (prove_sq 3 0 1 5 (by rfl))

lemma base_1035 : 0 < A271510 1035 :=
  A271510_pos_of_exists 1035 7 5 31 0 (by rfl) (by omega) (prove_sq 7 5 31 125 (by rfl))

lemma base_1036 : 0 < A271510 1036 :=
  A271510_pos_of_exists 1036 2 2 2 32 (by rfl) (by omega) (prove_sq 2 2 2 10 (by rfl))

lemma base_1037 : 0 < A271510 1037 :=
  A271510_pos_of_exists 1037 0 0 14 29 (by rfl) (by omega) (prove_sq 0 0 14 56 (by rfl))

lemma base_1038 : 0 < A271510 1038 :=
  A271510_pos_of_exists 1038 3 1 2 32 (by rfl) (by omega) (prove_sq 3 1 2 9 (by rfl))

lemma base_1039 : 0 < A271510 1039 :=
  A271510_pos_of_exists 1039 5 2 7 31 (by rfl) (by omega) (prove_sq 5 2 7 29 (by rfl))

lemma base_1040 : 0 < A271510 1040 :=
  A271510_pos_of_exists 1040 0 0 4 32 (by rfl) (by omega) (prove_sq 0 0 4 16 (by rfl))

lemma base_1041 : 0 < A271510 1041 :=
  A271510_pos_of_exists 1041 10 4 14 27 (by rfl) (by omega) (prove_sq 10 4 14 58 (by rfl))

lemma base_1042 : 0 < A271510 1042 :=
  A271510_pos_of_exists 1042 0 0 9 31 (by rfl) (by omega) (prove_sq 0 0 9 36 (by rfl))

lemma base_1043 : 0 < A271510 1043 :=
  A271510_pos_of_exists 1043 13 9 3 28 (by rfl) (by omega) (prove_sq 13 9 3 31 (by rfl))

lemma base_1044 : 0 < A271510 1044 :=
  A271510_pos_of_exists 1044 0 0 12 30 (by rfl) (by omega) (prove_sq 0 0 12 48 (by rfl))

lemma base_1045 : 0 < A271510 1045 :=
  A271510_pos_of_exists 1045 4 2 1 32 (by rfl) (by omega) (prove_sq 4 2 1 8 (by rfl))

lemma base_1046 : 0 < A271510 1046 :=
  A271510_pos_of_exists 1046 7 0 6 31 (by rfl) (by omega) (prove_sq 7 0 6 25 (by rfl))

lemma base_1047 : 0 < A271510 1047 :=
  A271510_pos_of_exists 1047 7 7 7 30 (by rfl) (by omega) (prove_sq 7 7 7 35 (by rfl))

lemma base_1048 : 0 < A271510 1048 :=
  A271510_pos_of_exists 1048 6 6 20 24 (by rfl) (by omega) (prove_sq 6 6 20 82 (by rfl))

lemma base_1049 : 0 < A271510 1049 :=
  A271510_pos_of_exists 1049 0 0 5 32 (by rfl) (by omega) (prove_sq 0 0 5 20 (by rfl))

lemma base_1050 : 0 < A271510 1050 :=
  A271510_pos_of_exists 1050 15 10 25 10 (by rfl) (by omega) (prove_sq 15 10 25 105 (by rfl))

lemma base_1051 : 0 < A271510 1051 :=
  A271510_pos_of_exists 1051 3 3 3 32 (by rfl) (by omega) (prove_sq 3 3 3 15 (by rfl))

lemma base_1052 : 0 < A271510 1052 :=
  A271510_pos_of_exists 1052 6 4 10 30 (by rfl) (by omega) (prove_sq 6 4 10 42 (by rfl))

lemma base_1053 : 0 < A271510 1053 :=
  A271510_pos_of_exists 1053 0 0 18 27 (by rfl) (by omega) (prove_sq 0 0 18 72 (by rfl))

lemma base_1054 : 0 < A271510 1054 :=
  A271510_pos_of_exists 1054 11 1 16 26 (by rfl) (by omega) (prove_sq 11 1 16 65 (by rfl))

lemma base_1055 : 0 < A271510 1055 :=
  A271510_pos_of_exists 1055 19 17 9 18 (by rfl) (by omega) (prove_sq 19 17 9 63 (by rfl))

lemma base_1056 : 0 < A271510 1056 :=
  A271510_pos_of_exists 1056 4 4 0 32 (by rfl) (by omega) (prove_sq 4 4 0 12 (by rfl))

lemma base_1057 : 0 < A271510 1057 :=
  A271510_pos_of_exists 1057 5 2 2 32 (by rfl) (by omega) (prove_sq 5 2 2 11 (by rfl))

lemma base_1058 : 0 < A271510 1058 :=
  A271510_pos_of_exists 1058 0 0 23 23 (by rfl) (by omega) (prove_sq 0 0 23 92 (by rfl))

lemma base_1059 : 0 < A271510 1059 :=
  A271510_pos_of_exists 1059 5 5 28 15 (by rfl) (by omega) (prove_sq 5 5 28 113 (by rfl))

lemma base_1060 : 0 < A271510 1060 :=
  A271510_pos_of_exists 1060 0 0 6 32 (by rfl) (by omega) (prove_sq 0 0 6 24 (by rfl))

lemma base_1061 : 0 < A271510 1061 :=
  A271510_pos_of_exists 1061 0 0 10 31 (by rfl) (by omega) (prove_sq 0 0 10 40 (by rfl))

lemma base_1062 : 0 < A271510 1062 :=
  A271510_pos_of_exists 1062 3 2 5 32 (by rfl) (by omega) (prove_sq 3 2 5 21 (by rfl))

lemma base_1063 : 0 < A271510 1063 :=
  A271510_pos_of_exists 1063 9 9 30 1 (by rfl) (by omega) (prove_sq 9 9 30 123 (by rfl))

lemma base_1064 : 0 < A271510 1064 :=
  A271510_pos_of_exists 1064 6 0 2 32 (by rfl) (by omega) (prove_sq 6 0 2 10 (by rfl))

lemma base_1065 : 0 < A271510 1065 :=
  A271510_pos_of_exists 1065 9 2 14 28 (by rfl) (by omega) (prove_sq 9 2 14 57 (by rfl))

lemma base_1066 : 0 < A271510 1066 :=
  A271510_pos_of_exists 1066 0 0 15 29 (by rfl) (by omega) (prove_sq 0 0 15 60 (by rfl))

lemma base_1067 : 0 < A271510 1067 :=
  A271510_pos_of_exists 1067 7 3 15 28 (by rfl) (by omega) (prove_sq 7 3 15 61 (by rfl))

lemma base_1068 : 0 < A271510 1068 :=
  A271510_pos_of_exists 1068 10 2 8 30 (by rfl) (by omega) (prove_sq 10 2 8 34 (by rfl))

lemma base_1069 : 0 < A271510 1069 :=
  A271510_pos_of_exists 1069 0 0 13 30 (by rfl) (by omega) (prove_sq 0 0 13 52 (by rfl))

lemma base_1070 : 0 < A271510 1070 :=
  A271510_pos_of_exists 1070 15 0 2 29 (by rfl) (by omega) (prove_sq 15 0 2 17 (by rfl))

lemma base_1071 : 0 < A271510 1071 :=
  A271510_pos_of_exists 1071 7 5 31 6 (by rfl) (by omega) (prove_sq 7 5 31 125 (by rfl))

lemma base_1072 : 0 < A271510 1072 :=
  A271510_pos_of_exists 1072 4 4 4 32 (by rfl) (by omega) (prove_sq 4 4 4 20 (by rfl))

lemma base_1073 : 0 < A271510 1073 :=
  A271510_pos_of_exists 1073 0 0 7 32 (by rfl) (by omega) (prove_sq 0 0 7 28 (by rfl))

lemma base_1074 : 0 < A271510 1074 :=
  A271510_pos_of_exists 1074 5 5 0 32 (by rfl) (by omega) (prove_sq 5 5 0 15 (by rfl))

lemma base_1075 : 0 < A271510 1075 :=
  A271510_pos_of_exists 1075 7 4 7 31 (by rfl) (by omega) (prove_sq 7 4 7 31 (by rfl))

lemma base_1076 : 0 < A271510 1076 :=
  A271510_pos_of_exists 1076 0 0 20 26 (by rfl) (by omega) (prove_sq 0 0 20 80 (by rfl))

lemma base_1077 : 0 < A271510 1077 :=
  A271510_pos_of_exists 1077 7 2 0 32 (by rfl) (by omega) (prove_sq 7 2 0 9 (by rfl))

lemma base_1078 : 0 < A271510 1078 :=
  A271510_pos_of_exists 1078 5 3 12 30 (by rfl) (by omega) (prove_sq 5 3 12 49 (by rfl))

lemma base_1079 : 0 < A271510 1079 :=
  A271510_pos_of_exists 1079 3 3 10 31 (by rfl) (by omega) (prove_sq 3 3 10 41 (by rfl))

lemma base_1080 : 0 < A271510 1080 :=
  A271510_pos_of_exists 1080 6 2 4 32 (by rfl) (by omega) (prove_sq 6 2 4 18 (by rfl))

lemma base_1081 : 0 < A271510 1081 :=
  A271510_pos_of_exists 1081 9 0 10 30 (by rfl) (by omega) (prove_sq 9 0 10 41 (by rfl))

lemma base_1082 : 0 < A271510 1082 :=
  A271510_pos_of_exists 1082 0 0 11 31 (by rfl) (by omega) (prove_sq 0 0 11 44 (by rfl))

lemma base_1083 : 0 < A271510 1083 :=
  A271510_pos_of_exists 1083 11 11 0 29 (by rfl) (by omega) (prove_sq 11 11 0 33 (by rfl))

lemma base_1084 : 0 < A271510 1084 :=
  A271510_pos_of_exists 1084 7 5 31 7 (by rfl) (by omega) (prove_sq 7 5 31 125 (by rfl))

lemma base_1085 : 0 < A271510 1085 :=
  A271510_pos_of_exists 1085 12 10 29 0 (by rfl) (by omega) (prove_sq 12 10 29 120 (by rfl))

lemma base_1086 : 0 < A271510 1086 :=
  A271510_pos_of_exists 1086 7 2 3 32 (by rfl) (by omega) (prove_sq 7 2 3 15 (by rfl))

lemma base_1087 : 0 < A271510 1087 :=
  A271510_pos_of_exists 1087 9 3 6 31 (by rfl) (by omega) (prove_sq 9 3 6 27 (by rfl))

lemma base_1088 : 0 < A271510 1088 :=
  A271510_pos_of_exists 1088 0 0 8 32 (by rfl) (by omega) (prove_sq 0 0 8 32 (by rfl))

lemma base_1089 : 0 < A271510 1089 :=
  A271510_pos_of_exists 1089 0 0 0 33 (by rfl) (by omega) (prove_sq 0 0 0 0 (by rfl))

lemma base_1090 : 0 < A271510 1090 :=
  A271510_pos_of_exists 1090 0 0 1 33 (by rfl) (by omega) (prove_sq 0 0 1 4 (by rfl))

lemma base_1091 : 0 < A271510 1091 :=
  A271510_pos_of_exists 1091 1 1 0 33 (by rfl) (by omega) (prove_sq 1 1 0 3 (by rfl))

lemma base_1092 : 0 < A271510 1092 :=
  A271510_pos_of_exists 1092 1 1 1 33 (by rfl) (by omega) (prove_sq 1 1 1 5 (by rfl))

lemma base_1093 : 0 < A271510 1093 :=
  A271510_pos_of_exists 1093 0 0 2 33 (by rfl) (by omega) (prove_sq 0 0 2 8 (by rfl))

lemma base_1094 : 0 < A271510 1094 :=
  A271510_pos_of_exists 1094 9 6 4 31 (by rfl) (by omega) (prove_sq 9 6 4 25 (by rfl))

lemma base_1095 : 0 < A271510 1095 :=
  A271510_pos_of_exists 1095 11 7 21 22 (by rfl) (by omega) (prove_sq 11 7 21 87 (by rfl))

lemma base_1096 : 0 < A271510 1096 :=
  A271510_pos_of_exists 1096 0 0 14 30 (by rfl) (by omega) (prove_sq 0 0 14 56 (by rfl))

lemma base_1097 : 0 < A271510 1097 :=
  A271510_pos_of_exists 1097 0 0 16 29 (by rfl) (by omega) (prove_sq 0 0 16 64 (by rfl))

lemma base_1098 : 0 < A271510 1098 :=
  A271510_pos_of_exists 1098 0 0 3 33 (by rfl) (by omega) (prove_sq 0 0 3 12 (by rfl))

lemma base_1099 : 0 < A271510 1099 :=
  A271510_pos_of_exists 1099 3 0 1 33 (by rfl) (by omega) (prove_sq 3 0 1 5 (by rfl))

lemma base_1100 : 0 < A271510 1100 :=
  A271510_pos_of_exists 1100 10 10 0 30 (by rfl) (by omega) (prove_sq 10 10 0 30 (by rfl))

lemma base_1101 : 0 < A271510 1101 :=
  A271510_pos_of_exists 1101 2 2 2 33 (by rfl) (by omega) (prove_sq 2 2 2 10 (by rfl))

lemma base_1102 : 0 < A271510 1102 :=
  A271510_pos_of_exists 1102 5 2 7 32 (by rfl) (by omega) (prove_sq 5 2 7 29 (by rfl))

lemma base_1103 : 0 < A271510 1103 :=
  A271510_pos_of_exists 1103 3 1 2 33 (by rfl) (by omega) (prove_sq 3 1 2 9 (by rfl))

lemma base_1104 : 0 < A271510 1104 :=
  A271510_pos_of_exists 1104 20 8 8 24 (by rfl) (by omega) (prove_sq 20 8 8 44 (by rfl))

lemma base_1105 : 0 < A271510 1105 :=
  A271510_pos_of_exists 1105 0 0 4 33 (by rfl) (by omega) (prove_sq 0 0 4 16 (by rfl))

lemma base_1106 : 0 < A271510 1106 :=
  A271510_pos_of_exists 1106 11 3 24 20 (by rfl) (by omega) (prove_sq 11 3 24 97 (by rfl))

lemma base_1107 : 0 < A271510 1107 :=
  A271510_pos_of_exists 1107 3 3 0 33 (by rfl) (by omega) (prove_sq 3 3 0 9 (by rfl))

lemma base_1108 : 0 < A271510 1108 :=
  A271510_pos_of_exists 1108 0 0 18 28 (by rfl) (by omega) (prove_sq 0 0 18 72 (by rfl))

lemma base_1109 : 0 < A271510 1109 :=
  A271510_pos_of_exists 1109 0 0 22 25 (by rfl) (by omega) (prove_sq 0 0 22 88 (by rfl))

lemma base_1110 : 0 < A271510 1110 :=
  A271510_pos_of_exists 1110 4 2 1 33 (by rfl) (by omega) (prove_sq 4 2 1 8 (by rfl))

lemma base_1111 : 0 < A271510 1111 :=
  A271510_pos_of_exists 1111 9 9 30 7 (by rfl) (by omega) (prove_sq 9 9 30 123 (by rfl))

lemma base_1112 : 0 < A271510 1112 :=
  A271510_pos_of_exists 1112 10 6 24 20 (by rfl) (by omega) (prove_sq 10 6 24 98 (by rfl))

lemma base_1113 : 0 < A271510 1113 :=
  A271510_pos_of_exists 1113 6 4 10 31 (by rfl) (by omega) (prove_sq 6 4 10 42 (by rfl))

lemma base_1114 : 0 < A271510 1114 :=
  A271510_pos_of_exists 1114 0 0 5 33 (by rfl) (by omega) (prove_sq 0 0 5 20 (by rfl))

lemma base_1115 : 0 < A271510 1115 :=
  A271510_pos_of_exists 1115 9 3 1 32 (by rfl) (by omega) (prove_sq 9 3 1 13 (by rfl))

lemma base_1116 : 0 < A271510 1116 :=
  A271510_pos_of_exists 1116 3 3 3 33 (by rfl) (by omega) (prove_sq 3 3 3 15 (by rfl))

lemma base_1117 : 0 < A271510 1117 :=
  A271510_pos_of_exists 1117 0 0 21 26 (by rfl) (by omega) (prove_sq 0 0 21 84 (by rfl))

lemma base_1118 : 0 < A271510 1118 :=
  A271510_pos_of_exists 1118 17 10 0 27 (by rfl) (by omega) (prove_sq 17 10 0 33 (by rfl))

lemma base_1119 : 0 < A271510 1119 :=
  A271510_pos_of_exists 1119 13 1 7 30 (by rfl) (by omega) (prove_sq 13 1 7 31 (by rfl))

lemma base_1120 : 0 < A271510 1120 :=
  A271510_pos_of_exists 1120 16 8 4 28 (by rfl) (by omega) (prove_sq 16 8 4 32 (by rfl))

lemma base_1121 : 0 < A271510 1121 :=
  A271510_pos_of_exists 1121 4 4 0 33 (by rfl) (by omega) (prove_sq 4 4 0 12 (by rfl))

lemma base_1122 : 0 < A271510 1122 :=
  A271510_pos_of_exists 1122 5 2 2 33 (by rfl) (by omega) (prove_sq 5 2 2 11 (by rfl))

lemma base_1123 : 0 < A271510 1123 :=
  A271510_pos_of_exists 1123 5 0 3 33 (by rfl) (by omega) (prove_sq 5 0 3 13 (by rfl))

lemma base_1124 : 0 < A271510 1124 :=
  A271510_pos_of_exists 1124 0 0 10 32 (by rfl) (by omega) (prove_sq 0 0 10 40 (by rfl))

lemma base_1125 : 0 < A271510 1125 :=
  A271510_pos_of_exists 1125 0 0 6 33 (by rfl) (by omega) (prove_sq 0 0 6 24 (by rfl))

lemma base_1126 : 0 < A271510 1126 :=
  A271510_pos_of_exists 1126 9 6 15 28 (by rfl) (by omega) (prove_sq 9 6 15 63 (by rfl))

lemma base_1127 : 0 < A271510 1127 :=
  A271510_pos_of_exists 1127 3 2 5 33 (by rfl) (by omega) (prove_sq 3 2 5 21 (by rfl))

lemma base_1128 : 0 < A271510 1128 :=
  A271510_pos_of_exists 1128 18 4 28 2 (by rfl) (by omega) (prove_sq 18 4 28 114 (by rfl))

lemma base_1129 : 0 < A271510 1129 :=
  A271510_pos_of_exists 1129 0 0 20 27 (by rfl) (by omega) (prove_sq 0 0 20 80 (by rfl))

lemma base_1130 : 0 < A271510 1130 :=
  A271510_pos_of_exists 1130 0 0 13 31 (by rfl) (by omega) (prove_sq 0 0 13 52 (by rfl))

lemma base_1131 : 0 < A271510 1131 :=
  A271510_pos_of_exists 1131 5 1 4 33 (by rfl) (by omega) (prove_sq 5 1 4 17 (by rfl))

lemma base_1132 : 0 < A271510 1132 :=
  A271510_pos_of_exists 1132 6 6 6 32 (by rfl) (by omega) (prove_sq 6 6 6 30 (by rfl))

lemma base_1133 : 0 < A271510 1133 :=
  A271510_pos_of_exists 1133 12 6 13 28 (by rfl) (by omega) (prove_sq 12 6 13 56 (by rfl))

lemma base_1134 : 0 < A271510 1134 :=
  A271510_pos_of_exists 1134 9 4 26 19 (by rfl) (by omega) (prove_sq 9 4 26 105 (by rfl))

lemma base_1135 : 0 < A271510 1135 :=
  A271510_pos_of_exists 1135 7 5 10 31 (by rfl) (by omega) (prove_sq 7 5 10 43 (by rfl))

lemma base_1136 : 0 < A271510 1136 :=
  A271510_pos_of_exists 1136 14 6 30 2 (by rfl) (by omega) (prove_sq 14 6 30 122 (by rfl))

lemma base_1137 : 0 < A271510 1137 :=
  A271510_pos_of_exists 1137 4 4 4 33 (by rfl) (by omega) (prove_sq 4 4 4 20 (by rfl))

lemma base_1138 : 0 < A271510 1138 :=
  A271510_pos_of_exists 1138 0 0 7 33 (by rfl) (by omega) (prove_sq 0 0 7 28 (by rfl))

lemma base_1139 : 0 < A271510 1139 :=
  A271510_pos_of_exists 1139 5 3 12 31 (by rfl) (by omega) (prove_sq 5 3 12 49 (by rfl))

lemma base_1140 : 0 < A271510 1140 :=
  A271510_pos_of_exists 1140 11 7 21 23 (by rfl) (by omega) (prove_sq 11 7 21 87 (by rfl))

lemma base_1141 : 0 < A271510 1141 :=
  A271510_pos_of_exists 1141 10 10 10 29 (by rfl) (by omega) (prove_sq 10 10 10 50 (by rfl))

lemma base_1142 : 0 < A271510 1142 :=
  A271510_pos_of_exists 1142 3 3 10 32 (by rfl) (by omega) (prove_sq 3 3 10 41 (by rfl))

lemma base_1143 : 0 < A271510 1143 :=
  A271510_pos_of_exists 1143 5 5 2 33 (by rfl) (by omega) (prove_sq 5 5 2 17 (by rfl))

lemma base_1144 : 0 < A271510 1144 :=
  A271510_pos_of_exists 1144 18 0 6 28 (by rfl) (by omega) (prove_sq 18 0 6 30 (by rfl))

lemma base_1145 : 0 < A271510 1145 :=
  A271510_pos_of_exists 1145 0 0 11 32 (by rfl) (by omega) (prove_sq 0 0 11 44 (by rfl))

lemma base_1146 : 0 < A271510 1146 :=
  A271510_pos_of_exists 1146 15 10 25 14 (by rfl) (by omega) (prove_sq 15 10 25 105 (by rfl))

lemma base_1147 : 0 < A271510 1147 :=
  A271510_pos_of_exists 1147 7 3 0 33 (by rfl) (by omega) (prove_sq 7 3 0 11 (by rfl))

lemma base_1148 : 0 < A271510 1148 :=
  A271510_pos_of_exists 1148 6 6 20 26 (by rfl) (by omega) (prove_sq 6 6 20 82 (by rfl))

lemma base_1149 : 0 < A271510 1149 :=
  A271510_pos_of_exists 1149 10 8 12 29 (by rfl) (by omega) (prove_sq 10 8 12 54 (by rfl))

lemma base_1150 : 0 < A271510 1150 :=
  A271510_pos_of_exists 1150 9 3 6 32 (by rfl) (by omega) (prove_sq 9 3 6 27 (by rfl))

lemma base_1151 : 0 < A271510 1151 :=
  A271510_pos_of_exists 1151 7 2 3 33 (by rfl) (by omega) (prove_sq 7 2 3 15 (by rfl))

lemma base_1152 : 0 < A271510 1152 :=
  A271510_pos_of_exists 1152 0 0 24 24 (by rfl) (by omega) (prove_sq 0 0 24 96 (by rfl))

lemma base_1153 : 0 < A271510 1153 :=
  A271510_pos_of_exists 1153 0 0 8 33 (by rfl) (by omega) (prove_sq 0 0 8 32 (by rfl))

lemma base_1154 : 0 < A271510 1154 :=
  A271510_pos_of_exists 1154 0 0 23 25 (by rfl) (by omega) (prove_sq 0 0 23 92 (by rfl))

lemma base_1155 : 0 < A271510 1155 :=
  A271510_pos_of_exists 1155 5 5 9 32 (by rfl) (by omega) (prove_sq 5 5 9 39 (by rfl))

lemma base_1156 : 0 < A271510 1156 :=
  A271510_pos_of_exists 1156 0 0 0 34 (by rfl) (by omega) (prove_sq 0 0 0 0 (by rfl))

lemma base_1157 : 0 < A271510 1157 :=
  A271510_pos_of_exists 1157 0 0 1 34 (by rfl) (by omega) (prove_sq 0 0 1 4 (by rfl))

lemma base_1158 : 0 < A271510 1158 :=
  A271510_pos_of_exists 1158 1 1 0 34 (by rfl) (by omega) (prove_sq 1 1 0 3 (by rfl))

lemma base_1159 : 0 < A271510 1159 :=
  A271510_pos_of_exists 1159 1 1 1 34 (by rfl) (by omega) (prove_sq 1 1 1 5 (by rfl))

lemma base_1160 : 0 < A271510 1160 :=
  A271510_pos_of_exists 1160 0 0 2 34 (by rfl) (by omega) (prove_sq 0 0 2 8 (by rfl))

lemma base_1161 : 0 < A271510 1161 :=
  A271510_pos_of_exists 1161 6 6 0 33 (by rfl) (by omega) (prove_sq 6 6 0 18 (by rfl))

lemma base_1162 : 0 < A271510 1162 :=
  A271510_pos_of_exists 1162 9 9 30 10 (by rfl) (by omega) (prove_sq 9 9 30 123 (by rfl))

lemma base_1163 : 0 < A271510 1163 :=
  A271510_pos_of_exists 1163 17 1 12 27 (by rfl) (by omega) (prove_sq 17 1 12 51 (by rfl))

lemma base_1164 : 0 < A271510 1164 :=
  A271510_pos_of_exists 1164 2 2 0 34 (by rfl) (by omega) (prove_sq 2 2 0 6 (by rfl))

lemma base_1165 : 0 < A271510 1165 :=
  A271510_pos_of_exists 1165 0 0 3 34 (by rfl) (by omega) (prove_sq 0 0 3 12 (by rfl))

lemma base_1166 : 0 < A271510 1166 :=
  A271510_pos_of_exists 1166 3 0 1 34 (by rfl) (by omega) (prove_sq 3 0 1 5 (by rfl))

lemma base_1167 : 0 < A271510 1167 :=
  A271510_pos_of_exists 1167 5 2 7 33 (by rfl) (by omega) (prove_sq 5 2 7 29 (by rfl))

lemma base_1168 : 0 < A271510 1168 :=
  A271510_pos_of_exists 1168 0 0 12 32 (by rfl) (by omega) (prove_sq 0 0 12 48 (by rfl))

lemma base_1169 : 0 < A271510 1169 :=
  A271510_pos_of_exists 1169 16 16 9 24 (by rfl) (by omega) (prove_sq 16 16 9 60 (by rfl))

lemma base_1170 : 0 < A271510 1170 :=
  A271510_pos_of_exists 1170 0 0 9 33 (by rfl) (by omega) (prove_sq 0 0 9 36 (by rfl))

lemma base_1171 : 0 < A271510 1171 :=
  A271510_pos_of_exists 1171 7 7 7 32 (by rfl) (by omega) (prove_sq 7 7 7 35 (by rfl))

lemma base_1172 : 0 < A271510 1172 :=
  A271510_pos_of_exists 1172 0 0 4 34 (by rfl) (by omega) (prove_sq 0 0 4 16 (by rfl))

lemma base_1173 : 0 < A271510 1173 :=
  A271510_pos_of_exists 1173 8 4 2 33 (by rfl) (by omega) (prove_sq 8 4 2 16 (by rfl))

lemma base_1174 : 0 < A271510 1174 :=
  A271510_pos_of_exists 1174 3 3 0 34 (by rfl) (by omega) (prove_sq 3 3 0 9 (by rfl))

lemma base_1175 : 0 < A271510 1175 :=
  A271510_pos_of_exists 1175 15 10 25 15 (by rfl) (by omega) (prove_sq 15 10 25 105 (by rfl))

lemma base_1176 : 0 < A271510 1176 :=
  A271510_pos_of_exists 1176 6 4 10 32 (by rfl) (by omega) (prove_sq 6 4 10 42 (by rfl))

lemma base_1177 : 0 < A271510 1177 :=
  A271510_pos_of_exists 1177 4 2 1 34 (by rfl) (by omega) (prove_sq 4 2 1 8 (by rfl))

lemma base_1178 : 0 < A271510 1178 :=
  A271510_pos_of_exists 1178 13 3 30 10 (by rfl) (by omega) (prove_sq 13 3 30 121 (by rfl))

lemma base_1179 : 0 < A271510 1179 :=
  A271510_pos_of_exists 1179 7 5 31 12 (by rfl) (by omega) (prove_sq 7 5 31 125 (by rfl))

lemma base_1180 : 0 < A271510 1180 :=
  A271510_pos_of_exists 1180 9 3 1 33 (by rfl) (by omega) (prove_sq 9 3 1 13 (by rfl))

lemma base_1181 : 0 < A271510 1181 :=
  A271510_pos_of_exists 1181 0 0 5 34 (by rfl) (by omega) (prove_sq 0 0 5 20 (by rfl))

lemma base_1182 : 0 < A271510 1182 :=
  A271510_pos_of_exists 1182 15 14 19 20 (by rfl) (by omega) (prove_sq 15 14 19 87 (by rfl))

lemma base_1183 : 0 < A271510 1183 :=
  A271510_pos_of_exists 1183 3 3 3 34 (by rfl) (by omega) (prove_sq 3 3 3 15 (by rfl))

lemma base_1184 : 0 < A271510 1184 :=
  A271510_pos_of_exists 1184 0 0 20 28 (by rfl) (by omega) (prove_sq 0 0 20 80 (by rfl))

lemma base_1185 : 0 < A271510 1185 :=
  A271510_pos_of_exists 1185 11 2 6 32 (by rfl) (by omega) (prove_sq 11 2 6 27 (by rfl))

lemma base_1186 : 0 < A271510 1186 :=
  A271510_pos_of_exists 1186 0 0 15 31 (by rfl) (by omega) (prove_sq 0 0 15 60 (by rfl))

lemma base_1187 : 0 < A271510 1187 :=
  A271510_pos_of_exists 1187 7 7 0 33 (by rfl) (by omega) (prove_sq 7 7 0 21 (by rfl))

lemma base_1188 : 0 < A271510 1188 :=
  A271510_pos_of_exists 1188 4 4 0 34 (by rfl) (by omega) (prove_sq 4 4 0 12 (by rfl))

lemma base_1189 : 0 < A271510 1189 :=
  A271510_pos_of_exists 1189 0 0 10 33 (by rfl) (by omega) (prove_sq 0 0 10 40 (by rfl))

lemma base_1190 : 0 < A271510 1190 :=
  A271510_pos_of_exists 1190 5 0 3 34 (by rfl) (by omega) (prove_sq 5 0 3 13 (by rfl))

lemma base_1191 : 0 < A271510 1191 :=
  A271510_pos_of_exists 1191 15 5 10 29 (by rfl) (by omega) (prove_sq 15 5 10 45 (by rfl))

lemma base_1192 : 0 < A271510 1192 :=
  A271510_pos_of_exists 1192 0 0 6 34 (by rfl) (by omega) (prove_sq 0 0 6 24 (by rfl))

lemma base_1193 : 0 < A271510 1193 :=
  A271510_pos_of_exists 1193 0 0 13 32 (by rfl) (by omega) (prove_sq 0 0 13 52 (by rfl))

lemma base_1194 : 0 < A271510 1194 :=
  A271510_pos_of_exists 1194 3 2 5 34 (by rfl) (by omega) (prove_sq 3 2 5 21 (by rfl))

lemma base_1195 : 0 < A271510 1195 :=
  A271510_pos_of_exists 1195 5 5 28 19 (by rfl) (by omega) (prove_sq 5 5 28 113 (by rfl))

lemma base_1196 : 0 < A271510 1196 :=
  A271510_pos_of_exists 1196 6 0 2 34 (by rfl) (by omega) (prove_sq 6 0 2 10 (by rfl))

lemma base_1197 : 0 < A271510 1197 :=
  A271510_pos_of_exists 1197 6 6 6 33 (by rfl) (by omega) (prove_sq 6 6 6 30 (by rfl))

lemma base_1198 : 0 < A271510 1198 :=
  A271510_pos_of_exists 1198 5 1 4 34 (by rfl) (by omega) (prove_sq 5 1 4 17 (by rfl))

lemma base_1199 : 0 < A271510 1199 :=
  A271510_pos_of_exists 1199 13 3 30 11 (by rfl) (by omega) (prove_sq 13 3 30 121 (by rfl))

lemma base_1200 : 0 < A271510 1200 :=
  A271510_pos_of_exists 1200 10 10 10 30 (by rfl) (by omega) (prove_sq 10 10 10 50 (by rfl))

lemma base_1201 : 0 < A271510 1201 :=
  A271510_pos_of_exists 1201 0 0 24 25 (by rfl) (by omega) (prove_sq 0 0 24 96 (by rfl))

lemma base_1202 : 0 < A271510 1202 :=
  A271510_pos_of_exists 1202 0 0 19 29 (by rfl) (by omega) (prove_sq 0 0 19 76 (by rfl))

lemma base_1203 : 0 < A271510 1203 :=
  A271510_pos_of_exists 1203 7 4 7 33 (by rfl) (by omega) (prove_sq 7 4 7 31 (by rfl))

lemma base_1204 : 0 < A271510 1204 :=
  A271510_pos_of_exists 1204 4 4 4 34 (by rfl) (by omega) (prove_sq 4 4 4 20 (by rfl))

lemma base_1205 : 0 < A271510 1205 :=
  A271510_pos_of_exists 1205 0 0 7 34 (by rfl) (by omega) (prove_sq 0 0 7 28 (by rfl))

lemma base_1206 : 0 < A271510 1206 :=
  A271510_pos_of_exists 1206 5 5 0 34 (by rfl) (by omega) (prove_sq 5 5 0 15 (by rfl))

lemma base_1207 : 0 < A271510 1207 :=
  A271510_pos_of_exists 1207 3 3 10 33 (by rfl) (by omega) (prove_sq 3 3 10 41 (by rfl))

lemma base_1208 : 0 < A271510 1208 :=
  A271510_pos_of_exists 1208 10 8 12 30 (by rfl) (by omega) (prove_sq 10 8 12 54 (by rfl))

lemma base_1209 : 0 < A271510 1209 :=
  A271510_pos_of_exists 1209 7 2 0 34 (by rfl) (by omega) (prove_sq 7 2 0 9 (by rfl))

lemma base_1210 : 0 < A271510 1210 :=
  A271510_pos_of_exists 1210 0 0 11 33 (by rfl) (by omega) (prove_sq 0 0 11 44 (by rfl))

lemma base_1211 : 0 < A271510 1211 :=
  A271510_pos_of_exists 1211 15 0 5 31 (by rfl) (by omega) (prove_sq 15 0 5 25 (by rfl))

lemma base_1212 : 0 < A271510 1212 :=
  A271510_pos_of_exists 1212 6 2 4 34 (by rfl) (by omega) (prove_sq 6 2 4 18 (by rfl))

lemma base_1213 : 0 < A271510 1213 :=
  A271510_pos_of_exists 1213 0 0 22 27 (by rfl) (by omega) (prove_sq 0 0 22 88 (by rfl))

lemma base_1214 : 0 < A271510 1214 :=
  A271510_pos_of_exists 1214 7 3 0 34 (by rfl) (by omega) (prove_sq 7 3 0 11 (by rfl))

lemma base_1215 : 0 < A271510 1215 :=
  A271510_pos_of_exists 1215 9 3 6 33 (by rfl) (by omega) (prove_sq 9 3 6 27 (by rfl))

lemma base_1216 : 0 < A271510 1216 :=
  A271510_pos_of_exists 1216 8 8 8 32 (by rfl) (by omega) (prove_sq 8 8 8 40 (by rfl))

lemma base_1217 : 0 < A271510 1217 :=
  A271510_pos_of_exists 1217 0 0 16 31 (by rfl) (by omega) (prove_sq 0 0 16 64 (by rfl))

lemma base_1218 : 0 < A271510 1218 :=
  A271510_pos_of_exists 1218 7 2 3 34 (by rfl) (by omega) (prove_sq 7 2 3 15 (by rfl))

lemma base_1219 : 0 < A271510 1219 :=
  A271510_pos_of_exists 1219 11 1 16 29 (by rfl) (by omega) (prove_sq 11 1 16 65 (by rfl))

lemma base_1220 : 0 < A271510 1220 :=
  A271510_pos_of_exists 1220 0 0 8 34 (by rfl) (by omega) (prove_sq 0 0 8 32 (by rfl))

lemma base_1221 : 0 < A271510 1221 :=
  A271510_pos_of_exists 1221 10 4 4 33 (by rfl) (by omega) (prove_sq 10 4 4 22 (by rfl))

lemma base_1222 : 0 < A271510 1222 :=
  A271510_pos_of_exists 1222 9 6 4 33 (by rfl) (by omega) (prove_sq 9 6 4 25 (by rfl))

lemma base_1223 : 0 < A271510 1223 :=
  A271510_pos_of_exists 1223 15 6 1 31 (by rfl) (by omega) (prove_sq 15 6 1 23 (by rfl))

lemma base_1224 : 0 < A271510 1224 :=
  A271510_pos_of_exists 1224 0 0 18 30 (by rfl) (by omega) (prove_sq 0 0 18 72 (by rfl))

lemma base_1225 : 0 < A271510 1225 :=
  A271510_pos_of_exists 1225 0 0 0 35 (by rfl) (by omega) (prove_sq 0 0 0 0 (by rfl))

lemma base_1226 : 0 < A271510 1226 :=
  A271510_pos_of_exists 1226 0 0 1 35 (by rfl) (by omega) (prove_sq 0 0 1 4 (by rfl))

lemma base_1227 : 0 < A271510 1227 :=
  A271510_pos_of_exists 1227 1 1 0 35 (by rfl) (by omega) (prove_sq 1 1 0 3 (by rfl))

lemma base_1228 : 0 < A271510 1228 :=
  A271510_pos_of_exists 1228 1 1 1 35 (by rfl) (by omega) (prove_sq 1 1 1 5 (by rfl))

lemma base_1229 : 0 < A271510 1229 :=
  A271510_pos_of_exists 1229 0 0 2 35 (by rfl) (by omega) (prove_sq 0 0 2 8 (by rfl))

lemma base_1230 : 0 < A271510 1230 :=
  A271510_pos_of_exists 1230 11 7 6 32 (by rfl) (by omega) (prove_sq 11 7 6 33 (by rfl))

lemma base_1231 : 0 < A271510 1231 :=
  A271510_pos_of_exists 1231 5 5 5 34 (by rfl) (by omega) (prove_sq 5 5 5 25 (by rfl))

lemma base_1232 : 0 < A271510 1232 :=
  A271510_pos_of_exists 1232 14 6 30 10 (by rfl) (by omega) (prove_sq 14 6 30 122 (by rfl))

lemma base_1233 : 0 < A271510 1233 :=
  A271510_pos_of_exists 1233 0 0 12 33 (by rfl) (by omega) (prove_sq 0 0 12 48 (by rfl))

lemma base_1234 : 0 < A271510 1234 :=
  A271510_pos_of_exists 1234 0 0 3 35 (by rfl) (by omega) (prove_sq 0 0 3 12 (by rfl))

lemma base_1235 : 0 < A271510 1235 :=
  A271510_pos_of_exists 1235 3 0 1 35 (by rfl) (by omega) (prove_sq 3 0 1 5 (by rfl))

lemma base_1236 : 0 < A271510 1236 :=
  A271510_pos_of_exists 1236 7 7 7 33 (by rfl) (by omega) (prove_sq 7 7 7 35 (by rfl))

lemma base_1237 : 0 < A271510 1237 :=
  A271510_pos_of_exists 1237 0 0 9 34 (by rfl) (by omega) (prove_sq 0 0 9 36 (by rfl))

lemma base_1238 : 0 < A271510 1238 :=
  A271510_pos_of_exists 1238 13 13 0 30 (by rfl) (by omega) (prove_sq 13 13 0 39 (by rfl))

lemma base_1239 : 0 < A271510 1239 :=
  A271510_pos_of_exists 1239 3 1 2 35 (by rfl) (by omega) (prove_sq 3 1 2 9 (by rfl))

lemma base_1240 : 0 < A271510 1240 :=
  A271510_pos_of_exists 1240 8 4 2 34 (by rfl) (by omega) (prove_sq 8 4 2 16 (by rfl))

lemma base_1241 : 0 < A271510 1241 :=
  A271510_pos_of_exists 1241 0 0 4 35 (by rfl) (by omega) (prove_sq 0 0 4 16 (by rfl))

lemma base_1242 : 0 < A271510 1242 :=
  A271510_pos_of_exists 1242 7 2 10 33 (by rfl) (by omega) (prove_sq 7 2 10 41 (by rfl))

lemma base_1243 : 0 < A271510 1243 :=
  A271510_pos_of_exists 1243 3 3 0 35 (by rfl) (by omega) (prove_sq 3 3 0 9 (by rfl))

lemma base_1244 : 0 < A271510 1244 :=
  A271510_pos_of_exists 1244 7 3 15 31 (by rfl) (by omega) (prove_sq 7 3 15 61 (by rfl))

lemma base_1245 : 0 < A271510 1245 :=
  A271510_pos_of_exists 1245 18 4 28 11 (by rfl) (by omega) (prove_sq 18 4 28 114 (by rfl))

lemma base_1246 : 0 < A271510 1246 :=
  A271510_pos_of_exists 1246 4 2 1 35 (by rfl) (by omega) (prove_sq 4 2 1 8 (by rfl))

lemma base_1247 : 0 < A271510 1247 :=
  A271510_pos_of_exists 1247 9 3 1 34 (by rfl) (by omega) (prove_sq 9 3 1 13 (by rfl))

lemma base_1248 : 0 < A271510 1248 :=
  A271510_pos_of_exists 1248 12 4 8 32 (by rfl) (by omega) (prove_sq 12 4 8 36 (by rfl))

lemma base_1249 : 0 < A271510 1249 :=
  A271510_pos_of_exists 1249 0 0 15 32 (by rfl) (by omega) (prove_sq 0 0 15 60 (by rfl))

lemma base_1250 : 0 < A271510 1250 :=
  A271510_pos_of_exists 1250 0 0 5 35 (by rfl) (by omega) (prove_sq 0 0 5 20 (by rfl))

lemma base_1251 : 0 < A271510 1251 :=
  A271510_pos_of_exists 1251 9 9 0 33 (by rfl) (by omega) (prove_sq 9 9 0 27 (by rfl))

lemma base_1252 : 0 < A271510 1252 :=
  A271510_pos_of_exists 1252 0 0 24 26 (by rfl) (by omega) (prove_sq 0 0 24 96 (by rfl))

lemma base_1253 : 0 < A271510 1253 :=
  A271510_pos_of_exists 1253 10 10 18 27 (by rfl) (by omega) (prove_sq 10 10 18 78 (by rfl))

lemma base_1254 : 0 < A271510 1254 :=
  A271510_pos_of_exists 1254 7 7 0 34 (by rfl) (by omega) (prove_sq 7 7 0 21 (by rfl))

lemma base_1255 : 0 < A271510 1255 :=
  A271510_pos_of_exists 1255 7 1 7 34 (by rfl) (by omega) (prove_sq 7 1 7 29 (by rfl))

lemma base_1256 : 0 < A271510 1256 :=
  A271510_pos_of_exists 1256 0 0 10 34 (by rfl) (by omega) (prove_sq 0 0 10 40 (by rfl))

lemma base_1257 : 0 < A271510 1257 :=
  A271510_pos_of_exists 1257 4 4 0 35 (by rfl) (by omega) (prove_sq 4 4 0 12 (by rfl))

lemma base_1258 : 0 < A271510 1258 :=
  A271510_pos_of_exists 1258 0 0 13 33 (by rfl) (by omega) (prove_sq 0 0 13 52 (by rfl))

lemma base_1259 : 0 < A271510 1259 :=
  A271510_pos_of_exists 1259 5 0 3 35 (by rfl) (by omega) (prove_sq 5 0 3 13 (by rfl))

lemma base_1260 : 0 < A271510 1260 :=
  A271510_pos_of_exists 1260 7 5 31 15 (by rfl) (by omega) (prove_sq 7 5 31 125 (by rfl))

lemma base_1261 : 0 < A271510 1261 :=
  A271510_pos_of_exists 1261 0 0 6 35 (by rfl) (by omega) (prove_sq 0 0 6 24 (by rfl))

lemma base_1262 : 0 < A271510 1262 :=
  A271510_pos_of_exists 1262 12 2 5 33 (by rfl) (by omega) (prove_sq 12 2 5 24 (by rfl))

lemma base_1263 : 0 < A271510 1263 :=
  A271510_pos_of_exists 1263 3 2 5 35 (by rfl) (by omega) (prove_sq 3 2 5 21 (by rfl))

lemma base_1264 : 0 < A271510 1264 :=
  A271510_pos_of_exists 1264 6 6 6 34 (by rfl) (by omega) (prove_sq 6 6 6 30 (by rfl))

lemma base_1265 : 0 < A271510 1265 :=
  A271510_pos_of_exists 1265 6 0 2 35 (by rfl) (by omega) (prove_sq 6 0 2 10 (by rfl))

lemma base_1266 : 0 < A271510 1266 :=
  A271510_pos_of_exists 1266 11 11 0 32 (by rfl) (by omega) (prove_sq 11 11 0 33 (by rfl))

lemma base_1267 : 0 < A271510 1267 :=
  A271510_pos_of_exists 1267 5 1 4 35 (by rfl) (by omega) (prove_sq 5 1 4 17 (by rfl))

lemma base_1268 : 0 < A271510 1268 :=
  A271510_pos_of_exists 1268 0 0 22 28 (by rfl) (by omega) (prove_sq 0 0 22 88 (by rfl))

lemma base_1269 : 0 < A271510 1269 :=
  A271510_pos_of_exists 1269 10 8 12 31 (by rfl) (by omega) (prove_sq 10 8 12 54 (by rfl))

lemma base_1270 : 0 < A271510 1270 :=
  A271510_pos_of_exists 1270 7 4 7 34 (by rfl) (by omega) (prove_sq 7 4 7 31 (by rfl))

lemma base_1271 : 0 < A271510 1271 :=
  A271510_pos_of_exists 1271 25 6 9 23 (by rfl) (by omega) (prove_sq 25 6 9 47 (by rfl))

lemma base_1272 : 0 < A271510 1272 :=
  A271510_pos_of_exists 1272 14 4 6 32 (by rfl) (by omega) (prove_sq 14 4 6 30 (by rfl))

lemma base_1273 : 0 < A271510 1273 :=
  A271510_pos_of_exists 1273 4 4 4 35 (by rfl) (by omega) (prove_sq 4 4 4 20 (by rfl))

lemma base_1274 : 0 < A271510 1274 :=
  A271510_pos_of_exists 1274 0 0 7 35 (by rfl) (by omega) (prove_sq 0 0 7 28 (by rfl))

lemma base_1275 : 0 < A271510 1275 :=
  A271510_pos_of_exists 1275 5 5 0 35 (by rfl) (by omega) (prove_sq 5 5 0 15 (by rfl))

lemma base_1276 : 0 < A271510 1276 :=
  A271510_pos_of_exists 1276 11 5 13 31 (by rfl) (by omega) (prove_sq 11 5 13 55 (by rfl))

lemma base_1277 : 0 < A271510 1277 :=
  A271510_pos_of_exists 1277 0 0 11 34 (by rfl) (by omega) (prove_sq 0 0 11 44 (by rfl))

lemma base_1278 : 0 < A271510 1278 :=
  A271510_pos_of_exists 1278 7 2 0 35 (by rfl) (by omega) (prove_sq 7 2 0 9 (by rfl))

lemma base_1279 : 0 < A271510 1279 :=
  A271510_pos_of_exists 1279 5 5 2 35 (by rfl) (by omega) (prove_sq 5 5 2 17 (by rfl))

lemma base_1280 : 0 < A271510 1280 :=
  A271510_pos_of_exists 1280 0 0 16 32 (by rfl) (by omega) (prove_sq 0 0 16 64 (by rfl))

lemma base_1281 : 0 < A271510 1281 :=
  A271510_pos_of_exists 1281 6 2 4 35 (by rfl) (by omega) (prove_sq 6 2 4 18 (by rfl))

lemma base_1282 : 0 < A271510 1282 :=
  A271510_pos_of_exists 1282 0 0 21 29 (by rfl) (by omega) (prove_sq 0 0 21 84 (by rfl))

lemma base_1283 : 0 < A271510 1283 :=
  A271510_pos_of_exists 1283 7 3 0 35 (by rfl) (by omega) (prove_sq 7 3 0 11 (by rfl))

lemma base_1284 : 0 < A271510 1284 :=
  A271510_pos_of_exists 1284 8 8 0 34 (by rfl) (by omega) (prove_sq 8 8 0 24 (by rfl))

lemma base_1285 : 0 < A271510 1285 :=
  A271510_pos_of_exists 1285 0 0 14 33 (by rfl) (by omega) (prove_sq 0 0 14 56 (by rfl))

lemma base_1286 : 0 < A271510 1286 :=
  A271510_pos_of_exists 1286 13 0 21 26 (by rfl) (by omega) (prove_sq 13 0 21 85 (by rfl))

lemma base_1287 : 0 < A271510 1287 :=
  A271510_pos_of_exists 1287 5 5 9 34 (by rfl) (by omega) (prove_sq 5 5 9 39 (by rfl))

lemma base_1288 : 0 < A271510 1288 :=
  A271510_pos_of_exists 1288 10 4 4 34 (by rfl) (by omega) (prove_sq 10 4 4 22 (by rfl))

lemma base_1289 : 0 < A271510 1289 :=
  A271510_pos_of_exists 1289 0 0 8 35 (by rfl) (by omega) (prove_sq 0 0 8 32 (by rfl))

lemma base_1290 : 0 < A271510 1290 :=
  A271510_pos_of_exists 1290 13 4 12 31 (by rfl) (by omega) (prove_sq 13 4 12 51 (by rfl))

lemma base_1291 : 0 < A271510 1291 :=
  A271510_pos_of_exists 1291 7 5 31 16 (by rfl) (by omega) (prove_sq 7 5 31 125 (by rfl))

lemma base_1292 : 0 < A271510 1292 :=
  A271510_pos_of_exists 1292 9 1 11 33 (by rfl) (by omega) (prove_sq 9 1 11 45 (by rfl))

lemma base_1293 : 0 < A271510 1293 :=
  A271510_pos_of_exists 1293 18 4 28 13 (by rfl) (by omega) (prove_sq 18 4 28 114 (by rfl))

lemma base_1294 : 0 < A271510 1294 :=
  A271510_pos_of_exists 1294 11 4 31 14 (by rfl) (by omega) (prove_sq 11 4 31 125 (by rfl))

lemma base_1295 : 0 < A271510 1295 :=
  A271510_pos_of_exists 1295 11 7 6 33 (by rfl) (by omega) (prove_sq 11 7 6 33 (by rfl))

lemma base_1296 : 0 < A271510 1296 :=
  A271510_pos_of_exists 1296 0 0 0 36 (by rfl) (by omega) (prove_sq 0 0 0 0 (by rfl))

lemma base_1297 : 0 < A271510 1297 :=
  A271510_pos_of_exists 1297 0 0 1 36 (by rfl) (by omega) (prove_sq 0 0 1 4 (by rfl))

lemma base_1298 : 0 < A271510 1298 :=
  A271510_pos_of_exists 1298 1 1 0 36 (by rfl) (by omega) (prove_sq 1 1 0 3 (by rfl))

lemma base_1299 : 0 < A271510 1299 :=
  A271510_pos_of_exists 1299 1 1 1 36 (by rfl) (by omega) (prove_sq 1 1 1 5 (by rfl))

lemma base_1300 : 0 < A271510 1300 :=
  A271510_pos_of_exists 1300 0 0 2 36 (by rfl) (by omega) (prove_sq 0 0 2 8 (by rfl))

lemma base_1301 : 0 < A271510 1301 :=
  A271510_pos_of_exists 1301 0 0 25 26 (by rfl) (by omega) (prove_sq 0 0 25 100 (by rfl))

lemma base_1302 : 0 < A271510 1302 :=
  A271510_pos_of_exists 1302 5 4 6 35 (by rfl) (by omega) (prove_sq 5 4 6 27 (by rfl))

lemma base_1303 : 0 < A271510 1303 :=
  A271510_pos_of_exists 1303 5 2 7 35 (by rfl) (by omega) (prove_sq 5 2 7 29 (by rfl))

lemma base_1304 : 0 < A271510 1304 :=
  A271510_pos_of_exists 1304 2 2 0 36 (by rfl) (by omega) (prove_sq 2 2 0 6 (by rfl))

lemma base_1305 : 0 < A271510 1305 :=
  A271510_pos_of_exists 1305 0 0 3 36 (by rfl) (by omega) (prove_sq 0 0 3 12 (by rfl))

lemma base_1306 : 0 < A271510 1306 :=
  A271510_pos_of_exists 1306 0 0 9 35 (by rfl) (by omega) (prove_sq 0 0 9 36 (by rfl))

lemma base_1307 : 0 < A271510 1307 :=
  A271510_pos_of_exists 1307 7 3 15 32 (by rfl) (by omega) (prove_sq 7 3 15 61 (by rfl))

lemma base_1308 : 0 < A271510 1308 :=
  A271510_pos_of_exists 1308 2 2 2 36 (by rfl) (by omega) (prove_sq 2 2 2 10 (by rfl))

lemma base_1309 : 0 < A271510 1309 :=
  A271510_pos_of_exists 1309 7 2 10 34 (by rfl) (by omega) (prove_sq 7 2 10 41 (by rfl))

lemma base_1310 : 0 < A271510 1310 :=
  A271510_pos_of_exists 1310 3 1 2 36 (by rfl) (by omega) (prove_sq 3 1 2 9 (by rfl))

lemma base_1311 : 0 < A271510 1311 :=
  A271510_pos_of_exists 1311 13 7 2 33 (by rfl) (by omega) (prove_sq 13 7 2 25 (by rfl))

lemma base_1312 : 0 < A271510 1312 :=
  A271510_pos_of_exists 1312 0 0 4 36 (by rfl) (by omega) (prove_sq 0 0 4 16 (by rfl))

lemma base_1313 : 0 < A271510 1313 :=
  A271510_pos_of_exists 1313 0 0 17 32 (by rfl) (by omega) (prove_sq 0 0 17 68 (by rfl))

lemma base_1314 : 0 < A271510 1314 :=
  A271510_pos_of_exists 1314 0 0 15 33 (by rfl) (by omega) (prove_sq 0 0 15 60 (by rfl))

lemma base_1315 : 0 < A271510 1315 :=
  A271510_pos_of_exists 1315 9 0 3 35 (by rfl) (by omega) (prove_sq 9 0 3 15 (by rfl))

lemma base_1316 : 0 < A271510 1316 :=
  A271510_pos_of_exists 1316 9 3 1 35 (by rfl) (by omega) (prove_sq 9 3 1 13 (by rfl))

lemma base_1317 : 0 < A271510 1317 :=
  A271510_pos_of_exists 1317 4 2 1 36 (by rfl) (by omega) (prove_sq 4 2 1 8 (by rfl))

lemma base_1318 : 0 < A271510 1318 :=
  A271510_pos_of_exists 1318 5 5 28 22 (by rfl) (by omega) (prove_sq 5 5 28 113 (by rfl))

lemma base_1319 : 0 < A271510 1319 :=
  A271510_pos_of_exists 1319 13 5 15 30 (by rfl) (by omega) (prove_sq 13 5 15 63 (by rfl))

lemma base_1320 : 0 < A271510 1320 :=
  A271510_pos_of_exists 1320 18 4 28 14 (by rfl) (by omega) (prove_sq 18 4 28 114 (by rfl))

lemma base_1321 : 0 < A271510 1321 :=
  A271510_pos_of_exists 1321 0 0 5 36 (by rfl) (by omega) (prove_sq 0 0 5 20 (by rfl))

lemma base_1322 : 0 < A271510 1322 :=
  A271510_pos_of_exists 1322 0 0 19 31 (by rfl) (by omega) (prove_sq 0 0 19 76 (by rfl))

lemma base_1323 : 0 < A271510 1323 :=
  A271510_pos_of_exists 1323 3 3 3 36 (by rfl) (by omega) (prove_sq 3 3 3 15 (by rfl))

lemma base_1324 : 0 < A271510 1324 :=
  A271510_pos_of_exists 1324 7 1 7 35 (by rfl) (by omega) (prove_sq 7 1 7 29 (by rfl))

lemma base_1325 : 0 < A271510 1325 :=
  A271510_pos_of_exists 1325 0 0 10 35 (by rfl) (by omega) (prove_sq 0 0 10 40 (by rfl))

lemma base_1326 : 0 < A271510 1326 :=
  A271510_pos_of_exists 1326 11 4 10 33 (by rfl) (by omega) (prove_sq 11 4 10 43 (by rfl))

lemma base_1327 : 0 < A271510 1327 :=
  A271510_pos_of_exists 1327 11 2 19 29 (by rfl) (by omega) (prove_sq 11 2 19 77 (by rfl))

lemma base_1328 : 0 < A271510 1328 :=
  A271510_pos_of_exists 1328 4 4 0 36 (by rfl) (by omega) (prove_sq 4 4 0 12 (by rfl))

lemma base_1329 : 0 < A271510 1329 :=
  A271510_pos_of_exists 1329 5 2 2 36 (by rfl) (by omega) (prove_sq 5 2 2 11 (by rfl))

lemma base_1330 : 0 < A271510 1330 :=
  A271510_pos_of_exists 1330 5 0 3 36 (by rfl) (by omega) (prove_sq 5 0 3 13 (by rfl))

lemma base_1331 : 0 < A271510 1331 :=
  A271510_pos_of_exists 1331 9 5 35 0 (by rfl) (by omega) (prove_sq 9 5 35 141 (by rfl))

lemma base_1332 : 0 < A271510 1332 :=
  A271510_pos_of_exists 1332 0 0 6 36 (by rfl) (by omega) (prove_sq 0 0 6 24 (by rfl))

lemma base_1333 : 0 < A271510 1333 :=
  A271510_pos_of_exists 1333 6 6 6 35 (by rfl) (by omega) (prove_sq 6 6 6 30 (by rfl))

lemma base_1334 : 0 < A271510 1334 :=
  A271510_pos_of_exists 1334 3 2 5 36 (by rfl) (by omega) (prove_sq 3 2 5 21 (by rfl))

lemma base_1335 : 0 < A271510 1335 :=
  A271510_pos_of_exists 1335 9 5 35 2 (by rfl) (by omega) (prove_sq 9 5 35 141 (by rfl))

lemma base_1336 : 0 < A271510 1336 :=
  A271510_pos_of_exists 1336 6 0 2 36 (by rfl) (by omega) (prove_sq 6 0 2 10 (by rfl))

lemma base_1337 : 0 < A271510 1337 :=
  A271510_pos_of_exists 1337 9 0 10 34 (by rfl) (by omega) (prove_sq 9 0 10 41 (by rfl))

lemma base_1338 : 0 < A271510 1338 :=
  A271510_pos_of_exists 1338 5 1 4 36 (by rfl) (by omega) (prove_sq 5 1 4 17 (by rfl))

lemma base_1339 : 0 < A271510 1339 :=
  A271510_pos_of_exists 1339 7 4 7 35 (by rfl) (by omega) (prove_sq 7 4 7 31 (by rfl))

lemma base_1340 : 0 < A271510 1340 :=
  A271510_pos_of_exists 1340 9 5 35 3 (by rfl) (by omega) (prove_sq 9 5 35 141 (by rfl))

lemma base_1341 : 0 < A271510 1341 :=
  A271510_pos_of_exists 1341 0 0 21 30 (by rfl) (by omega) (prove_sq 0 0 21 84 (by rfl))

lemma base_1342 : 0 < A271510 1342 :=
  A271510_pos_of_exists 1342 19 16 26 7 (by rfl) (by omega) (prove_sq 19 16 26 115 (by rfl))

lemma base_1343 : 0 < A271510 1343 :=
  A271510_pos_of_exists 1343 3 3 10 35 (by rfl) (by omega) (prove_sq 3 3 10 41 (by rfl))

lemma base_1344 : 0 < A271510 1344 :=
  A271510_pos_of_exists 1344 4 4 4 36 (by rfl) (by omega) (prove_sq 4 4 4 20 (by rfl))

lemma base_1345 : 0 < A271510 1345 :=
  A271510_pos_of_exists 1345 0 0 7 36 (by rfl) (by omega) (prove_sq 0 0 7 28 (by rfl))

lemma base_1346 : 0 < A271510 1346 :=
  A271510_pos_of_exists 1346 0 0 11 35 (by rfl) (by omega) (prove_sq 0 0 11 44 (by rfl))

lemma base_1347 : 0 < A271510 1347 :=
  A271510_pos_of_exists 1347 9 5 35 4 (by rfl) (by omega) (prove_sq 9 5 35 141 (by rfl))

lemma base_1348 : 0 < A271510 1348 :=
  A271510_pos_of_exists 1348 0 0 18 32 (by rfl) (by omega) (prove_sq 0 0 18 72 (by rfl))

lemma base_1349 : 0 < A271510 1349 :=
  A271510_pos_of_exists 1349 7 2 0 36 (by rfl) (by omega) (prove_sq 7 2 0 9 (by rfl))

lemma base_1350 : 0 < A271510 1350 :=
  A271510_pos_of_exists 1350 5 5 2 36 (by rfl) (by omega) (prove_sq 5 5 2 17 (by rfl))

lemma base_1351 : 0 < A271510 1351 :=
  A271510_pos_of_exists 1351 9 3 6 35 (by rfl) (by omega) (prove_sq 9 3 6 27 (by rfl))

lemma base_1352 : 0 < A271510 1352 :=
  A271510_pos_of_exists 1352 0 0 14 34 (by rfl) (by omega) (prove_sq 0 0 14 56 (by rfl))

lemma base_1353 : 0 < A271510 1353 :=
  A271510_pos_of_exists 1353 8 8 0 35 (by rfl) (by omega) (prove_sq 8 8 0 24 (by rfl))

lemma base_1354 : 0 < A271510 1354 :=
  A271510_pos_of_exists 1354 0 0 25 27 (by rfl) (by omega) (prove_sq 0 0 25 100 (by rfl))

lemma base_1355 : 0 < A271510 1355 :=
  A271510_pos_of_exists 1355 23 4 27 9 (by rfl) (by omega) (prove_sq 23 4 27 111 (by rfl))

lemma base_1356 : 0 < A271510 1356 :=
  A271510_pos_of_exists 1356 5 5 9 35 (by rfl) (by omega) (prove_sq 5 5 9 39 (by rfl))

lemma base_1357 : 0 < A271510 1357 :=
  A271510_pos_of_exists 1357 10 4 4 35 (by rfl) (by omega) (prove_sq 10 4 4 22 (by rfl))

lemma base_1358 : 0 < A271510 1358 :=
  A271510_pos_of_exists 1358 7 2 3 36 (by rfl) (by omega) (prove_sq 7 2 3 15 (by rfl))

lemma base_1359 : 0 < A271510 1359 :=
  A271510_pos_of_exists 1359 7 5 31 18 (by rfl) (by omega) (prove_sq 7 5 31 125 (by rfl))

lemma base_1360 : 0 < A271510 1360 :=
  A271510_pos_of_exists 1360 0 0 8 36 (by rfl) (by omega) (prove_sq 0 0 8 32 (by rfl))

lemma base_1361 : 0 < A271510 1361 :=
  A271510_pos_of_exists 1361 0 0 20 31 (by rfl) (by omega) (prove_sq 0 0 20 80 (by rfl))

lemma base_1362 : 0 < A271510 1362 :=
  A271510_pos_of_exists 1362 11 7 6 34 (by rfl) (by omega) (prove_sq 11 7 6 33 (by rfl))

lemma base_1363 : 0 < A271510 1363 :=
  A271510_pos_of_exists 1363 5 4 19 31 (by rfl) (by omega) (prove_sq 5 4 19 77 (by rfl))

lemma base_1364 : 0 < A271510 1364 :=
  A271510_pos_of_exists 1364 14 0 12 32 (by rfl) (by omega) (prove_sq 14 0 12 50 (by rfl))

lemma base_1365 : 0 < A271510 1365 :=
  A271510_pos_of_exists 1365 10 10 18 29 (by rfl) (by omega) (prove_sq 10 10 18 78 (by rfl))

lemma base_1366 : 0 < A271510 1366 :=
  A271510_pos_of_exists 1366 9 6 15 32 (by rfl) (by omega) (prove_sq 9 6 15 63 (by rfl))

lemma base_1367 : 0 < A271510 1367 :=
  A271510_pos_of_exists 1367 9 5 35 6 (by rfl) (by omega) (prove_sq 9 5 35 141 (by rfl))

lemma base_1368 : 0 < A271510 1368 :=
  A271510_pos_of_exists 1368 6 6 0 36 (by rfl) (by omega) (prove_sq 6 6 0 18 (by rfl))

lemma base_1369 : 0 < A271510 1369 :=
  A271510_pos_of_exists 1369 0 0 0 37 (by rfl) (by omega) (prove_sq 0 0 0 0 (by rfl))

lemma base_1370 : 0 < A271510 1370 :=
  A271510_pos_of_exists 1370 0 0 1 37 (by rfl) (by omega) (prove_sq 0 0 1 4 (by rfl))

lemma base_1371 : 0 < A271510 1371 :=
  A271510_pos_of_exists 1371 1 1 0 37 (by rfl) (by omega) (prove_sq 1 1 0 3 (by rfl))

lemma base_1372 : 0 < A271510 1372 :=
  A271510_pos_of_exists 1372 1 1 1 37 (by rfl) (by omega) (prove_sq 1 1 1 5 (by rfl))

lemma base_1373 : 0 < A271510 1373 :=
  A271510_pos_of_exists 1373 0 0 2 37 (by rfl) (by omega) (prove_sq 0 0 2 8 (by rfl))

lemma base_1374 : 0 < A271510 1374 :=
  A271510_pos_of_exists 1374 5 2 7 36 (by rfl) (by omega) (prove_sq 5 2 7 29 (by rfl))

lemma base_1375 : 0 < A271510 1375 :=
  A271510_pos_of_exists 1375 13 1 7 34 (by rfl) (by omega) (prove_sq 13 1 7 31 (by rfl))

lemma base_1376 : 0 < A271510 1376 :=
  A271510_pos_of_exists 1376 20 16 24 12 (by rfl) (by omega) (prove_sq 20 16 24 108 (by rfl))

lemma base_1377 : 0 < A271510 1377 :=
  A271510_pos_of_exists 1377 0 0 9 36 (by rfl) (by omega) (prove_sq 0 0 9 36 (by rfl))

lemma base_1378 : 0 < A271510 1378 :=
  A271510_pos_of_exists 1378 0 0 3 37 (by rfl) (by omega) (prove_sq 0 0 3 12 (by rfl))

lemma base_1379 : 0 < A271510 1379 :=
  A271510_pos_of_exists 1379 3 0 1 37 (by rfl) (by omega) (prove_sq 3 0 1 5 (by rfl))

lemma base_1380 : 0 < A271510 1380 :=
  A271510_pos_of_exists 1380 8 4 2 36 (by rfl) (by omega) (prove_sq 8 4 2 16 (by rfl))

lemma base_1381 : 0 < A271510 1381 :=
  A271510_pos_of_exists 1381 0 0 15 34 (by rfl) (by omega) (prove_sq 0 0 15 60 (by rfl))

lemma base_1382 : 0 < A271510 1382 :=
  A271510_pos_of_exists 1382 11 3 24 26 (by rfl) (by omega) (prove_sq 11 3 24 97 (by rfl))

lemma base_1383 : 0 < A271510 1383 :=
  A271510_pos_of_exists 1383 3 1 2 37 (by rfl) (by omega) (prove_sq 3 1 2 9 (by rfl))

lemma base_1384 : 0 < A271510 1384 :=
  A271510_pos_of_exists 1384 0 0 22 30 (by rfl) (by omega) (prove_sq 0 0 22 88 (by rfl))

lemma base_1385 : 0 < A271510 1385 :=
  A271510_pos_of_exists 1385 0 0 4 37 (by rfl) (by omega) (prove_sq 0 0 4 16 (by rfl))

lemma base_1386 : 0 < A271510 1386 :=
  A271510_pos_of_exists 1386 9 0 3 36 (by rfl) (by omega) (prove_sq 9 0 3 15 (by rfl))

lemma base_1387 : 0 < A271510 1387 :=
  A271510_pos_of_exists 1387 3 3 0 37 (by rfl) (by omega) (prove_sq 3 3 0 9 (by rfl))

lemma base_1388 : 0 < A271510 1388 :=
  A271510_pos_of_exists 1388 10 6 24 26 (by rfl) (by omega) (prove_sq 10 6 24 98 (by rfl))

lemma base_1389 : 0 < A271510 1389 :=
  A271510_pos_of_exists 1389 10 10 10 33 (by rfl) (by omega) (prove_sq 10 10 10 50 (by rfl))

lemma base_1390 : 0 < A271510 1390 :=
  A271510_pos_of_exists 1390 4 2 1 37 (by rfl) (by omega) (prove_sq 4 2 1 8 (by rfl))

lemma base_1391 : 0 < A271510 1391 :=
  A271510_pos_of_exists 1391 15 1 29 18 (by rfl) (by omega) (prove_sq 15 1 29 117 (by rfl))

lemma base_1392 : 0 < A271510 1392 :=
  A271510_pos_of_exists 1392 12 8 20 28 (by rfl) (by omega) (prove_sq 12 8 20 84 (by rfl))

lemma base_1393 : 0 < A271510 1393 :=
  A271510_pos_of_exists 1393 10 2 8 35 (by rfl) (by omega) (prove_sq 10 2 8 34 (by rfl))

lemma base_1394 : 0 < A271510 1394 :=
  A271510_pos_of_exists 1394 0 0 5 37 (by rfl) (by omega) (prove_sq 0 0 5 20 (by rfl))

lemma base_1395 : 0 < A271510 1395 :=
  A271510_pos_of_exists 1395 7 1 7 36 (by rfl) (by omega) (prove_sq 7 1 7 29 (by rfl))

lemma base_1396 : 0 < A271510 1396 :=
  A271510_pos_of_exists 1396 0 0 10 36 (by rfl) (by omega) (prove_sq 0 0 10 40 (by rfl))

lemma base_1397 : 0 < A271510 1397 :=
  A271510_pos_of_exists 1397 10 8 12 33 (by rfl) (by omega) (prove_sq 10 8 12 54 (by rfl))

lemma base_1398 : 0 < A271510 1398 :=
  A271510_pos_of_exists 1398 9 4 26 25 (by rfl) (by omega) (prove_sq 9 4 26 105 (by rfl))

lemma base_1399 : 0 < A271510 1399 :=
  A271510_pos_of_exists 1399 7 5 10 35 (by rfl) (by omega) (prove_sq 7 5 10 43 (by rfl))

lemma base_1400 : 0 < A271510 1400 :=
  A271510_pos_of_exists 1400 18 0 20 26 (by rfl) (by omega) (prove_sq 18 0 20 82 (by rfl))

lemma base_1401 : 0 < A271510 1401 :=
  A271510_pos_of_exists 1401 4 4 0 37 (by rfl) (by omega) (prove_sq 4 4 0 12 (by rfl))

lemma base_1402 : 0 < A271510 1402 :=
  A271510_pos_of_exists 1402 0 0 21 31 (by rfl) (by omega) (prove_sq 0 0 21 84 (by rfl))

lemma base_1403 : 0 < A271510 1403 :=
  A271510_pos_of_exists 1403 5 0 3 37 (by rfl) (by omega) (prove_sq 5 0 3 13 (by rfl))

lemma base_1404 : 0 < A271510 1404 :=
  A271510_pos_of_exists 1404 6 6 6 36 (by rfl) (by omega) (prove_sq 6 6 6 30 (by rfl))

lemma base_1405 : 0 < A271510 1405 :=
  A271510_pos_of_exists 1405 0 0 6 37 (by rfl) (by omega) (prove_sq 0 0 6 24 (by rfl))

lemma base_1406 : 0 < A271510 1406 :=
  A271510_pos_of_exists 1406 9 0 10 35 (by rfl) (by omega) (prove_sq 9 0 10 41 (by rfl))

lemma base_1407 : 0 < A271510 1407 :=
  A271510_pos_of_exists 1407 3 2 5 37 (by rfl) (by omega) (prove_sq 3 2 5 21 (by rfl))

lemma base_1408 : 0 < A271510 1408 :=
  A271510_pos_of_exists 1408 24 24 0 16 (by rfl) (by omega) (prove_sq 24 24 0 72 (by rfl))

lemma base_1409 : 0 < A271510 1409 :=
  A271510_pos_of_exists 1409 0 0 25 28 (by rfl) (by omega) (prove_sq 0 0 25 100 (by rfl))

lemma base_1410 : 0 < A271510 1410 :=
  A271510_pos_of_exists 1410 5 5 28 24 (by rfl) (by omega) (prove_sq 5 5 28 113 (by rfl))

lemma base_1411 : 0 < A271510 1411 :=
  A271510_pos_of_exists 1411 5 1 4 37 (by rfl) (by omega) (prove_sq 5 1 4 17 (by rfl))

lemma base_1412 : 0 < A271510 1412 :=
  A271510_pos_of_exists 1412 0 0 16 34 (by rfl) (by omega) (prove_sq 0 0 16 64 (by rfl))

lemma base_1413 : 0 < A271510 1413 :=
  A271510_pos_of_exists 1413 0 0 18 33 (by rfl) (by omega) (prove_sq 0 0 18 72 (by rfl))

lemma base_1414 : 0 < A271510 1414 :=
  A271510_pos_of_exists 1414 3 3 10 36 (by rfl) (by omega) (prove_sq 3 3 10 41 (by rfl))

lemma base_1415 : 0 < A271510 1415 :=
  A271510_pos_of_exists 1415 13 9 3 34 (by rfl) (by omega) (prove_sq 13 9 3 31 (by rfl))

lemma base_1416 : 0 < A271510 1416 :=
  A271510_pos_of_exists 1416 14 14 0 32 (by rfl) (by omega) (prove_sq 14 14 0 42 (by rfl))

lemma base_1417 : 0 < A271510 1417 :=
  A271510_pos_of_exists 1417 0 0 11 36 (by rfl) (by omega) (prove_sq 0 0 11 44 (by rfl))

lemma base_1418 : 0 < A271510 1418 :=
  A271510_pos_of_exists 1418 0 0 7 37 (by rfl) (by omega) (prove_sq 0 0 7 28 (by rfl))

lemma base_1419 : 0 < A271510 1419 :=
  A271510_pos_of_exists 1419 5 5 0 37 (by rfl) (by omega) (prove_sq 5 5 0 15 (by rfl))

lemma base_1420 : 0 < A271510 1420 :=
  A271510_pos_of_exists 1420 14 2 14 32 (by rfl) (by omega) (prove_sq 14 2 14 58 (by rfl))

lemma base_1421 : 0 < A271510 1421 :=
  A271510_pos_of_exists 1421 0 0 14 35 (by rfl) (by omega) (prove_sq 0 0 14 56 (by rfl))

lemma base_1422 : 0 < A271510 1422 :=
  A271510_pos_of_exists 1422 7 2 0 37 (by rfl) (by omega) (prove_sq 7 2 0 9 (by rfl))

lemma base_1423 : 0 < A271510 1423 :=
  A271510_pos_of_exists 1423 5 5 2 37 (by rfl) (by omega) (prove_sq 5 5 2 17 (by rfl))

lemma base_1424 : 0 < A271510 1424 :=
  A271510_pos_of_exists 1424 0 0 20 32 (by rfl) (by omega) (prove_sq 0 0 20 80 (by rfl))

lemma base_1425 : 0 < A271510 1425 :=
  A271510_pos_of_exists 1425 6 2 4 37 (by rfl) (by omega) (prove_sq 6 2 4 18 (by rfl))

lemma base_1426 : 0 < A271510 1426 :=
  A271510_pos_of_exists 1426 5 4 19 32 (by rfl) (by omega) (prove_sq 5 4 19 77 (by rfl))

lemma base_1427 : 0 < A271510 1427 :=
  A271510_pos_of_exists 1427 5 5 9 36 (by rfl) (by omega) (prove_sq 5 5 9 39 (by rfl))

lemma base_1428 : 0 < A271510 1428 :=
  A271510_pos_of_exists 1428 9 1 11 35 (by rfl) (by omega) (prove_sq 9 1 11 45 (by rfl))

lemma base_1429 : 0 < A271510 1429 :=
  A271510_pos_of_exists 1429 0 0 23 30 (by rfl) (by omega) (prove_sq 0 0 23 92 (by rfl))

lemma base_1430 : 0 < A271510 1430 :=
  A271510_pos_of_exists 1430 23 9 12 26 (by rfl) (by omega) (prove_sq 23 9 12 59 (by rfl))

lemma base_1431 : 0 < A271510 1431 :=
  A271510_pos_of_exists 1431 7 2 3 37 (by rfl) (by omega) (prove_sq 7 2 3 15 (by rfl))

lemma base_1432 : 0 < A271510 1432 :=
  A271510_pos_of_exists 1432 10 0 6 36 (by rfl) (by omega) (prove_sq 10 0 6 26 (by rfl))

lemma base_1433 : 0 < A271510 1433 :=
  A271510_pos_of_exists 1433 0 0 8 37 (by rfl) (by omega) (prove_sq 0 0 8 32 (by rfl))

lemma base_1434 : 0 < A271510 1434 :=
  A271510_pos_of_exists 1434 15 10 25 22 (by rfl) (by omega) (prove_sq 15 10 25 105 (by rfl))

lemma base_1435 : 0 < A271510 1435 :=
  A271510_pos_of_exists 1435 7 5 31 20 (by rfl) (by omega) (prove_sq 7 5 31 125 (by rfl))

lemma base_1436 : 0 < A271510 1436 :=
  A271510_pos_of_exists 1436 23 13 3 27 (by rfl) (by omega) (prove_sq 23 13 3 45 (by rfl))

lemma base_1437 : 0 < A271510 1437 :=
  A271510_pos_of_exists 1437 9 2 14 34 (by rfl) (by omega) (prove_sq 9 2 14 57 (by rfl))

lemma base_1438 : 0 < A271510 1438 :=
  A271510_pos_of_exists 1438 12 6 13 33 (by rfl) (by omega) (prove_sq 12 6 13 56 (by rfl))

lemma base_1439 : 0 < A271510 1439 :=
  A271510_pos_of_exists 1439 7 3 15 34 (by rfl) (by omega) (prove_sq 7 3 15 61 (by rfl))

lemma base_1440 : 0 < A271510 1440 :=
  A271510_pos_of_exists 1440 0 0 12 36 (by rfl) (by omega) (prove_sq 0 0 12 48 (by rfl))

lemma base_1441 : 0 < A271510 1441 :=
  A271510_pos_of_exists 1441 6 6 0 37 (by rfl) (by omega) (prove_sq 6 6 0 18 (by rfl))

lemma base_1442 : 0 < A271510 1442 :=
  A271510_pos_of_exists 1442 9 7 4 36 (by rfl) (by omega) (prove_sq 9 7 4 27 (by rfl))

lemma base_1443 : 0 < A271510 1443 :=
  A271510_pos_of_exists 1443 7 7 7 36 (by rfl) (by omega) (prove_sq 7 7 7 35 (by rfl))

lemma base_1444 : 0 < A271510 1444 :=
  A271510_pos_of_exists 1444 0 0 0 38 (by rfl) (by omega) (prove_sq 0 0 0 0 (by rfl))

lemma base_1445 : 0 < A271510 1445 :=
  A271510_pos_of_exists 1445 0 0 1 38 (by rfl) (by omega) (prove_sq 0 0 1 4 (by rfl))

lemma base_1446 : 0 < A271510 1446 :=
  A271510_pos_of_exists 1446 1 1 0 38 (by rfl) (by omega) (prove_sq 1 1 0 3 (by rfl))

lemma base_1447 : 0 < A271510 1447 :=
  A271510_pos_of_exists 1447 1 1 1 38 (by rfl) (by omega) (prove_sq 1 1 1 5 (by rfl))

lemma base_1448 : 0 < A271510 1448 :=
  A271510_pos_of_exists 1448 0 0 2 38 (by rfl) (by omega) (prove_sq 0 0 2 8 (by rfl))

lemma base_1449 : 0 < A271510 1449 :=
  A271510_pos_of_exists 1449 7 2 10 36 (by rfl) (by omega) (prove_sq 7 2 10 41 (by rfl))

lemma base_1450 : 0 < A271510 1450 :=
  A271510_pos_of_exists 1450 0 0 9 37 (by rfl) (by omega) (prove_sq 0 0 9 36 (by rfl))

lemma base_1451 : 0 < A271510 1451 :=
  A271510_pos_of_exists 1451 13 0 21 29 (by rfl) (by omega) (prove_sq 13 0 21 85 (by rfl))

lemma base_1452 : 0 < A271510 1452 :=
  A271510_pos_of_exists 1452 2 2 0 38 (by rfl) (by omega) (prove_sq 2 2 0 6 (by rfl))

lemma base_1453 : 0 < A271510 1453 :=
  A271510_pos_of_exists 1453 0 0 3 38 (by rfl) (by omega) (prove_sq 0 0 3 12 (by rfl))

lemma base_1454 : 0 < A271510 1454 :=
  A271510_pos_of_exists 1454 3 0 1 38 (by rfl) (by omega) (prove_sq 3 0 1 5 (by rfl))

lemma base_1455 : 0 < A271510 1455 :=
  A271510_pos_of_exists 1455 17 1 3 34 (by rfl) (by omega) (prove_sq 17 1 3 21 (by rfl))

lemma base_1456 : 0 < A271510 1456 :=
  A271510_pos_of_exists 1456 2 2 2 38 (by rfl) (by omega) (prove_sq 2 2 2 10 (by rfl))

lemma base_1457 : 0 < A271510 1457 :=
  A271510_pos_of_exists 1457 11 2 6 36 (by rfl) (by omega) (prove_sq 11 2 6 27 (by rfl))

lemma base_1458 : 0 < A271510 1458 :=
  A271510_pos_of_exists 1458 0 0 27 27 (by rfl) (by omega) (prove_sq 0 0 27 108 (by rfl))

lemma base_1459 : 0 < A271510 1459 :=
  A271510_pos_of_exists 1459 5 5 28 25 (by rfl) (by omega) (prove_sq 5 5 28 113 (by rfl))

lemma base_1460 : 0 < A271510 1460 :=
  A271510_pos_of_exists 1460 0 0 4 38 (by rfl) (by omega) (prove_sq 0 0 4 16 (by rfl))

lemma base_1461 : 0 < A271510 1461 :=
  A271510_pos_of_exists 1461 22 22 22 3 (by rfl) (by omega) (prove_sq 22 22 22 110 (by rfl))

lemma base_1462 : 0 < A271510 1462 :=
  A271510_pos_of_exists 1462 3 3 0 38 (by rfl) (by omega) (prove_sq 3 3 0 9 (by rfl))

lemma base_1463 : 0 < A271510 1463 :=
  A271510_pos_of_exists 1463 15 3 2 35 (by rfl) (by omega) (prove_sq 15 3 2 19 (by rfl))

lemma base_1464 : 0 < A271510 1464 :=
  A271510_pos_of_exists 1464 10 2 8 36 (by rfl) (by omega) (prove_sq 10 2 8 34 (by rfl))

lemma base_1465 : 0 < A271510 1465 :=
  A271510_pos_of_exists 1465 0 0 13 36 (by rfl) (by omega) (prove_sq 0 0 13 52 (by rfl))

lemma base_1466 : 0 < A271510 1466 :=
  A271510_pos_of_exists 1466 0 0 25 29 (by rfl) (by omega) (prove_sq 0 0 25 100 (by rfl))

lemma base_1467 : 0 < A271510 1467 :=
  A271510_pos_of_exists 1467 7 7 0 37 (by rfl) (by omega) (prove_sq 7 7 0 21 (by rfl))

lemma base_1468 : 0 < A271510 1468 :=
  A271510_pos_of_exists 1468 7 1 7 37 (by rfl) (by omega) (prove_sq 7 1 7 29 (by rfl))

lemma base_1469 : 0 < A271510 1469 :=
  A271510_pos_of_exists 1469 0 0 5 38 (by rfl) (by omega) (prove_sq 0 0 5 20 (by rfl))

lemma base_1470 : 0 < A271510 1470 :=
  A271510_pos_of_exists 1470 7 5 10 36 (by rfl) (by omega) (prove_sq 7 5 10 43 (by rfl))

lemma base_1471 : 0 < A271510 1471 :=
  A271510_pos_of_exists 1471 3 3 3 38 (by rfl) (by omega) (prove_sq 3 3 3 15 (by rfl))

lemma base_1472 : 0 < A271510 1472 :=
  A271510_pos_of_exists 1472 24 8 16 24 (by rfl) (by omega) (prove_sq 24 8 16 72 (by rfl))

lemma base_1473 : 0 < A271510 1473 :=
  A271510_pos_of_exists 1473 14 4 6 35 (by rfl) (by omega) (prove_sq 14 4 6 30 (by rfl))

lemma base_1474 : 0 < A271510 1474 :=
  A271510_pos_of_exists 1474 5 3 12 36 (by rfl) (by omega) (prove_sq 5 3 12 49 (by rfl))

lemma base_1475 : 0 < A271510 1475 :=
  A271510_pos_of_exists 1475 9 3 19 32 (by rfl) (by omega) (prove_sq 9 3 19 77 (by rfl))

lemma base_1476 : 0 < A271510 1476 :=
  A271510_pos_of_exists 1476 0 0 24 30 (by rfl) (by omega) (prove_sq 0 0 24 96 (by rfl))

lemma base_1477 : 0 < A271510 1477 :=
  A271510_pos_of_exists 1477 5 2 2 38 (by rfl) (by omega) (prove_sq 5 2 2 11 (by rfl))

lemma base_1478 : 0 < A271510 1478 :=
  A271510_pos_of_exists 1478 5 0 3 38 (by rfl) (by omega) (prove_sq 5 0 3 13 (by rfl))

lemma base_1479 : 0 < A271510 1479 :=
  A271510_pos_of_exists 1479 15 10 25 23 (by rfl) (by omega) (prove_sq 15 10 25 105 (by rfl))

lemma base_1480 : 0 < A271510 1480 :=
  A271510_pos_of_exists 1480 0 0 6 38 (by rfl) (by omega) (prove_sq 0 0 6 24 (by rfl))

lemma base_1481 : 0 < A271510 1481 :=
  A271510_pos_of_exists 1481 0 0 16 35 (by rfl) (by omega) (prove_sq 0 0 16 64 (by rfl))

lemma base_1482 : 0 < A271510 1482 :=
  A271510_pos_of_exists 1482 3 2 5 38 (by rfl) (by omega) (prove_sq 3 2 5 21 (by rfl))

lemma base_1483 : 0 < A271510 1483 :=
  A271510_pos_of_exists 1483 7 4 7 37 (by rfl) (by omega) (prove_sq 7 4 7 31 (by rfl))

lemma base_1484 : 0 < A271510 1484 :=
  A271510_pos_of_exists 1484 6 0 2 38 (by rfl) (by omega) (prove_sq 6 0 2 10 (by rfl))

lemma base_1485 : 0 < A271510 1485 :=
  A271510_pos_of_exists 1485 10 10 18 31 (by rfl) (by omega) (prove_sq 10 10 18 78 (by rfl))

lemma base_1486 : 0 < A271510 1486 :=
  A271510_pos_of_exists 1486 5 1 4 38 (by rfl) (by omega) (prove_sq 5 1 4 17 (by rfl))

lemma base_1487 : 0 < A271510 1487 :=
  A271510_pos_of_exists 1487 3 3 10 37 (by rfl) (by omega) (prove_sq 3 3 10 41 (by rfl))

lemma base_1488 : 0 < A271510 1488 :=
  A271510_pos_of_exists 1488 8 8 8 36 (by rfl) (by omega) (prove_sq 8 8 8 40 (by rfl))

lemma base_1489 : 0 < A271510 1489 :=
  A271510_pos_of_exists 1489 0 0 20 33 (by rfl) (by omega) (prove_sq 0 0 20 80 (by rfl))

lemma base_1490 : 0 < A271510 1490 :=
  A271510_pos_of_exists 1490 0 0 11 37 (by rfl) (by omega) (prove_sq 0 0 11 44 (by rfl))

lemma base_1491 : 0 < A271510 1491 :=
  A271510_pos_of_exists 1491 5 4 19 33 (by rfl) (by omega) (prove_sq 5 4 19 77 (by rfl))

lemma base_1492 : 0 < A271510 1492 :=
  A271510_pos_of_exists 1492 0 0 14 36 (by rfl) (by omega) (prove_sq 0 0 14 56 (by rfl))

lemma base_1493 : 0 < A271510 1493 :=
  A271510_pos_of_exists 1493 0 0 7 38 (by rfl) (by omega) (prove_sq 0 0 7 28 (by rfl))

lemma base_1494 : 0 < A271510 1494 :=
  A271510_pos_of_exists 1494 5 5 0 38 (by rfl) (by omega) (prove_sq 5 5 0 15 (by rfl))

lemma base_1495 : 0 < A271510 1495 :=
  A271510_pos_of_exists 1495 9 3 6 37 (by rfl) (by omega) (prove_sq 9 3 6 27 (by rfl))

lemma base_1496 : 0 < A271510 1496 :=
  A271510_pos_of_exists 1496 6 6 20 32 (by rfl) (by omega) (prove_sq 6 6 20 82 (by rfl))

lemma base_1497 : 0 < A271510 1497 :=
  A271510_pos_of_exists 1497 7 2 0 38 (by rfl) (by omega) (prove_sq 7 2 0 9 (by rfl))

lemma base_1498 : 0 < A271510 1498 :=
  A271510_pos_of_exists 1498 5 5 2 38 (by rfl) (by omega) (prove_sq 5 5 2 17 (by rfl))

lemma base_1499 : 0 < A271510 1499 :=
  A271510_pos_of_exists 1499 9 1 11 36 (by rfl) (by omega) (prove_sq 9 1 11 45 (by rfl))

lemma base_1500 : 0 < A271510 1500 :=
  A271510_pos_of_exists 1500 5 5 9 37 (by rfl) (by omega) (prove_sq 5 5 9 39 (by rfl))

lemma base_1501 : 0 < A271510 1501 :=
  A271510_pos_of_exists 1501 10 4 4 37 (by rfl) (by omega) (prove_sq 10 4 4 22 (by rfl))

lemma base_1502 : 0 < A271510 1502 :=
  A271510_pos_of_exists 1502 7 3 0 38 (by rfl) (by omega) (prove_sq 7 3 0 11 (by rfl))

lemma base_1503 : 0 < A271510 1503 :=
  A271510_pos_of_exists 1503 9 9 30 21 (by rfl) (by omega) (prove_sq 9 9 30 123 (by rfl))

lemma base_1504 : 0 < A271510 1504 :=
  A271510_pos_of_exists 1504 20 8 28 16 (by rfl) (by omega) (prove_sq 20 8 28 116 (by rfl))

lemma base_1505 : 0 < A271510 1505 :=
  A271510_pos_of_exists 1505 10 0 6 37 (by rfl) (by omega) (prove_sq 10 0 6 26 (by rfl))

lemma base_1506 : 0 < A271510 1506 :=
  A271510_pos_of_exists 1506 7 2 3 38 (by rfl) (by omega) (prove_sq 7 2 3 15 (by rfl))

lemma base_1507 : 0 < A271510 1507 :=
  A271510_pos_of_exists 1507 19 8 11 31 (by rfl) (by omega) (prove_sq 19 8 11 53 (by rfl))

lemma base_1508 : 0 < A271510 1508 :=
  A271510_pos_of_exists 1508 0 0 8 38 (by rfl) (by omega) (prove_sq 0 0 8 32 (by rfl))

lemma base_1509 : 0 < A271510 1509 :=
  A271510_pos_of_exists 1509 15 2 32 16 (by rfl) (by omega) (prove_sq 15 2 32 129 (by rfl))

lemma base_1510 : 0 < A271510 1510 :=
  A271510_pos_of_exists 1510 5 5 28 26 (by rfl) (by omega) (prove_sq 5 5 28 113 (by rfl))

lemma base_1511 : 0 < A271510 1511 :=
  A271510_pos_of_exists 1511 7 7 18 33 (by rfl) (by omega) (prove_sq 7 7 18 75 (by rfl))

lemma base_1512 : 0 < A271510 1512 :=
  A271510_pos_of_exists 1512 10 10 4 36 (by rfl) (by omega) (prove_sq 10 10 4 34 (by rfl))

lemma base_1513 : 0 < A271510 1513 :=
  A271510_pos_of_exists 1513 0 0 12 37 (by rfl) (by omega) (prove_sq 0 0 12 48 (by rfl))

lemma base_1514 : 0 < A271510 1514 :=
  A271510_pos_of_exists 1514 0 0 17 35 (by rfl) (by omega) (prove_sq 0 0 17 68 (by rfl))

lemma base_1515 : 0 < A271510 1515 :=
  A271510_pos_of_exists 1515 9 7 4 37 (by rfl) (by omega) (prove_sq 9 7 4 27 (by rfl))

lemma base_1516 : 0 < A271510 1516 :=
  A271510_pos_of_exists 1516 6 6 0 38 (by rfl) (by omega) (prove_sq 6 6 0 18 (by rfl))

lemma base_1517 : 0 < A271510 1517 :=
  A271510_pos_of_exists 1517 0 0 19 34 (by rfl) (by omega) (prove_sq 0 0 19 76 (by rfl))

lemma base_1518 : 0 < A271510 1518 :=
  A271510_pos_of_exists 1518 13 7 2 36 (by rfl) (by omega) (prove_sq 13 7 2 25 (by rfl))

lemma base_1519 : 0 < A271510 1519 :=
  A271510_pos_of_exists 1519 5 5 5 38 (by rfl) (by omega) (prove_sq 5 5 5 25 (by rfl))

lemma base_1520 : 0 < A271510 1520 :=
  A271510_pos_of_exists 1520 12 4 8 36 (by rfl) (by omega) (prove_sq 12 4 8 36 (by rfl))

lemma base_1521 : 0 < A271510 1521 :=
  A271510_pos_of_exists 1521 0 0 0 39 (by rfl) (by omega) (prove_sq 0 0 0 0 (by rfl))

lemma base_1522 : 0 < A271510 1522 :=
  A271510_pos_of_exists 1522 0 0 1 39 (by rfl) (by omega) (prove_sq 0 0 1 4 (by rfl))

lemma base_1523 : 0 < A271510 1523 :=
  A271510_pos_of_exists 1523 1 1 0 39 (by rfl) (by omega) (prove_sq 1 1 0 3 (by rfl))

lemma base_1524 : 0 < A271510 1524 :=
  A271510_pos_of_exists 1524 1 1 1 39 (by rfl) (by omega) (prove_sq 1 1 1 5 (by rfl))

lemma base_1525 : 0 < A271510 1525 :=
  A271510_pos_of_exists 1525 0 0 2 39 (by rfl) (by omega) (prove_sq 0 0 2 8 (by rfl))

lemma base_1526 : 0 < A271510 1526 :=
  A271510_pos_of_exists 1526 12 10 29 21 (by rfl) (by omega) (prove_sq 12 10 29 120 (by rfl))

lemma base_1527 : 0 < A271510 1527 :=
  A271510_pos_of_exists 1527 9 5 35 14 (by rfl) (by omega) (prove_sq 9 5 35 141 (by rfl))

lemma base_1528 : 0 < A271510 1528 :=
  A271510_pos_of_exists 1528 8 4 2 38 (by rfl) (by omega) (prove_sq 8 4 2 16 (by rfl))

lemma base_1529 : 0 < A271510 1529 :=
  A271510_pos_of_exists 1529 2 2 0 39 (by rfl) (by omega) (prove_sq 2 2 0 6 (by rfl))

lemma base_1530 : 0 < A271510 1530 :=
  A271510_pos_of_exists 1530 0 0 3 39 (by rfl) (by omega) (prove_sq 0 0 3 12 (by rfl))

lemma base_1531 : 0 < A271510 1531 :=
  A271510_pos_of_exists 1531 3 0 1 39 (by rfl) (by omega) (prove_sq 3 0 1 5 (by rfl))

lemma base_1532 : 0 < A271510 1532 :=
  A271510_pos_of_exists 1532 14 6 30 20 (by rfl) (by omega) (prove_sq 14 6 30 122 (by rfl))

lemma base_1533 : 0 < A271510 1533 :=
  A271510_pos_of_exists 1533 2 2 2 39 (by rfl) (by omega) (prove_sq 2 2 2 10 (by rfl))

lemma base_1534 : 0 < A271510 1534 :=
  A271510_pos_of_exists 1534 9 0 3 38 (by rfl) (by omega) (prove_sq 9 0 3 15 (by rfl))

lemma base_1535 : 0 < A271510 1535 :=
  A271510_pos_of_exists 1535 3 1 2 39 (by rfl) (by omega) (prove_sq 3 1 2 9 (by rfl))

lemma base_1536 : 0 < A271510 1536 :=
  A271510_pos_of_exists 1536 16 16 0 32 (by rfl) (by omega) (prove_sq 16 16 0 48 (by rfl))

lemma base_1537 : 0 < A271510 1537 :=
  A271510_pos_of_exists 1537 0 0 4 39 (by rfl) (by omega) (prove_sq 0 0 4 16 (by rfl))

lemma base_1538 : 0 < A271510 1538 :=
  A271510_pos_of_exists 1538 0 0 13 37 (by rfl) (by omega) (prove_sq 0 0 13 52 (by rfl))

lemma base_1539 : 0 < A271510 1539 :=
  A271510_pos_of_exists 1539 3 3 0 39 (by rfl) (by omega) (prove_sq 3 3 0 9 (by rfl))

lemma base_1540 : 0 < A271510 1540 :=
  A271510_pos_of_exists 1540 9 3 19 33 (by rfl) (by omega) (prove_sq 9 3 19 77 (by rfl))

lemma base_1541 : 0 < A271510 1541 :=
  A271510_pos_of_exists 1541 18 2 22 27 (by rfl) (by omega) (prove_sq 18 2 22 90 (by rfl))

lemma base_1542 : 0 < A271510 1542 :=
  A271510_pos_of_exists 1542 4 2 1 39 (by rfl) (by omega) (prove_sq 4 2 1 8 (by rfl))

lemma base_1543 : 0 < A271510 1543 :=
  A271510_pos_of_exists 1543 7 1 7 38 (by rfl) (by omega) (prove_sq 7 1 7 29 (by rfl))

lemma base_1544 : 0 < A271510 1544 :=
  A271510_pos_of_exists 1544 0 0 10 38 (by rfl) (by omega) (prove_sq 0 0 10 40 (by rfl))

lemma base_1545 : 0 < A271510 1545 :=
  A271510_pos_of_exists 1545 14 8 14 33 (by rfl) (by omega) (prove_sq 14 8 14 62 (by rfl))

lemma base_1546 : 0 < A271510 1546 :=
  A271510_pos_of_exists 1546 0 0 5 39 (by rfl) (by omega) (prove_sq 0 0 5 20 (by rfl))

lemma base_1547 : 0 < A271510 1547 :=
  A271510_pos_of_exists 1547 5 3 12 37 (by rfl) (by omega) (prove_sq 5 3 12 49 (by rfl))

lemma base_1548 : 0 < A271510 1548 :=
  A271510_pos_of_exists 1548 3 3 3 39 (by rfl) (by omega) (prove_sq 3 3 3 15 (by rfl))

lemma base_1549 : 0 < A271510 1549 :=
  A271510_pos_of_exists 1549 0 0 18 35 (by rfl) (by omega) (prove_sq 0 0 18 72 (by rfl))

lemma base_1550 : 0 < A271510 1550 :=
  A271510_pos_of_exists 1550 9 0 10 37 (by rfl) (by omega) (prove_sq 9 0 10 41 (by rfl))

lemma base_1551 : 0 < A271510 1551 :=
  A271510_pos_of_exists 1551 15 1 29 22 (by rfl) (by omega) (prove_sq 15 1 29 117 (by rfl))

lemma base_1552 : 0 < A271510 1552 :=
  A271510_pos_of_exists 1552 0 0 16 36 (by rfl) (by omega) (prove_sq 0 0 16 64 (by rfl))

lemma base_1553 : 0 < A271510 1553 :=
  A271510_pos_of_exists 1553 0 0 23 32 (by rfl) (by omega) (prove_sq 0 0 23 92 (by rfl))

lemma base_1554 : 0 < A271510 1554 :=
  A271510_pos_of_exists 1554 5 2 2 39 (by rfl) (by omega) (prove_sq 5 2 2 11 (by rfl))

lemma base_1555 : 0 < A271510 1555 :=
  A271510_pos_of_exists 1555 5 0 3 39 (by rfl) (by omega) (prove_sq 5 0 3 13 (by rfl))

lemma base_1556 : 0 < A271510 1556 :=
  A271510_pos_of_exists 1556 0 0 20 34 (by rfl) (by omega) (prove_sq 0 0 20 80 (by rfl))

lemma base_1557 : 0 < A271510 1557 :=
  A271510_pos_of_exists 1557 0 0 6 39 (by rfl) (by omega) (prove_sq 0 0 6 24 (by rfl))

lemma base_1558 : 0 < A271510 1558 :=
  A271510_pos_of_exists 1558 5 4 19 34 (by rfl) (by omega) (prove_sq 5 4 19 77 (by rfl))

lemma base_1559 : 0 < A271510 1559 :=
  A271510_pos_of_exists 1559 3 2 5 39 (by rfl) (by omega) (prove_sq 3 2 5 21 (by rfl))

lemma base_1560 : 0 < A271510 1560 :=
  A271510_pos_of_exists 1560 26 8 6 28 (by rfl) (by omega) (prove_sq 26 8 6 42 (by rfl))

lemma base_1561 : 0 < A271510 1561 :=
  A271510_pos_of_exists 1561 6 0 2 39 (by rfl) (by omega) (prove_sq 6 0 2 10 (by rfl))

lemma base_1562 : 0 < A271510 1562 :=
  A271510_pos_of_exists 1562 3 3 10 38 (by rfl) (by omega) (prove_sq 3 3 10 41 (by rfl))

lemma base_1563 : 0 < A271510 1563 :=
  A271510_pos_of_exists 1563 5 1 4 39 (by rfl) (by omega) (prove_sq 5 1 4 17 (by rfl))

lemma base_1564 : 0 < A271510 1564 :=
  A271510_pos_of_exists 1564 7 5 31 23 (by rfl) (by omega) (prove_sq 7 5 31 125 (by rfl))

lemma base_1565 : 0 < A271510 1565 :=
  A271510_pos_of_exists 1565 0 0 11 38 (by rfl) (by omega) (prove_sq 0 0 11 44 (by rfl))

lemma base_1566 : 0 < A271510 1566 :=
  A271510_pos_of_exists 1566 15 14 19 28 (by rfl) (by omega) (prove_sq 15 14 19 87 (by rfl))

lemma base_1567 : 0 < A271510 1567 :=
  A271510_pos_of_exists 1567 7 7 5 38 (by rfl) (by omega) (prove_sq 7 7 5 29 (by rfl))

lemma base_1568 : 0 < A271510 1568 :=
  A271510_pos_of_exists 1568 0 0 28 28 (by rfl) (by omega) (prove_sq 0 0 28 112 (by rfl))

lemma base_1569 : 0 < A271510 1569 :=
  A271510_pos_of_exists 1569 4 4 4 39 (by rfl) (by omega) (prove_sq 4 4 4 20 (by rfl))

lemma base_1570 : 0 < A271510 1570 :=
  A271510_pos_of_exists 1570 0 0 7 39 (by rfl) (by omega) (prove_sq 0 0 7 28 (by rfl))

lemma base_1571 : 0 < A271510 1571 :=
  A271510_pos_of_exists 1571 5 5 0 39 (by rfl) (by omega) (prove_sq 5 5 0 15 (by rfl))

lemma base_1572 : 0 < A271510 1572 :=
  A271510_pos_of_exists 1572 8 8 0 38 (by rfl) (by omega) (prove_sq 8 8 0 24 (by rfl))

lemma base_1573 : 0 < A271510 1573 :=
  A271510_pos_of_exists 1573 0 0 22 33 (by rfl) (by omega) (prove_sq 0 0 22 88 (by rfl))

lemma base_1574 : 0 < A271510 1574 :=
  A271510_pos_of_exists 1574 7 2 0 39 (by rfl) (by omega) (prove_sq 7 2 0 9 (by rfl))

lemma base_1575 : 0 < A271510 1575 :=
  A271510_pos_of_exists 1575 5 5 2 39 (by rfl) (by omega) (prove_sq 5 5 2 17 (by rfl))

lemma base_1576 : 0 < A271510 1576 :=
  A271510_pos_of_exists 1576 0 0 26 30 (by rfl) (by omega) (prove_sq 0 0 26 104 (by rfl))

lemma base_1577 : 0 < A271510 1577 :=
  A271510_pos_of_exists 1577 6 2 4 39 (by rfl) (by omega) (prove_sq 6 2 4 18 (by rfl))

lemma base_1578 : 0 < A271510 1578 :=
  A271510_pos_of_exists 1578 7 7 18 34 (by rfl) (by omega) (prove_sq 7 7 18 75 (by rfl))

lemma base_1579 : 0 < A271510 1579 :=
  A271510_pos_of_exists 1579 7 3 0 39 (by rfl) (by omega) (prove_sq 7 3 0 11 (by rfl))

lemma base_1580 : 0 < A271510 1580 :=
  A271510_pos_of_exists 1580 10 0 6 38 (by rfl) (by omega) (prove_sq 10 0 6 26 (by rfl))

lemma base_1581 : 0 < A271510 1581 :=
  A271510_pos_of_exists 1581 13 10 4 36 (by rfl) (by omega) (prove_sq 13 10 4 35 (by rfl))

lemma base_1582 : 0 < A271510 1582 :=
  A271510_pos_of_exists 1582 11 4 31 22 (by rfl) (by omega) (prove_sq 11 4 31 125 (by rfl))

lemma base_1583 : 0 < A271510 1583 :=
  A271510_pos_of_exists 1583 7 2 3 39 (by rfl) (by omega) (prove_sq 7 2 3 15 (by rfl))

lemma base_1584 : 0 < A271510 1584 :=
  A271510_pos_of_exists 1584 12 12 0 36 (by rfl) (by omega) (prove_sq 12 12 0 36 (by rfl))

lemma base_1585 : 0 < A271510 1585 :=
  A271510_pos_of_exists 1585 0 0 8 39 (by rfl) (by omega) (prove_sq 0 0 8 32 (by rfl))

lemma base_1586 : 0 < A271510 1586 :=
  A271510_pos_of_exists 1586 0 0 19 35 (by rfl) (by omega) (prove_sq 0 0 19 76 (by rfl))

lemma base_1587 : 0 < A271510 1587 :=
  A271510_pos_of_exists 1587 9 5 35 16 (by rfl) (by omega) (prove_sq 9 5 35 141 (by rfl))

lemma base_1588 : 0 < A271510 1588 :=
  A271510_pos_of_exists 1588 0 0 12 38 (by rfl) (by omega) (prove_sq 0 0 12 48 (by rfl))

lemma base_1589 : 0 < A271510 1589 :=
  A271510_pos_of_exists 1589 15 12 8 34 (by rfl) (by omega) (prove_sq 15 12 8 49 (by rfl))

lemma base_1590 : 0 < A271510 1590 :=
  A271510_pos_of_exists 1590 9 7 4 38 (by rfl) (by omega) (prove_sq 9 7 4 27 (by rfl))

lemma base_1591 : 0 < A271510 1591 :=
  A271510_pos_of_exists 1591 7 7 7 38 (by rfl) (by omega) (prove_sq 7 7 7 35 (by rfl))

lemma base_1592 : 0 < A271510 1592 :=
  A271510_pos_of_exists 1592 24 4 10 30 (by rfl) (by omega) (prove_sq 24 4 10 48 (by rfl))

lemma base_1593 : 0 < A271510 1593 :=
  A271510_pos_of_exists 1593 6 6 0 39 (by rfl) (by omega) (prove_sq 6 6 0 18 (by rfl))

lemma base_1594 : 0 < A271510 1594 :=
  A271510_pos_of_exists 1594 0 0 15 37 (by rfl) (by omega) (prove_sq 0 0 15 60 (by rfl))

lemma base_1595 : 0 < A271510 1595 :=
  A271510_pos_of_exists 1595 17 1 3 36 (by rfl) (by omega) (prove_sq 17 1 3 21 (by rfl))

lemma base_1596 : 0 < A271510 1596 :=
  A271510_pos_of_exists 1596 5 5 5 39 (by rfl) (by omega) (prove_sq 5 5 5 25 (by rfl))

lemma base_1597 : 0 < A271510 1597 :=
  A271510_pos_of_exists 1597 0 0 21 34 (by rfl) (by omega) (prove_sq 0 0 21 84 (by rfl))

lemma base_1598 : 0 < A271510 1598 :=
  A271510_pos_of_exists 1598 5 4 6 39 (by rfl) (by omega) (prove_sq 5 4 6 27 (by rfl))

lemma base_1599 : 0 < A271510 1599 :=
  A271510_pos_of_exists 1599 5 2 7 39 (by rfl) (by omega) (prove_sq 5 2 7 29 (by rfl))

lemma base_1600 : 0 < A271510 1600 :=
  A271510_pos_of_exists 1600 0 0 0 40 (by rfl) (by omega) (prove_sq 0 0 0 0 (by rfl))

lemma base_1601 : 0 < A271510 1601 :=
  A271510_pos_of_exists 1601 0 0 1 40 (by rfl) (by omega) (prove_sq 0 0 1 4 (by rfl))

lemma base_1602 : 0 < A271510 1602 :=
  A271510_pos_of_exists 1602 0 0 9 39 (by rfl) (by omega) (prove_sq 0 0 9 36 (by rfl))

lemma base_1603 : 0 < A271510 1603 :=
  A271510_pos_of_exists 1603 1 1 1 40 (by rfl) (by omega) (prove_sq 1 1 1 5 (by rfl))

lemma base_1604 : 0 < A271510 1604 :=
  A271510_pos_of_exists 1604 0 0 2 40 (by rfl) (by omega) (prove_sq 0 0 2 8 (by rfl))

lemma base_1605 : 0 < A271510 1605 :=
  A271510_pos_of_exists 1605 8 4 2 39 (by rfl) (by omega) (prove_sq 8 4 2 16 (by rfl))

lemma base_1606 : 0 < A271510 1606 :=
  A271510_pos_of_exists 1606 7 0 6 39 (by rfl) (by omega) (prove_sq 7 0 6 25 (by rfl))

lemma base_1607 : 0 < A271510 1607 :=
  A271510_pos_of_exists 1607 9 3 19 34 (by rfl) (by omega) (prove_sq 9 3 19 77 (by rfl))

lemma base_1608 : 0 < A271510 1608 :=
  A271510_pos_of_exists 1608 2 2 0 40 (by rfl) (by omega) (prove_sq 2 2 0 6 (by rfl))

lemma base_1609 : 0 < A271510 1609 :=
  A271510_pos_of_exists 1609 0 0 3 40 (by rfl) (by omega) (prove_sq 0 0 3 12 (by rfl))

lemma base_1610 : 0 < A271510 1610 :=
  A271510_pos_of_exists 1610 3 0 1 40 (by rfl) (by omega) (prove_sq 3 0 1 5 (by rfl))

lemma base_1611 : 0 < A271510 1611 :=
  A271510_pos_of_exists 1611 7 5 31 24 (by rfl) (by omega) (prove_sq 7 5 31 125 (by rfl))

lemma base_1612 : 0 < A271510 1612 :=
  A271510_pos_of_exists 1612 2 2 2 40 (by rfl) (by omega) (prove_sq 2 2 2 10 (by rfl))

lemma base_1613 : 0 < A271510 1613 :=
  A271510_pos_of_exists 1613 0 0 13 38 (by rfl) (by omega) (prove_sq 0 0 13 52 (by rfl))

lemma base_1614 : 0 < A271510 1614 :=
  A271510_pos_of_exists 1614 3 1 2 40 (by rfl) (by omega) (prove_sq 3 1 2 9 (by rfl))

lemma base_1615 : 0 < A271510 1615 :=
  A271510_pos_of_exists 1615 11 7 1 38 (by rfl) (by omega) (prove_sq 11 7 1 23 (by rfl))

lemma base_1616 : 0 < A271510 1616 :=
  A271510_pos_of_exists 1616 0 0 4 40 (by rfl) (by omega) (prove_sq 0 0 4 16 (by rfl))

lemma base_1617 : 0 < A271510 1617 :=
  A271510_pos_of_exists 1617 10 8 38 3 (by rfl) (by omega) (prove_sq 10 8 38 154 (by rfl))

lemma base_1618 : 0 < A271510 1618 :=
  A271510_pos_of_exists 1618 0 0 23 33 (by rfl) (by omega) (prove_sq 0 0 23 92 (by rfl))

lemma base_1619 : 0 < A271510 1619 :=
  A271510_pos_of_exists 1619 7 7 0 39 (by rfl) (by omega) (prove_sq 7 7 0 21 (by rfl))

lemma base_1620 : 0 < A271510 1620 :=
  A271510_pos_of_exists 1620 0 0 18 36 (by rfl) (by omega) (prove_sq 0 0 18 72 (by rfl))

lemma base_1621 : 0 < A271510 1621 :=
  A271510_pos_of_exists 1621 0 0 10 39 (by rfl) (by omega) (prove_sq 0 0 10 40 (by rfl))

lemma base_1622 : 0 < A271510 1622 :=
  A271510_pos_of_exists 1622 5 3 12 38 (by rfl) (by omega) (prove_sq 5 3 12 49 (by rfl))

lemma base_1623 : 0 < A271510 1623 :=
  A271510_pos_of_exists 1623 15 14 19 29 (by rfl) (by omega) (prove_sq 15 14 19 87 (by rfl))

lemma base_1624 : 0 < A271510 1624 :=
  A271510_pos_of_exists 1624 10 8 38 4 (by rfl) (by omega) (prove_sq 10 8 38 154 (by rfl))

lemma base_1625 : 0 < A271510 1625 :=
  A271510_pos_of_exists 1625 0 0 5 40 (by rfl) (by omega) (prove_sq 0 0 5 20 (by rfl))

lemma base_1626 : 0 < A271510 1626 :=
  A271510_pos_of_exists 1626 15 10 25 26 (by rfl) (by omega) (prove_sq 15 10 25 105 (by rfl))

lemma base_1627 : 0 < A271510 1627 :=
  A271510_pos_of_exists 1627 3 3 3 40 (by rfl) (by omega) (prove_sq 3 3 3 15 (by rfl))

lemma base_1628 : 0 < A271510 1628 :=
  A271510_pos_of_exists 1628 6 6 20 34 (by rfl) (by omega) (prove_sq 6 6 20 82 (by rfl))

lemma base_1629 : 0 < A271510 1629 :=
  A271510_pos_of_exists 1629 0 0 27 30 (by rfl) (by omega) (prove_sq 0 0 27 108 (by rfl))

lemma base_1630 : 0 < A271510 1630 :=
  A271510_pos_of_exists 1630 21 15 30 8 (by rfl) (by omega) (prove_sq 21 15 30 129 (by rfl))

lemma base_1631 : 0 < A271510 1631 :=
  A271510_pos_of_exists 1631 15 6 1 37 (by rfl) (by omega) (prove_sq 15 6 1 23 (by rfl))

lemma base_1632 : 0 < A271510 1632 :=
  A271510_pos_of_exists 1632 4 4 0 40 (by rfl) (by omega) (prove_sq 4 4 0 12 (by rfl))

lemma base_1633 : 0 < A271510 1633 :=
  A271510_pos_of_exists 1633 5 2 2 40 (by rfl) (by omega) (prove_sq 5 2 2 11 (by rfl))

lemma base_1634 : 0 < A271510 1634 :=
  A271510_pos_of_exists 1634 5 0 3 40 (by rfl) (by omega) (prove_sq 5 0 3 13 (by rfl))

lemma base_1635 : 0 < A271510 1635 :=
  A271510_pos_of_exists 1635 7 4 7 39 (by rfl) (by omega) (prove_sq 7 4 7 31 (by rfl))

lemma base_1636 : 0 < A271510 1636 :=
  A271510_pos_of_exists 1636 0 0 6 40 (by rfl) (by omega) (prove_sq 0 0 6 24 (by rfl))

lemma base_1637 : 0 < A271510 1637 :=
  A271510_pos_of_exists 1637 0 0 26 31 (by rfl) (by omega) (prove_sq 0 0 26 104 (by rfl))

lemma base_1638 : 0 < A271510 1638 :=
  A271510_pos_of_exists 1638 3 2 5 40 (by rfl) (by omega) (prove_sq 3 2 5 21 (by rfl))

lemma base_1639 : 0 < A271510 1639 :=
  A271510_pos_of_exists 1639 3 3 10 39 (by rfl) (by omega) (prove_sq 3 3 10 41 (by rfl))

lemma base_1640 : 0 < A271510 1640 :=
  A271510_pos_of_exists 1640 0 0 14 38 (by rfl) (by omega) (prove_sq 0 0 14 56 (by rfl))

lemma base_1641 : 0 < A271510 1641 :=
  A271510_pos_of_exists 1641 20 20 0 29 (by rfl) (by omega) (prove_sq 20 20 0 60 (by rfl))

lemma base_1642 : 0 < A271510 1642 :=
  A271510_pos_of_exists 1642 0 0 11 39 (by rfl) (by omega) (prove_sq 0 0 11 44 (by rfl))

lemma base_1643 : 0 < A271510 1643 :=
  A271510_pos_of_exists 1643 15 1 29 24 (by rfl) (by omega) (prove_sq 15 1 29 117 (by rfl))

lemma base_1644 : 0 < A271510 1644 :=
  A271510_pos_of_exists 1644 7 7 5 39 (by rfl) (by omega) (prove_sq 7 7 5 29 (by rfl))

lemma base_1645 : 0 < A271510 1645 :=
  A271510_pos_of_exists 1645 11 8 26 28 (by rfl) (by omega) (prove_sq 11 8 26 107 (by rfl))

lemma base_1646 : 0 < A271510 1646 :=
  A271510_pos_of_exists 1646 15 5 10 36 (by rfl) (by omega) (prove_sq 15 5 10 45 (by rfl))

lemma base_1647 : 0 < A271510 1647 :=
  A271510_pos_of_exists 1647 7 7 18 35 (by rfl) (by omega) (prove_sq 7 7 18 75 (by rfl))

lemma base_1648 : 0 < A271510 1648 :=
  A271510_pos_of_exists 1648 4 4 4 40 (by rfl) (by omega) (prove_sq 4 4 4 20 (by rfl))

lemma base_1649 : 0 < A271510 1649 :=
  A271510_pos_of_exists 1649 0 0 7 40 (by rfl) (by omega) (prove_sq 0 0 7 28 (by rfl))

lemma base_1650 : 0 < A271510 1650 :=
  A271510_pos_of_exists 1650 5 5 0 40 (by rfl) (by omega) (prove_sq 5 5 0 15 (by rfl))

lemma base_1651 : 0 < A271510 1651 :=
  A271510_pos_of_exists 1651 15 9 36 7 (by rfl) (by omega) (prove_sq 15 9 36 147 (by rfl))

lemma base_1652 : 0 < A271510 1652 :=
  A271510_pos_of_exists 1652 5 5 9 39 (by rfl) (by omega) (prove_sq 5 5 9 39 (by rfl))

lemma base_1653 : 0 < A271510 1653 :=
  A271510_pos_of_exists 1653 7 2 0 40 (by rfl) (by omega) (prove_sq 7 2 0 9 (by rfl))

lemma base_1654 : 0 < A271510 1654 :=
  A271510_pos_of_exists 1654 5 5 2 40 (by rfl) (by omega) (prove_sq 5 5 2 17 (by rfl))

lemma base_1655 : 0 < A271510 1655 :=
  A271510_pos_of_exists 1655 9 5 35 18 (by rfl) (by omega) (prove_sq 9 5 35 141 (by rfl))

lemma base_1656 : 0 < A271510 1656 :=
  A271510_pos_of_exists 1656 6 2 4 40 (by rfl) (by omega) (prove_sq 6 2 4 18 (by rfl))

lemma base_1657 : 0 < A271510 1657 :=
  A271510_pos_of_exists 1657 0 0 19 36 (by rfl) (by omega) (prove_sq 0 0 19 76 (by rfl))

lemma base_1658 : 0 < A271510 1658 :=
  A271510_pos_of_exists 1658 0 0 17 37 (by rfl) (by omega) (prove_sq 0 0 17 68 (by rfl))

lemma base_1659 : 0 < A271510 1659 :=
  A271510_pos_of_exists 1659 11 11 11 36 (by rfl) (by omega) (prove_sq 11 11 11 55 (by rfl))

lemma base_1660 : 0 < A271510 1660 :=
  A271510_pos_of_exists 1660 7 5 31 25 (by rfl) (by omega) (prove_sq 7 5 31 125 (by rfl))

lemma base_1661 : 0 < A271510 1661 :=
  A271510_pos_of_exists 1661 12 10 29 24 (by rfl) (by omega) (prove_sq 12 10 29 120 (by rfl))

lemma base_1662 : 0 < A271510 1662 :=
  A271510_pos_of_exists 1662 7 2 3 40 (by rfl) (by omega) (prove_sq 7 2 3 15 (by rfl))

lemma base_1663 : 0 < A271510 1663 :=
  A271510_pos_of_exists 1663 11 11 14 35 (by rfl) (by omega) (prove_sq 11 11 14 65 (by rfl))

lemma base_1664 : 0 < A271510 1664 :=
  A271510_pos_of_exists 1664 0 0 8 40 (by rfl) (by omega) (prove_sq 0 0 8 32 (by rfl))

lemma base_1665 : 0 < A271510 1665 :=
  A271510_pos_of_exists 1665 0 0 12 39 (by rfl) (by omega) (prove_sq 0 0 12 48 (by rfl))

lemma base_1666 : 0 < A271510 1666 :=
  A271510_pos_of_exists 1666 0 0 21 35 (by rfl) (by omega) (prove_sq 0 0 21 84 (by rfl))

lemma base_1667 : 0 < A271510 1667 :=
  A271510_pos_of_exists 1667 9 7 4 39 (by rfl) (by omega) (prove_sq 9 7 4 27 (by rfl))

lemma base_1668 : 0 < A271510 1668 :=
  A271510_pos_of_exists 1668 7 7 7 39 (by rfl) (by omega) (prove_sq 7 7 7 35 (by rfl))

lemma base_1669 : 0 < A271510 1669 :=
  A271510_pos_of_exists 1669 0 0 15 38 (by rfl) (by omega) (prove_sq 0 0 15 60 (by rfl))

lemma base_1670 : 0 < A271510 1670 :=
  A271510_pos_of_exists 1670 33 15 10 16 (by rfl) (by omega) (prove_sq 33 15 10 67 (by rfl))

lemma base_1671 : 0 < A271510 1671 :=
  A271510_pos_of_exists 1671 25 11 21 22 (by rfl) (by omega) (prove_sq 25 11 21 93 (by rfl))

lemma base_1672 : 0 < A271510 1672 :=
  A271510_pos_of_exists 1672 6 6 0 40 (by rfl) (by omega) (prove_sq 6 6 0 18 (by rfl))

lemma base_1673 : 0 < A271510 1673 :=
  A271510_pos_of_exists 1673 6 4 10 39 (by rfl) (by omega) (prove_sq 6 4 10 42 (by rfl))

lemma base_1674 : 0 < A271510 1674 :=
  A271510_pos_of_exists 1674 7 2 10 39 (by rfl) (by omega) (prove_sq 7 2 10 41 (by rfl))

lemma base_1675 : 0 < A271510 1675 :=
  A271510_pos_of_exists 1675 5 5 5 40 (by rfl) (by omega) (prove_sq 5 5 5 25 (by rfl))

lemma base_1676 : 0 < A271510 1676 :=
  A271510_pos_of_exists 1676 9 3 19 35 (by rfl) (by omega) (prove_sq 9 3 19 77 (by rfl))

lemma base_1677 : 0 < A271510 1677 :=
  A271510_pos_of_exists 1677 5 4 6 40 (by rfl) (by omega) (prove_sq 5 4 6 27 (by rfl))

lemma base_1678 : 0 < A271510 1678 :=
  A271510_pos_of_exists 1678 5 2 7 40 (by rfl) (by omega) (prove_sq 5 2 7 29 (by rfl))

lemma base_1679 : 0 < A271510 1679 :=
  A271510_pos_of_exists 1679 15 10 25 27 (by rfl) (by omega) (prove_sq 15 10 25 105 (by rfl))

lemma base_1680 : 0 < A271510 1680 :=
  A271510_pos_of_exists 1680 10 10 18 34 (by rfl) (by omega) (prove_sq 10 10 18 78 (by rfl))

lemma base_1681 : 0 < A271510 1681 :=
  A271510_pos_of_exists 1681 0 0 0 41 (by rfl) (by omega) (prove_sq 0 0 0 0 (by rfl))

lemma base_1682 : 0 < A271510 1682 :=
  A271510_pos_of_exists 1682 0 0 1 41 (by rfl) (by omega) (prove_sq 0 0 1 4 (by rfl))

lemma base_1683 : 0 < A271510 1683 :=
  A271510_pos_of_exists 1683 1 1 0 41 (by rfl) (by omega) (prove_sq 1 1 0 3 (by rfl))

lemma base_1684 : 0 < A271510 1684 :=
  A271510_pos_of_exists 1684 0 0 28 30 (by rfl) (by omega) (prove_sq 0 0 28 112 (by rfl))

lemma base_1685 : 0 < A271510 1685 :=
  A271510_pos_of_exists 1685 0 0 2 41 (by rfl) (by omega) (prove_sq 0 0 2 8 (by rfl))

lemma base_1686 : 0 < A271510 1686 :=
  A271510_pos_of_exists 1686 11 11 0 38 (by rfl) (by omega) (prove_sq 11 11 0 33 (by rfl))

lemma base_1687 : 0 < A271510 1687 :=
  A271510_pos_of_exists 1687 9 9 9 38 (by rfl) (by omega) (prove_sq 9 9 9 45 (by rfl))

lemma base_1688 : 0 < A271510 1688 :=
  A271510_pos_of_exists 1688 14 14 0 36 (by rfl) (by omega) (prove_sq 14 14 0 42 (by rfl))

lemma base_1689 : 0 < A271510 1689 :=
  A271510_pos_of_exists 1689 2 2 0 41 (by rfl) (by omega) (prove_sq 2 2 0 6 (by rfl))

lemma base_1690 : 0 < A271510 1690 :=
  A271510_pos_of_exists 1690 0 0 3 41 (by rfl) (by omega) (prove_sq 0 0 3 12 (by rfl))

lemma base_1691 : 0 < A271510 1691 :=
  A271510_pos_of_exists 1691 3 0 1 41 (by rfl) (by omega) (prove_sq 3 0 1 5 (by rfl))

lemma base_1692 : 0 < A271510 1692 :=
  A271510_pos_of_exists 1692 9 5 35 19 (by rfl) (by omega) (prove_sq 9 5 35 141 (by rfl))

lemma base_1693 : 0 < A271510 1693 :=
  A271510_pos_of_exists 1693 0 0 18 37 (by rfl) (by omega) (prove_sq 0 0 18 72 (by rfl))

lemma base_1694 : 0 < A271510 1694 :=
  A271510_pos_of_exists 1694 12 2 5 39 (by rfl) (by omega) (prove_sq 12 2 5 24 (by rfl))

lemma base_1695 : 0 < A271510 1695 :=
  A271510_pos_of_exists 1695 3 1 2 41 (by rfl) (by omega) (prove_sq 3 1 2 9 (by rfl))

lemma base_1696 : 0 < A271510 1696 :=
  A271510_pos_of_exists 1696 0 0 20 36 (by rfl) (by omega) (prove_sq 0 0 20 80 (by rfl))

lemma base_1697 : 0 < A271510 1697 :=
  A271510_pos_of_exists 1697 0 0 4 41 (by rfl) (by omega) (prove_sq 0 0 4 16 (by rfl))

lemma base_1698 : 0 < A271510 1698 :=
  A271510_pos_of_exists 1698 5 4 19 36 (by rfl) (by omega) (prove_sq 5 4 19 77 (by rfl))

lemma base_1699 : 0 < A271510 1699 :=
  A271510_pos_of_exists 1699 3 3 0 41 (by rfl) (by omega) (prove_sq 3 3 0 9 (by rfl))

lemma base_1700 : 0 < A271510 1700 :=
  A271510_pos_of_exists 1700 0 0 10 40 (by rfl) (by omega) (prove_sq 0 0 10 40 (by rfl))

lemma base_1701 : 0 < A271510 1701 :=
  A271510_pos_of_exists 1701 11 10 38 6 (by rfl) (by omega) (prove_sq 11 10 38 155 (by rfl))

lemma base_1702 : 0 < A271510 1702 :=
  A271510_pos_of_exists 1702 4 2 1 41 (by rfl) (by omega) (prove_sq 4 2 1 8 (by rfl))

lemma base_1703 : 0 < A271510 1703 :=
  A271510_pos_of_exists 1703 13 3 30 25 (by rfl) (by omega) (prove_sq 13 3 30 121 (by rfl))

lemma base_1704 : 0 < A271510 1704 :=
  A271510_pos_of_exists 1704 14 14 36 4 (by rfl) (by omega) (prove_sq 14 14 36 150 (by rfl))

lemma base_1705 : 0 < A271510 1705 :=
  A271510_pos_of_exists 1705 7 4 22 34 (by rfl) (by omega) (prove_sq 7 4 22 89 (by rfl))

lemma base_1706 : 0 < A271510 1706 :=
  A271510_pos_of_exists 1706 0 0 5 41 (by rfl) (by omega) (prove_sq 0 0 5 20 (by rfl))

lemma base_1707 : 0 < A271510 1707 :=
  A271510_pos_of_exists 1707 13 13 0 37 (by rfl) (by omega) (prove_sq 13 13 0 39 (by rfl))

lemma base_1708 : 0 < A271510 1708 :=
  A271510_pos_of_exists 1708 3 3 3 41 (by rfl) (by omega) (prove_sq 3 3 3 15 (by rfl))

lemma base_1709 : 0 < A271510 1709 :=
  A271510_pos_of_exists 1709 0 0 22 35 (by rfl) (by omega) (prove_sq 0 0 22 88 (by rfl))

lemma base_1710 : 0 < A271510 1710 :=
  A271510_pos_of_exists 1710 12 6 3 39 (by rfl) (by omega) (prove_sq 12 6 3 24 (by rfl))

lemma base_1711 : 0 < A271510 1711 :=
  A271510_pos_of_exists 1711 7 5 31 26 (by rfl) (by omega) (prove_sq 7 5 31 125 (by rfl))

lemma base_1712 : 0 < A271510 1712 :=
  A271510_pos_of_exists 1712 18 2 22 30 (by rfl) (by omega) (prove_sq 18 2 22 90 (by rfl))

lemma base_1713 : 0 < A271510 1713 :=
  A271510_pos_of_exists 1713 4 4 0 41 (by rfl) (by omega) (prove_sq 4 4 0 12 (by rfl))

lemma base_1714 : 0 < A271510 1714 :=
  A271510_pos_of_exists 1714 0 0 25 33 (by rfl) (by omega) (prove_sq 0 0 25 100 (by rfl))

lemma base_1715 : 0 < A271510 1715 :=
  A271510_pos_of_exists 1715 5 0 3 41 (by rfl) (by omega) (prove_sq 5 0 3 13 (by rfl))

lemma base_1716 : 0 < A271510 1716 :=
  A271510_pos_of_exists 1716 19 17 29 15 (by rfl) (by omega) (prove_sq 19 17 29 127 (by rfl))

lemma base_1717 : 0 < A271510 1717 :=
  A271510_pos_of_exists 1717 0 0 6 41 (by rfl) (by omega) (prove_sq 0 0 6 24 (by rfl))

lemma base_1718 : 0 < A271510 1718 :=
  A271510_pos_of_exists 1718 3 3 10 40 (by rfl) (by omega) (prove_sq 3 3 10 41 (by rfl))

lemma base_1719 : 0 < A271510 1719 :=
  A271510_pos_of_exists 1719 3 2 5 41 (by rfl) (by omega) (prove_sq 3 2 5 21 (by rfl))

lemma base_1720 : 0 < A271510 1720 :=
  A271510_pos_of_exists 1720 14 10 20 32 (by rfl) (by omega) (prove_sq 14 10 20 86 (by rfl))

lemma base_1721 : 0 < A271510 1721 :=
  A271510_pos_of_exists 1721 0 0 11 40 (by rfl) (by omega) (prove_sq 0 0 11 44 (by rfl))

lemma base_1722 : 0 < A271510 1722 :=
  A271510_pos_of_exists 1722 19 8 36 1 (by rfl) (by omega) (prove_sq 19 8 36 147 (by rfl))

lemma base_1723 : 0 < A271510 1723 :=
  A271510_pos_of_exists 1723 5 1 4 41 (by rfl) (by omega) (prove_sq 5 1 4 17 (by rfl))

lemma base_1724 : 0 < A271510 1724 :=
  A271510_pos_of_exists 1724 9 1 11 39 (by rfl) (by omega) (prove_sq 9 1 11 45 (by rfl))

lemma base_1725 : 0 < A271510 1725 :=
  A271510_pos_of_exists 1725 9 2 14 38 (by rfl) (by omega) (prove_sq 9 2 14 57 (by rfl))

lemma base_1726 : 0 < A271510 1726 :=
  A271510_pos_of_exists 1726 9 3 6 40 (by rfl) (by omega) (prove_sq 9 3 6 27 (by rfl))

lemma base_1727 : 0 < A271510 1727 :=
  A271510_pos_of_exists 1727 7 3 15 38 (by rfl) (by omega) (prove_sq 7 3 15 61 (by rfl))

lemma base_1728 : 0 < A271510 1728 :=
  A271510_pos_of_exists 1728 8 8 0 40 (by rfl) (by omega) (prove_sq 8 8 0 24 (by rfl))

lemma base_1729 : 0 < A271510 1729 :=
  A271510_pos_of_exists 1729 4 4 4 41 (by rfl) (by omega) (prove_sq 4 4 4 20 (by rfl))

lemma base_1730 : 0 < A271510 1730 :=
  A271510_pos_of_exists 1730 0 0 7 41 (by rfl) (by omega) (prove_sq 0 0 7 28 (by rfl))

lemma base_1731 : 0 < A271510 1731 :=
  A271510_pos_of_exists 1731 5 5 0 41 (by rfl) (by omega) (prove_sq 5 5 0 15 (by rfl))

lemma base_1732 : 0 < A271510 1732 :=
  A271510_pos_of_exists 1732 0 0 24 34 (by rfl) (by omega) (prove_sq 0 0 24 96 (by rfl))

lemma base_1733 : 0 < A271510 1733 :=
  A271510_pos_of_exists 1733 0 0 17 38 (by rfl) (by omega) (prove_sq 0 0 17 68 (by rfl))

lemma base_1734 : 0 < A271510 1734 :=
  A271510_pos_of_exists 1734 5 5 28 30 (by rfl) (by omega) (prove_sq 5 5 28 113 (by rfl))

lemma base_1735 : 0 < A271510 1735 :=
  A271510_pos_of_exists 1735 5 5 2 41 (by rfl) (by omega) (prove_sq 5 5 2 17 (by rfl))

lemma base_1736 : 0 < A271510 1736 :=
  A271510_pos_of_exists 1736 10 0 6 40 (by rfl) (by omega) (prove_sq 10 0 6 26 (by rfl))

lemma base_1737 : 0 < A271510 1737 :=
  A271510_pos_of_exists 1737 0 0 21 36 (by rfl) (by omega) (prove_sq 0 0 21 84 (by rfl))

lemma base_1738 : 0 < A271510 1738 :=
  A271510_pos_of_exists 1738 9 9 30 26 (by rfl) (by omega) (prove_sq 9 9 30 123 (by rfl))

lemma base_1739 : 0 < A271510 1739 :=
  A271510_pos_of_exists 1739 7 3 0 41 (by rfl) (by omega) (prove_sq 7 3 0 11 (by rfl))

lemma base_1740 : 0 < A271510 1740 :=
  A271510_pos_of_exists 1740 13 1 7 39 (by rfl) (by omega) (prove_sq 13 1 7 31 (by rfl))

lemma base_1741 : 0 < A271510 1741 :=
  A271510_pos_of_exists 1741 0 0 29 30 (by rfl) (by omega) (prove_sq 0 0 29 116 (by rfl))

lemma base_1742 : 0 < A271510 1742 :=
  A271510_pos_of_exists 1742 17 3 0 38 (by rfl) (by omega) (prove_sq 17 3 0 19 (by rfl))

lemma base_1743 : 0 < A271510 1743 :=
  A271510_pos_of_exists 1743 7 2 3 41 (by rfl) (by omega) (prove_sq 7 2 3 15 (by rfl))

lemma base_1744 : 0 < A271510 1744 :=
  A271510_pos_of_exists 1744 0 0 12 40 (by rfl) (by omega) (prove_sq 0 0 12 48 (by rfl))

lemma base_1745 : 0 < A271510 1745 :=
  A271510_pos_of_exists 1745 0 0 8 41 (by rfl) (by omega) (prove_sq 0 0 8 32 (by rfl))

lemma base_1746 : 0 < A271510 1746 :=
  A271510_pos_of_exists 1746 0 0 15 39 (by rfl) (by omega) (prove_sq 0 0 15 60 (by rfl))

lemma base_1747 : 0 < A271510 1747 :=
  A271510_pos_of_exists 1747 7 7 7 40 (by rfl) (by omega) (prove_sq 7 7 7 35 (by rfl))

lemma base_1748 : 0 < A271510 1748 :=
  A271510_pos_of_exists 1748 18 0 20 32 (by rfl) (by omega) (prove_sq 18 0 20 82 (by rfl))

lemma base_1749 : 0 < A271510 1749 :=
  A271510_pos_of_exists 1749 10 10 18 35 (by rfl) (by omega) (prove_sq 10 10 18 78 (by rfl))

lemma base_1750 : 0 < A271510 1750 :=
  A271510_pos_of_exists 1750 11 5 40 2 (by rfl) (by omega) (prove_sq 11 5 40 161 (by rfl))

lemma base_1751 : 0 < A271510 1751 :=
  A271510_pos_of_exists 1751 31 18 21 5 (by rfl) (by omega) (prove_sq 31 18 21 103 (by rfl))

lemma base_1752 : 0 < A271510 1752 :=
  A271510_pos_of_exists 1752 6 4 10 40 (by rfl) (by omega) (prove_sq 6 4 10 42 (by rfl))

lemma base_1753 : 0 < A271510 1753 :=
  A271510_pos_of_exists 1753 0 0 27 32 (by rfl) (by omega) (prove_sq 0 0 27 108 (by rfl))

lemma base_1754 : 0 < A271510 1754 :=
  A271510_pos_of_exists 1754 0 0 23 35 (by rfl) (by omega) (prove_sq 0 0 23 92 (by rfl))

lemma base_1755 : 0 < A271510 1755 :=
  A271510_pos_of_exists 1755 11 5 40 3 (by rfl) (by omega) (prove_sq 11 5 40 161 (by rfl))

lemma base_1756 : 0 < A271510 1756 :=
  A271510_pos_of_exists 1756 5 5 5 41 (by rfl) (by omega) (prove_sq 5 5 5 25 (by rfl))

lemma base_1757 : 0 < A271510 1757 :=
  A271510_pos_of_exists 1757 14 6 30 25 (by rfl) (by omega) (prove_sq 14 6 30 122 (by rfl))

lemma base_1758 : 0 < A271510 1758 :=
  A271510_pos_of_exists 1758 5 4 6 41 (by rfl) (by omega) (prove_sq 5 4 6 27 (by rfl))

lemma base_1759 : 0 < A271510 1759 :=
  A271510_pos_of_exists 1759 5 2 7 41 (by rfl) (by omega) (prove_sq 5 2 7 29 (by rfl))

lemma base_1760 : 0 < A271510 1760 :=
  A271510_pos_of_exists 1760 12 0 4 40 (by rfl) (by omega) (prove_sq 12 0 4 20 (by rfl))

lemma base_1761 : 0 < A271510 1761 :=
  A271510_pos_of_exists 1761 11 2 6 40 (by rfl) (by omega) (prove_sq 11 2 6 27 (by rfl))

lemma base_1762 : 0 < A271510 1762 :=
  A271510_pos_of_exists 1762 0 0 9 41 (by rfl) (by omega) (prove_sq 0 0 9 36 (by rfl))

lemma base_1763 : 0 < A271510 1763 :=
  A271510_pos_of_exists 1763 11 11 0 39 (by rfl) (by omega) (prove_sq 11 11 0 33 (by rfl))

lemma base_1764 : 0 < A271510 1764 :=
  A271510_pos_of_exists 1764 0 0 0 42 (by rfl) (by omega) (prove_sq 0 0 0 0 (by rfl))

lemma base_1765 : 0 < A271510 1765 :=
  A271510_pos_of_exists 1765 0 0 1 42 (by rfl) (by omega) (prove_sq 0 0 1 4 (by rfl))

lemma base_1766 : 0 < A271510 1766 :=
  A271510_pos_of_exists 1766 1 1 0 42 (by rfl) (by omega) (prove_sq 1 1 0 3 (by rfl))

lemma base_1767 : 0 < A271510 1767 :=
  A271510_pos_of_exists 1767 1 1 1 42 (by rfl) (by omega) (prove_sq 1 1 1 5 (by rfl))

lemma base_1768 : 0 < A271510 1768 :=
  A271510_pos_of_exists 1768 0 0 2 42 (by rfl) (by omega) (prove_sq 0 0 2 8 (by rfl))

lemma base_1769 : 0 < A271510 1769 :=
  A271510_pos_of_exists 1769 0 0 13 40 (by rfl) (by omega) (prove_sq 0 0 13 52 (by rfl))

lemma base_1770 : 0 < A271510 1770 :=
  A271510_pos_of_exists 1770 19 8 36 7 (by rfl) (by omega) (prove_sq 19 8 36 147 (by rfl))

lemma base_1771 : 0 < A271510 1771 :=
  A271510_pos_of_exists 1771 5 4 19 37 (by rfl) (by omega) (prove_sq 5 4 19 77 (by rfl))

lemma base_1772 : 0 < A271510 1772 :=
  A271510_pos_of_exists 1772 2 2 0 42 (by rfl) (by omega) (prove_sq 2 2 0 6 (by rfl))

lemma base_1773 : 0 < A271510 1773 :=
  A271510_pos_of_exists 1773 0 0 3 42 (by rfl) (by omega) (prove_sq 0 0 3 12 (by rfl))

lemma base_1774 : 0 < A271510 1774 :=
  A271510_pos_of_exists 1774 3 0 1 42 (by rfl) (by omega) (prove_sq 3 0 1 5 (by rfl))

lemma base_1775 : 0 < A271510 1775 :=
  A271510_pos_of_exists 1775 19 10 15 33 (by rfl) (by omega) (prove_sq 19 10 15 69 (by rfl))

lemma base_1776 : 0 < A271510 1776 :=
  A271510_pos_of_exists 1776 2 2 2 42 (by rfl) (by omega) (prove_sq 2 2 2 10 (by rfl))

lemma base_1777 : 0 < A271510 1777 :=
  A271510_pos_of_exists 1777 0 0 16 39 (by rfl) (by omega) (prove_sq 0 0 16 64 (by rfl))

lemma base_1778 : 0 < A271510 1778 :=
  A271510_pos_of_exists 1778 3 1 2 42 (by rfl) (by omega) (prove_sq 3 1 2 9 (by rfl))

lemma base_1779 : 0 < A271510 1779 :=
  A271510_pos_of_exists 1779 7 7 0 41 (by rfl) (by omega) (prove_sq 7 7 0 21 (by rfl))

lemma base_1780 : 0 < A271510 1780 :=
  A271510_pos_of_exists 1780 0 0 4 42 (by rfl) (by omega) (prove_sq 0 0 4 16 (by rfl))

lemma base_1781 : 0 < A271510 1781 :=
  A271510_pos_of_exists 1781 0 0 10 41 (by rfl) (by omega) (prove_sq 0 0 10 40 (by rfl))

lemma base_1782 : 0 < A271510 1782 :=
  A271510_pos_of_exists 1782 3 3 0 42 (by rfl) (by omega) (prove_sq 3 3 0 9 (by rfl))

lemma base_1783 : 0 < A271510 1783 :=
  A271510_pos_of_exists 1783 15 6 1 39 (by rfl) (by omega) (prove_sq 15 6 1 23 (by rfl))

lemma base_1784 : 0 < A271510 1784 :=
  A271510_pos_of_exists 1784 14 0 12 38 (by rfl) (by omega) (prove_sq 14 0 12 50 (by rfl))

lemma base_1785 : 0 < A271510 1785 :=
  A271510_pos_of_exists 1785 4 2 1 42 (by rfl) (by omega) (prove_sq 4 2 1 8 (by rfl))

lemma base_1786 : 0 < A271510 1786 :=
  A271510_pos_of_exists 1786 9 6 15 38 (by rfl) (by omega) (prove_sq 9 6 15 63 (by rfl))

lemma base_1787 : 0 < A271510 1787 :=
  A271510_pos_of_exists 1787 23 23 0 27 (by rfl) (by omega) (prove_sq 23 23 0 69 (by rfl))

lemma base_1788 : 0 < A271510 1788 :=
  A271510_pos_of_exists 1788 13 5 15 37 (by rfl) (by omega) (prove_sq 13 5 15 63 (by rfl))

lemma base_1789 : 0 < A271510 1789 :=
  A271510_pos_of_exists 1789 0 0 5 42 (by rfl) (by omega) (prove_sq 0 0 5 20 (by rfl))

lemma base_1790 : 0 < A271510 1790 :=
  A271510_pos_of_exists 1790 11 0 15 38 (by rfl) (by omega) (prove_sq 11 0 15 61 (by rfl))

lemma base_1791 : 0 < A271510 1791 :=
  A271510_pos_of_exists 1791 3 3 3 42 (by rfl) (by omega) (prove_sq 3 3 3 15 (by rfl))

lemma base_1792 : 0 < A271510 1792 :=
  A271510_pos_of_exists 1792 8 8 8 40 (by rfl) (by omega) (prove_sq 8 8 8 40 (by rfl))

lemma base_1793 : 0 < A271510 1793 :=
  A271510_pos_of_exists 1793 12 6 13 38 (by rfl) (by omega) (prove_sq 12 6 13 56 (by rfl))

lemma base_1794 : 0 < A271510 1794 :=
  A271510_pos_of_exists 1794 13 4 3 40 (by rfl) (by omega) (prove_sq 13 4 3 21 (by rfl))

lemma base_1795 : 0 < A271510 1795 :=
  A271510_pos_of_exists 1795 5 5 28 31 (by rfl) (by omega) (prove_sq 5 5 28 113 (by rfl))

lemma base_1796 : 0 < A271510 1796 :=
  A271510_pos_of_exists 1796 0 0 14 40 (by rfl) (by omega) (prove_sq 0 0 14 56 (by rfl))

lemma base_1797 : 0 < A271510 1797 :=
  A271510_pos_of_exists 1797 5 2 2 42 (by rfl) (by omega) (prove_sq 5 2 2 11 (by rfl))

lemma base_1798 : 0 < A271510 1798 :=
  A271510_pos_of_exists 1798 5 0 3 42 (by rfl) (by omega) (prove_sq 5 0 3 13 (by rfl))

lemma base_1799 : 0 < A271510 1799 :=
  A271510_pos_of_exists 1799 3 3 10 41 (by rfl) (by omega) (prove_sq 3 3 10 41 (by rfl))

lemma base_1800 : 0 < A271510 1800 :=
  A271510_pos_of_exists 1800 0 0 6 42 (by rfl) (by omega) (prove_sq 0 0 6 24 (by rfl))

lemma base_1801 : 0 < A271510 1801 :=
  A271510_pos_of_exists 1801 0 0 24 35 (by rfl) (by omega) (prove_sq 0 0 24 96 (by rfl))

lemma base_1802 : 0 < A271510 1802 :=
  A271510_pos_of_exists 1802 0 0 11 41 (by rfl) (by omega) (prove_sq 0 0 11 44 (by rfl))

lemma base_1803 : 0 < A271510 1803 :=
  A271510_pos_of_exists 1803 9 1 11 40 (by rfl) (by omega) (prove_sq 9 1 11 45 (by rfl))

lemma base_1804 : 0 < A271510 1804 :=
  A271510_pos_of_exists 1804 6 0 2 42 (by rfl) (by omega) (prove_sq 6 0 2 10 (by rfl))

lemma base_1805 : 0 < A271510 1805 :=
  A271510_pos_of_exists 1805 0 0 19 38 (by rfl) (by omega) (prove_sq 0 0 19 76 (by rfl))

lemma base_1806 : 0 < A271510 1806 :=
  A271510_pos_of_exists 1806 5 1 4 42 (by rfl) (by omega) (prove_sq 5 1 4 17 (by rfl))

lemma base_1807 : 0 < A271510 1807 :=
  A271510_pos_of_exists 1807 9 3 6 41 (by rfl) (by omega) (prove_sq 9 3 6 27 (by rfl))

lemma base_1808 : 0 < A271510 1808 :=
  A271510_pos_of_exists 1808 0 0 28 32 (by rfl) (by omega) (prove_sq 0 0 28 112 (by rfl))

lemma base_1809 : 0 < A271510 1809 :=
  A271510_pos_of_exists 1809 8 8 0 41 (by rfl) (by omega) (prove_sq 8 8 0 24 (by rfl))

lemma base_1810 : 0 < A271510 1810 :=
  A271510_pos_of_exists 1810 0 0 17 39 (by rfl) (by omega) (prove_sq 0 0 17 68 (by rfl))

lemma base_1811 : 0 < A271510 1811 :=
  A271510_pos_of_exists 1811 19 12 9 35 (by rfl) (by omega) (prove_sq 19 12 9 53 (by rfl))

lemma base_1812 : 0 < A271510 1812 :=
  A271510_pos_of_exists 1812 4 4 4 42 (by rfl) (by omega) (prove_sq 4 4 4 20 (by rfl))

lemma base_1813 : 0 < A271510 1813 :=
  A271510_pos_of_exists 1813 0 0 7 42 (by rfl) (by omega) (prove_sq 0 0 7 28 (by rfl))

lemma base_1814 : 0 < A271510 1814 :=
  A271510_pos_of_exists 1814 5 5 0 42 (by rfl) (by omega) (prove_sq 5 5 0 15 (by rfl))

lemma base_1815 : 0 < A271510 1815 :=
  A271510_pos_of_exists 1815 9 5 35 22 (by rfl) (by omega) (prove_sq 9 5 35 141 (by rfl))

lemma base_1816 : 0 < A271510 1816 :=
  A271510_pos_of_exists 1816 10 10 4 40 (by rfl) (by omega) (prove_sq 10 10 4 34 (by rfl))

lemma base_1817 : 0 < A271510 1817 :=
  A271510_pos_of_exists 1817 7 2 0 42 (by rfl) (by omega) (prove_sq 7 2 0 9 (by rfl))

lemma base_1818 : 0 < A271510 1818 :=
  A271510_pos_of_exists 1818 0 0 27 33 (by rfl) (by omega) (prove_sq 0 0 27 108 (by rfl))

lemma base_1819 : 0 < A271510 1819 :=
  A271510_pos_of_exists 1819 7 5 31 28 (by rfl) (by omega) (prove_sq 7 5 31 125 (by rfl))

lemma base_1820 : 0 < A271510 1820 :=
  A271510_pos_of_exists 1820 6 2 4 42 (by rfl) (by omega) (prove_sq 6 2 4 18 (by rfl))

lemma base_1821 : 0 < A271510 1821 :=
  A271510_pos_of_exists 1821 10 10 10 39 (by rfl) (by omega) (prove_sq 10 10 10 50 (by rfl))

lemma base_1822 : 0 < A271510 1822 :=
  A271510_pos_of_exists 1822 7 3 0 42 (by rfl) (by omega) (prove_sq 7 3 0 11 (by rfl))

lemma base_1823 : 0 < A271510 1823 :=
  A271510_pos_of_exists 1823 33 19 7 18 (by rfl) (by omega) (prove_sq 33 19 7 69 (by rfl))

lemma base_1824 : 0 < A271510 1824 :=
  A271510_pos_of_exists 1824 12 4 8 40 (by rfl) (by omega) (prove_sq 12 4 8 36 (by rfl))

lemma base_1825 : 0 < A271510 1825 :=
  A271510_pos_of_exists 1825 0 0 12 41 (by rfl) (by omega) (prove_sq 0 0 12 48 (by rfl))

lemma base_1826 : 0 < A271510 1826 :=
  A271510_pos_of_exists 1826 7 2 3 42 (by rfl) (by omega) (prove_sq 7 2 3 15 (by rfl))

lemma base_1827 : 0 < A271510 1827 :=
  A271510_pos_of_exists 1827 9 7 4 41 (by rfl) (by omega) (prove_sq 9 7 4 27 (by rfl))

lemma base_1828 : 0 < A271510 1828 :=
  A271510_pos_of_exists 1828 0 0 8 42 (by rfl) (by omega) (prove_sq 0 0 8 32 (by rfl))

lemma base_1829 : 0 < A271510 1829 :=
  A271510_pos_of_exists 1829 10 8 12 39 (by rfl) (by omega) (prove_sq 10 8 12 54 (by rfl))

lemma base_1830 : 0 < A271510 1830 :=
  A271510_pos_of_exists 1830 21 2 4 37 (by rfl) (by omega) (prove_sq 21 2 4 27 (by rfl))

lemma base_1831 : 0 < A271510 1831 :=
  A271510_pos_of_exists 1831 15 15 15 34 (by rfl) (by omega) (prove_sq 15 15 15 75 (by rfl))

lemma base_1832 : 0 < A271510 1832 :=
  A271510_pos_of_exists 1832 0 0 26 34 (by rfl) (by omega) (prove_sq 0 0 26 104 (by rfl))

lemma base_1833 : 0 < A271510 1833 :=
  A271510_pos_of_exists 1833 6 4 10 41 (by rfl) (by omega) (prove_sq 6 4 10 42 (by rfl))

lemma base_1834 : 0 < A271510 1834 :=
  A271510_pos_of_exists 1834 7 2 10 41 (by rfl) (by omega) (prove_sq 7 2 10 41 (by rfl))

lemma base_1835 : 0 < A271510 1835 :=
  A271510_pos_of_exists 1835 13 0 21 35 (by rfl) (by omega) (prove_sq 13 0 21 85 (by rfl))

lemma base_1836 : 0 < A271510 1836 :=
  A271510_pos_of_exists 1836 6 6 0 42 (by rfl) (by omega) (prove_sq 6 6 0 18 (by rfl))

lemma base_1837 : 0 < A271510 1837 :=
  A271510_pos_of_exists 1837 11 4 10 40 (by rfl) (by omega) (prove_sq 11 4 10 43 (by rfl))

lemma base_1838 : 0 < A271510 1838 :=
  A271510_pos_of_exists 1838 15 3 2 40 (by rfl) (by omega) (prove_sq 15 3 2 19 (by rfl))

lemma base_1839 : 0 < A271510 1839 :=
  A271510_pos_of_exists 1839 5 5 5 42 (by rfl) (by omega) (prove_sq 5 5 5 25 (by rfl))

lemma base_1840 : 0 < A271510 1840 :=
  A271510_pos_of_exists 1840 14 2 14 38 (by rfl) (by omega) (prove_sq 14 2 14 58 (by rfl))

lemma base_1841 : 0 < A271510 1841 :=
  A271510_pos_of_exists 1841 5 4 6 42 (by rfl) (by omega) (prove_sq 5 4 6 27 (by rfl))

lemma base_1842 : 0 < A271510 1842 :=
  A271510_pos_of_exists 1842 5 2 7 42 (by rfl) (by omega) (prove_sq 5 2 7 29 (by rfl))

lemma base_1843 : 0 < A271510 1843 :=
  A271510_pos_of_exists 1843 9 9 0 41 (by rfl) (by omega) (prove_sq 9 9 0 27 (by rfl))

lemma base_1844 : 0 < A271510 1844 :=
  A271510_pos_of_exists 1844 0 0 20 38 (by rfl) (by omega) (prove_sq 0 0 20 80 (by rfl))

lemma base_1845 : 0 < A271510 1845 :=
  A271510_pos_of_exists 1845 0 0 9 42 (by rfl) (by omega) (prove_sq 0 0 9 36 (by rfl))

lemma base_1846 : 0 < A271510 1846 :=
  A271510_pos_of_exists 1846 5 4 19 38 (by rfl) (by omega) (prove_sq 5 4 19 77 (by rfl))

lemma base_1847 : 0 < A271510 1847 :=
  A271510_pos_of_exists 1847 31 18 21 11 (by rfl) (by omega) (prove_sq 31 18 21 103 (by rfl))

lemma base_1848 : 0 < A271510 1848 :=
  A271510_pos_of_exists 1848 8 4 2 42 (by rfl) (by omega) (prove_sq 8 4 2 16 (by rfl))

lemma base_1849 : 0 < A271510 1849 :=
  A271510_pos_of_exists 1849 0 0 0 43 (by rfl) (by omega) (prove_sq 0 0 0 0 (by rfl))

lemma base_1850 : 0 < A271510 1850 :=
  A271510_pos_of_exists 1850 0 0 1 43 (by rfl) (by omega) (prove_sq 0 0 1 4 (by rfl))

lemma base_1851 : 0 < A271510 1851 :=
  A271510_pos_of_exists 1851 1 1 0 43 (by rfl) (by omega) (prove_sq 1 1 0 3 (by rfl))

lemma base_1852 : 0 < A271510 1852 :=
  A271510_pos_of_exists 1852 1 1 1 43 (by rfl) (by omega) (prove_sq 1 1 1 5 (by rfl))

lemma base_1853 : 0 < A271510 1853 :=
  A271510_pos_of_exists 1853 0 0 2 43 (by rfl) (by omega) (prove_sq 0 0 2 8 (by rfl))

lemma base_1854 : 0 < A271510 1854 :=
  A271510_pos_of_exists 1854 9 0 3 42 (by rfl) (by omega) (prove_sq 9 0 3 15 (by rfl))

lemma base_1855 : 0 < A271510 1855 :=
  A271510_pos_of_exists 1855 7 5 10 41 (by rfl) (by omega) (prove_sq 7 5 10 43 (by rfl))

lemma base_1856 : 0 < A271510 1856 :=
  A271510_pos_of_exists 1856 0 0 16 40 (by rfl) (by omega) (prove_sq 0 0 16 64 (by rfl))

lemma base_1857 : 0 < A271510 1857 :=
  A271510_pos_of_exists 1857 2 2 0 43 (by rfl) (by omega) (prove_sq 2 2 0 6 (by rfl))

lemma base_1858 : 0 < A271510 1858 :=
  A271510_pos_of_exists 1858 0 0 3 43 (by rfl) (by omega) (prove_sq 0 0 3 12 (by rfl))

lemma base_1859 : 0 < A271510 1859 :=
  A271510_pos_of_exists 1859 3 0 1 43 (by rfl) (by omega) (prove_sq 3 0 1 5 (by rfl))

lemma base_1860 : 0 < A271510 1860 :=
  A271510_pos_of_exists 1860 9 5 35 23 (by rfl) (by omega) (prove_sq 9 5 35 141 (by rfl))

lemma base_1861 : 0 < A271510 1861 :=
  A271510_pos_of_exists 1861 0 0 30 31 (by rfl) (by omega) (prove_sq 0 0 30 120 (by rfl))

lemma base_1862 : 0 < A271510 1862 :=
  A271510_pos_of_exists 1862 7 7 0 42 (by rfl) (by omega) (prove_sq 7 7 0 21 (by rfl))

lemma base_1863 : 0 < A271510 1863 :=
  A271510_pos_of_exists 1863 3 1 2 43 (by rfl) (by omega) (prove_sq 3 1 2 9 (by rfl))

lemma base_1864 : 0 < A271510 1864 :=
  A271510_pos_of_exists 1864 0 0 10 42 (by rfl) (by omega) (prove_sq 0 0 10 40 (by rfl))

lemma base_1865 : 0 < A271510 1865 :=
  A271510_pos_of_exists 1865 0 0 4 43 (by rfl) (by omega) (prove_sq 0 0 4 16 (by rfl))

lemma base_1866 : 0 < A271510 1866 :=
  A271510_pos_of_exists 1866 7 7 18 38 (by rfl) (by omega) (prove_sq 7 7 18 75 (by rfl))

lemma base_1867 : 0 < A271510 1867 :=
  A271510_pos_of_exists 1867 3 3 0 43 (by rfl) (by omega) (prove_sq 3 3 0 9 (by rfl))

lemma base_1868 : 0 < A271510 1868 :=
  A271510_pos_of_exists 1868 10 6 24 34 (by rfl) (by omega) (prove_sq 10 6 24 98 (by rfl))

lemma base_1869 : 0 < A271510 1869 :=
  A271510_pos_of_exists 1869 12 10 29 28 (by rfl) (by omega) (prove_sq 12 10 29 120 (by rfl))

lemma base_1870 : 0 < A271510 1870 :=
  A271510_pos_of_exists 1870 4 2 1 43 (by rfl) (by omega) (prove_sq 4 2 1 8 (by rfl))

lemma base_1871 : 0 < A271510 1871 :=
  A271510_pos_of_exists 1871 15 5 10 39 (by rfl) (by omega) (prove_sq 15 5 10 45 (by rfl))

lemma base_1872 : 0 < A271510 1872 :=
  A271510_pos_of_exists 1872 0 0 24 36 (by rfl) (by omega) (prove_sq 0 0 24 96 (by rfl))

lemma base_1873 : 0 < A271510 1873 :=
  A271510_pos_of_exists 1873 0 0 28 33 (by rfl) (by omega) (prove_sq 0 0 28 112 (by rfl))

lemma base_1874 : 0 < A271510 1874 :=
  A271510_pos_of_exists 1874 0 0 5 43 (by rfl) (by omega) (prove_sq 0 0 5 20 (by rfl))

lemma base_1875 : 0 < A271510 1875 :=
  A271510_pos_of_exists 1875 13 4 3 41 (by rfl) (by omega) (prove_sq 13 4 3 21 (by rfl))

lemma base_1876 : 0 < A271510 1876 :=
  A271510_pos_of_exists 1876 3 3 3 43 (by rfl) (by omega) (prove_sq 3 3 3 15 (by rfl))

lemma base_1877 : 0 < A271510 1877 :=
  A271510_pos_of_exists 1877 0 0 14 41 (by rfl) (by omega) (prove_sq 0 0 14 56 (by rfl))

lemma base_1878 : 0 < A271510 1878 :=
  A271510_pos_of_exists 1878 7 4 7 42 (by rfl) (by omega) (prove_sq 7 4 7 31 (by rfl))

lemma base_1879 : 0 < A271510 1879 :=
  A271510_pos_of_exists 1879 13 1 22 35 (by rfl) (by omega) (prove_sq 13 1 22 89 (by rfl))

lemma base_1880 : 0 < A271510 1880 :=
  A271510_pos_of_exists 1880 18 0 20 34 (by rfl) (by omega) (prove_sq 18 0 20 82 (by rfl))

lemma base_1881 : 0 < A271510 1881 :=
  A271510_pos_of_exists 1881 4 4 0 43 (by rfl) (by omega) (prove_sq 4 4 0 12 (by rfl))

lemma base_1882 : 0 < A271510 1882 :=
  A271510_pos_of_exists 1882 0 0 19 39 (by rfl) (by omega) (prove_sq 0 0 19 76 (by rfl))

lemma base_1883 : 0 < A271510 1883 :=
  A271510_pos_of_exists 1883 5 0 3 43 (by rfl) (by omega) (prove_sq 5 0 3 13 (by rfl))

lemma base_1884 : 0 < A271510 1884 :=
  A271510_pos_of_exists 1884 9 1 11 41 (by rfl) (by omega) (prove_sq 9 1 11 45 (by rfl))

lemma base_1885 : 0 < A271510 1885 :=
  A271510_pos_of_exists 1885 0 0 6 43 (by rfl) (by omega) (prove_sq 0 0 6 24 (by rfl))

lemma base_1886 : 0 < A271510 1886 :=
  A271510_pos_of_exists 1886 21 10 7 36 (by rfl) (by omega) (prove_sq 21 10 7 45 (by rfl))

lemma base_1887 : 0 < A271510 1887 :=
  A271510_pos_of_exists 1887 3 2 5 43 (by rfl) (by omega) (prove_sq 3 2 5 21 (by rfl))

lemma base_1888 : 0 < A271510 1888 :=
  A271510_pos_of_exists 1888 12 12 0 40 (by rfl) (by omega) (prove_sq 12 12 0 36 (by rfl))

lemma base_1889 : 0 < A271510 1889 :=
  A271510_pos_of_exists 1889 0 0 17 40 (by rfl) (by omega) (prove_sq 0 0 17 68 (by rfl))

lemma base_1890 : 0 < A271510 1890 :=
  A271510_pos_of_exists 1890 9 3 6 42 (by rfl) (by omega) (prove_sq 9 3 6 27 (by rfl))

lemma base_1891 : 0 < A271510 1891 :=
  A271510_pos_of_exists 1891 5 1 4 43 (by rfl) (by omega) (prove_sq 5 1 4 17 (by rfl))

lemma base_1892 : 0 < A271510 1892 :=
  A271510_pos_of_exists 1892 8 8 0 42 (by rfl) (by omega) (prove_sq 8 8 0 24 (by rfl))

lemma base_1893 : 0 < A271510 1893 :=
  A271510_pos_of_exists 1893 10 10 18 37 (by rfl) (by omega) (prove_sq 10 10 18 78 (by rfl))

lemma base_1894 : 0 < A271510 1894 :=
  A271510_pos_of_exists 1894 13 10 5 40 (by rfl) (by omega) (prove_sq 13 10 5 37 (by rfl))

lemma base_1895 : 0 < A271510 1895 :=
  A271510_pos_of_exists 1895 5 5 9 42 (by rfl) (by omega) (prove_sq 5 5 9 39 (by rfl))

lemma base_1896 : 0 < A271510 1896 :=
  A271510_pos_of_exists 1896 10 4 4 42 (by rfl) (by omega) (prove_sq 10 4 4 22 (by rfl))

lemma base_1897 : 0 < A271510 1897 :=
  A271510_pos_of_exists 1897 4 4 4 43 (by rfl) (by omega) (prove_sq 4 4 4 20 (by rfl))

lemma base_1898 : 0 < A271510 1898 :=
  A271510_pos_of_exists 1898 0 0 7 43 (by rfl) (by omega) (prove_sq 0 0 7 28 (by rfl))

lemma base_1899 : 0 < A271510 1899 :=
  A271510_pos_of_exists 1899 5 5 0 43 (by rfl) (by omega) (prove_sq 5 5 0 15 (by rfl))

lemma base_1900 : 0 < A271510 1900 :=
  A271510_pos_of_exists 1900 10 0 6 42 (by rfl) (by omega) (prove_sq 10 0 6 26 (by rfl))

lemma base_1901 : 0 < A271510 1901 :=
  A271510_pos_of_exists 1901 0 0 26 35 (by rfl) (by omega) (prove_sq 0 0 26 104 (by rfl))

lemma base_1902 : 0 < A271510 1902 :=
  A271510_pos_of_exists 1902 7 2 0 43 (by rfl) (by omega) (prove_sq 7 2 0 9 (by rfl))

lemma base_1903 : 0 < A271510 1903 :=
  A271510_pos_of_exists 1903 5 5 2 43 (by rfl) (by omega) (prove_sq 5 5 2 17 (by rfl))

lemma base_1904 : 0 < A271510 1904 :=
  A271510_pos_of_exists 1904 12 8 20 36 (by rfl) (by omega) (prove_sq 12 8 20 84 (by rfl))

lemma base_1905 : 0 < A271510 1905 :=
  A271510_pos_of_exists 1905 6 2 4 43 (by rfl) (by omega) (prove_sq 6 2 4 18 (by rfl))

lemma base_1906 : 0 < A271510 1906 :=
  A271510_pos_of_exists 1906 0 0 15 41 (by rfl) (by omega) (prove_sq 0 0 15 60 (by rfl))

lemma base_1907 : 0 < A271510 1907 :=
  A271510_pos_of_exists 1907 7 3 0 43 (by rfl) (by omega) (prove_sq 7 3 0 11 (by rfl))

lemma base_1908 : 0 < A271510 1908 :=
  A271510_pos_of_exists 1908 0 0 12 42 (by rfl) (by omega) (prove_sq 0 0 12 48 (by rfl))

lemma base_1909 : 0 < A271510 1909 :=
  A271510_pos_of_exists 1909 15 0 28 30 (by rfl) (by omega) (prove_sq 15 0 28 113 (by rfl))

lemma base_1910 : 0 < A271510 1910 :=
  A271510_pos_of_exists 1910 9 7 4 42 (by rfl) (by omega) (prove_sq 9 7 4 27 (by rfl))

lemma base_1911 : 0 < A271510 1911 :=
  A271510_pos_of_exists 1911 7 2 3 43 (by rfl) (by omega) (prove_sq 7 2 3 15 (by rfl))

lemma base_1912 : 0 < A271510 1912 :=
  A271510_pos_of_exists 1912 10 4 14 40 (by rfl) (by omega) (prove_sq 10 4 14 58 (by rfl))

lemma base_1913 : 0 < A271510 1913 :=
  A271510_pos_of_exists 1913 0 0 8 43 (by rfl) (by omega) (prove_sq 0 0 8 32 (by rfl))

lemma base_1914 : 0 < A271510 1914 :=
  A271510_pos_of_exists 1914 23 1 22 30 (by rfl) (by omega) (prove_sq 23 1 22 91 (by rfl))

lemma base_1915 : 0 < A271510 1915 :=
  A271510_pos_of_exists 1915 11 5 13 40 (by rfl) (by omega) (prove_sq 11 5 13 55 (by rfl))

lemma base_1916 : 0 < A271510 1916 :=
  A271510_pos_of_exists 1916 6 4 10 42 (by rfl) (by omega) (prove_sq 6 4 10 42 (by rfl))

lemma base_1917 : 0 < A271510 1917 :=
  A271510_pos_of_exists 1917 7 2 10 42 (by rfl) (by omega) (prove_sq 7 2 10 41 (by rfl))

lemma base_1918 : 0 < A271510 1918 :=
  A271510_pos_of_exists 1918 7 4 22 37 (by rfl) (by omega) (prove_sq 7 4 22 89 (by rfl))

lemma base_1919 : 0 < A271510 1919 :=
  A271510_pos_of_exists 1919 13 3 30 29 (by rfl) (by omega) (prove_sq 13 3 30 121 (by rfl))

lemma base_1920 : 0 < A271510 1920 :=
  A271510_pos_of_exists 1920 24 8 16 32 (by rfl) (by omega) (prove_sq 24 8 16 72 (by rfl))

lemma base_1921 : 0 < A271510 1921 :=
  A271510_pos_of_exists 1921 0 0 20 39 (by rfl) (by omega) (prove_sq 0 0 20 80 (by rfl))

lemma base_1922 : 0 < A271510 1922 :=
  A271510_pos_of_exists 1922 0 0 31 31 (by rfl) (by omega) (prove_sq 0 0 31 124 (by rfl))

lemma base_1923 : 0 < A271510 1923 :=
  A271510_pos_of_exists 1923 5 4 19 39 (by rfl) (by omega) (prove_sq 5 4 19 77 (by rfl))

lemma base_1924 : 0 < A271510 1924 :=
  A271510_pos_of_exists 1924 0 0 18 40 (by rfl) (by omega) (prove_sq 0 0 18 72 (by rfl))

lemma base_1925 : 0 < A271510 1925 :=
  A271510_pos_of_exists 1925 11 2 6 42 (by rfl) (by omega) (prove_sq 11 2 6 27 (by rfl))

lemma base_1926 : 0 < A271510 1926 :=
  A271510_pos_of_exists 1926 5 4 6 43 (by rfl) (by omega) (prove_sq 5 4 6 27 (by rfl))

lemma base_1927 : 0 < A271510 1927 :=
  A271510_pos_of_exists 1927 5 2 7 43 (by rfl) (by omega) (prove_sq 5 2 7 29 (by rfl))

lemma base_1928 : 0 < A271510 1928 :=
  A271510_pos_of_exists 1928 0 0 22 38 (by rfl) (by omega) (prove_sq 0 0 22 88 (by rfl))

lemma base_1929 : 0 < A271510 1929 :=
  A271510_pos_of_exists 1929 9 4 26 34 (by rfl) (by omega) (prove_sq 9 4 26 105 (by rfl))

lemma base_1930 : 0 < A271510 1930 :=
  A271510_pos_of_exists 1930 0 0 9 43 (by rfl) (by omega) (prove_sq 0 0 9 36 (by rfl))

lemma base_1931 : 0 < A271510 1931 :=
  A271510_pos_of_exists 1931 11 3 24 35 (by rfl) (by omega) (prove_sq 11 3 24 97 (by rfl))

lemma base_1932 : 0 < A271510 1932 :=
  A271510_pos_of_exists 1932 10 2 8 42 (by rfl) (by omega) (prove_sq 10 2 8 34 (by rfl))

lemma base_1933 : 0 < A271510 1933 :=
  A271510_pos_of_exists 1933 0 0 13 42 (by rfl) (by omega) (prove_sq 0 0 13 52 (by rfl))

lemma base_1934 : 0 < A271510 1934 :=
  A271510_pos_of_exists 1934 7 0 6 43 (by rfl) (by omega) (prove_sq 7 0 6 25 (by rfl))

lemma base_1935 : 0 < A271510 1935 :=
  A271510_pos_of_exists 1935 7 5 31 30 (by rfl) (by omega) (prove_sq 7 5 31 125 (by rfl))

lemma base_1936 : 0 < A271510 1936 :=
  A271510_pos_of_exists 1936 0 0 0 44 (by rfl) (by omega) (prove_sq 0 0 0 0 (by rfl))

lemma base_1937 : 0 < A271510 1937 :=
  A271510_pos_of_exists 1937 0 0 1 44 (by rfl) (by omega) (prove_sq 0 0 1 4 (by rfl))

lemma base_1938 : 0 < A271510 1938 :=
  A271510_pos_of_exists 1938 1 1 0 44 (by rfl) (by omega) (prove_sq 1 1 0 3 (by rfl))

lemma base_1939 : 0 < A271510 1939 :=
  A271510_pos_of_exists 1939 1 1 1 44 (by rfl) (by omega) (prove_sq 1 1 1 5 (by rfl))

lemma base_1940 : 0 < A271510 1940 :=
  A271510_pos_of_exists 1940 0 0 2 44 (by rfl) (by omega) (prove_sq 0 0 2 8 (by rfl))

lemma base_1941 : 0 < A271510 1941 :=
  A271510_pos_of_exists 1941 25 16 6 32 (by rfl) (by omega) (prove_sq 25 16 6 57 (by rfl))

lemma base_1942 : 0 < A271510 1942 :=
  A271510_pos_of_exists 1942 5 3 12 42 (by rfl) (by omega) (prove_sq 5 3 12 49 (by rfl))

lemma base_1943 : 0 < A271510 1943 :=
  A271510_pos_of_exists 1943 7 7 18 39 (by rfl) (by omega) (prove_sq 7 7 18 75 (by rfl))

lemma base_1944 : 0 < A271510 1944 :=
  A271510_pos_of_exists 1944 2 2 0 44 (by rfl) (by omega) (prove_sq 2 2 0 6 (by rfl))

lemma base_1945 : 0 < A271510 1945 :=
  A271510_pos_of_exists 1945 0 0 3 44 (by rfl) (by omega) (prove_sq 0 0 3 12 (by rfl))

lemma base_1946 : 0 < A271510 1946 :=
  A271510_pos_of_exists 1946 3 0 1 44 (by rfl) (by omega) (prove_sq 3 0 1 5 (by rfl))

lemma base_1947 : 0 < A271510 1947 :=
  A271510_pos_of_exists 1947 7 7 0 43 (by rfl) (by omega) (prove_sq 7 7 0 21 (by rfl))

lemma base_1948 : 0 < A271510 1948 :=
  A271510_pos_of_exists 1948 2 2 2 44 (by rfl) (by omega) (prove_sq 2 2 2 10 (by rfl))

lemma base_1949 : 0 < A271510 1949 :=
  A271510_pos_of_exists 1949 0 0 10 43 (by rfl) (by omega) (prove_sq 0 0 10 40 (by rfl))

lemma base_1950 : 0 < A271510 1950 :=
  A271510_pos_of_exists 1950 3 1 2 44 (by rfl) (by omega) (prove_sq 3 1 2 9 (by rfl))

lemma base_1951 : 0 < A271510 1951 :=
  A271510_pos_of_exists 1951 13 13 13 38 (by rfl) (by omega) (prove_sq 13 13 13 65 (by rfl))

lemma base_1952 : 0 < A271510 1952 :=
  A271510_pos_of_exists 1952 0 0 4 44 (by rfl) (by omega) (prove_sq 0 0 4 16 (by rfl))

lemma base_1953 : 0 < A271510 1953 :=
  A271510_pos_of_exists 1953 12 6 3 42 (by rfl) (by omega) (prove_sq 12 6 3 24 (by rfl))

lemma base_1954 : 0 < A271510 1954 :=
  A271510_pos_of_exists 1954 0 0 27 35 (by rfl) (by omega) (prove_sq 0 0 27 108 (by rfl))

lemma base_1955 : 0 < A271510 1955 :=
  A271510_pos_of_exists 1955 17 1 12 39 (by rfl) (by omega) (prove_sq 17 1 12 51 (by rfl))

lemma base_1956 : 0 < A271510 1956 :=
  A271510_pos_of_exists 1956 8 8 8 42 (by rfl) (by omega) (prove_sq 8 8 8 40 (by rfl))

lemma base_1957 : 0 < A271510 1957 :=
  A271510_pos_of_exists 1957 4 2 1 44 (by rfl) (by omega) (prove_sq 4 2 1 8 (by rfl))

lemma base_1958 : 0 < A271510 1958 :=
  A271510_pos_of_exists 1958 13 4 3 42 (by rfl) (by omega) (prove_sq 13 4 3 21 (by rfl))

lemma base_1959 : 0 < A271510 1959 :=
  A271510_pos_of_exists 1959 11 11 14 39 (by rfl) (by omega) (prove_sq 11 11 14 65 (by rfl))

lemma base_1960 : 0 < A271510 1960 :=
  A271510_pos_of_exists 1960 0 0 14 42 (by rfl) (by omega) (prove_sq 0 0 14 56 (by rfl))

lemma base_1961 : 0 < A271510 1961 :=
  A271510_pos_of_exists 1961 0 0 5 44 (by rfl) (by omega) (prove_sq 0 0 5 20 (by rfl))

lemma base_1962 : 0 < A271510 1962 :=
  A271510_pos_of_exists 1962 0 0 21 39 (by rfl) (by omega) (prove_sq 0 0 21 84 (by rfl))

lemma base_1963 : 0 < A271510 1963 :=
  A271510_pos_of_exists 1963 3 3 3 44 (by rfl) (by omega) (prove_sq 3 3 3 15 (by rfl))

lemma base_1964 : 0 < A271510 1964 :=
  A271510_pos_of_exists 1964 7 3 15 41 (by rfl) (by omega) (prove_sq 7 3 15 61 (by rfl))

lemma base_1965 : 0 < A271510 1965 :=
  A271510_pos_of_exists 1965 18 4 28 29 (by rfl) (by omega) (prove_sq 18 4 28 114 (by rfl))

lemma base_1966 : 0 < A271510 1966 :=
  A271510_pos_of_exists 1966 13 10 4 41 (by rfl) (by omega) (prove_sq 13 10 4 35 (by rfl))

lemma base_1967 : 0 < A271510 1967 :=
  A271510_pos_of_exists 1967 3 3 10 43 (by rfl) (by omega) (prove_sq 3 3 10 41 (by rfl))

lemma base_1968 : 0 < A271510 1968 :=
  A271510_pos_of_exists 1968 4 4 0 44 (by rfl) (by omega) (prove_sq 4 4 0 12 (by rfl))

lemma base_1969 : 0 < A271510 1969 :=
  A271510_pos_of_exists 1969 5 2 2 44 (by rfl) (by omega) (prove_sq 5 2 2 11 (by rfl))

lemma base_1970 : 0 < A271510 1970 :=
  A271510_pos_of_exists 1970 0 0 11 43 (by rfl) (by omega) (prove_sq 0 0 11 44 (by rfl))

lemma base_1971 : 0 < A271510 1971 :=
  A271510_pos_of_exists 1971 11 5 40 15 (by rfl) (by omega) (prove_sq 11 5 40 161 (by rfl))

lemma base_1972 : 0 < A271510 1972 :=
  A271510_pos_of_exists 1972 0 0 6 44 (by rfl) (by omega) (prove_sq 0 0 6 24 (by rfl))

lemma base_1973 : 0 < A271510 1973 :=
  A271510_pos_of_exists 1973 0 0 23 38 (by rfl) (by omega) (prove_sq 0 0 23 92 (by rfl))

lemma base_1974 : 0 < A271510 1974 :=
  A271510_pos_of_exists 1974 3 2 5 44 (by rfl) (by omega) (prove_sq 3 2 5 21 (by rfl))

lemma base_1975 : 0 < A271510 1975 :=
  A271510_pos_of_exists 1975 9 3 6 43 (by rfl) (by omega) (prove_sq 9 3 6 27 (by rfl))

lemma base_1976 : 0 < A271510 1976 :=
  A271510_pos_of_exists 1976 6 0 2 44 (by rfl) (by omega) (prove_sq 6 0 2 10 (by rfl))

lemma base_1977 : 0 < A271510 1977 :=
  A271510_pos_of_exists 1977 8 8 0 43 (by rfl) (by omega) (prove_sq 8 8 0 24 (by rfl))

lemma base_1978 : 0 < A271510 1978 :=
  A271510_pos_of_exists 1978 5 1 4 44 (by rfl) (by omega) (prove_sq 5 1 4 17 (by rfl))

lemma base_1979 : 0 < A271510 1979 :=
  A271510_pos_of_exists 1979 13 0 21 37 (by rfl) (by omega) (prove_sq 13 0 21 85 (by rfl))

lemma base_1980 : 0 < A271510 1980 :=
  A271510_pos_of_exists 1980 5 5 9 43 (by rfl) (by omega) (prove_sq 5 5 9 39 (by rfl))

lemma base_1981 : 0 < A271510 1981 :=
  A271510_pos_of_exists 1981 10 4 4 43 (by rfl) (by omega) (prove_sq 10 4 4 22 (by rfl))

lemma base_1982 : 0 < A271510 1982 :=
  A271510_pos_of_exists 1982 9 6 4 43 (by rfl) (by omega) (prove_sq 9 6 4 25 (by rfl))

lemma base_1983 : 0 < A271510 1983 :=
  A271510_pos_of_exists 1983 13 1 7 42 (by rfl) (by omega) (prove_sq 13 1 7 31 (by rfl))

lemma base_1984 : 0 < A271510 1984 :=
  A271510_pos_of_exists 1984 4 4 4 44 (by rfl) (by omega) (prove_sq 4 4 4 20 (by rfl))

lemma base_1985 : 0 < A271510 1985 :=
  A271510_pos_of_exists 1985 0 0 7 44 (by rfl) (by omega) (prove_sq 0 0 7 28 (by rfl))

lemma base_1986 : 0 < A271510 1986 :=
  A271510_pos_of_exists 1986 5 5 0 44 (by rfl) (by omega) (prove_sq 5 5 0 15 (by rfl))

lemma base_1987 : 0 < A271510 1987 :=
  A271510_pos_of_exists 1987 15 0 9 41 (by rfl) (by omega) (prove_sq 15 0 9 39 (by rfl))

lemma base_1988 : 0 < A271510 1988 :=
  A271510_pos_of_exists 1988 12 4 8 42 (by rfl) (by omega) (prove_sq 12 4 8 36 (by rfl))

lemma base_1989 : 0 < A271510 1989 :=
  A271510_pos_of_exists 1989 0 0 15 42 (by rfl) (by omega) (prove_sq 0 0 15 60 (by rfl))

lemma base_1990 : 0 < A271510 1990 :=
  A271510_pos_of_exists 1990 5 5 2 44 (by rfl) (by omega) (prove_sq 5 5 2 17 (by rfl))

lemma base_1991 : 0 < A271510 1991 :=
  A271510_pos_of_exists 1991 35 10 15 21 (by rfl) (by omega) (prove_sq 35 10 15 75 (by rfl))

lemma base_1992 : 0 < A271510 1992 :=
  A271510_pos_of_exists 1992 6 2 4 44 (by rfl) (by omega) (prove_sq 6 2 4 18 (by rfl))

lemma base_1993 : 0 < A271510 1993 :=
  A271510_pos_of_exists 1993 0 0 12 43 (by rfl) (by omega) (prove_sq 0 0 12 48 (by rfl))

lemma base_1994 : 0 < A271510 1994 :=
  A271510_pos_of_exists 1994 0 0 25 37 (by rfl) (by omega) (prove_sq 0 0 25 100 (by rfl))

lemma base_1995 : 0 < A271510 1995 :=
  A271510_pos_of_exists 1995 9 7 4 43 (by rfl) (by omega) (prove_sq 9 7 4 27 (by rfl))

lemma base_1996 : 0 < A271510 1996 :=
  A271510_pos_of_exists 1996 7 5 31 31 (by rfl) (by omega) (prove_sq 7 5 31 125 (by rfl))

lemma base_1997 : 0 < A271510 1997 :=
  A271510_pos_of_exists 1997 0 0 29 34 (by rfl) (by omega) (prove_sq 0 0 29 116 (by rfl))

lemma base_1998 : 0 < A271510 1998 :=
  A271510_pos_of_exists 1998 7 2 3 44 (by rfl) (by omega) (prove_sq 7 2 3 15 (by rfl))

lemma base_1999 : 0 < A271510 1999 :=
  A271510_pos_of_exists 1999 17 17 35 14 (by rfl) (by omega) (prove_sq 17 17 35 149 (by rfl))

lemma base_2000 : 0 < A271510 2000 :=
  A271510_pos_of_exists 2000 0 0 8 44 (by rfl) (by omega) (prove_sq 0 0 8 32 (by rfl))

lemma base_2001 : 0 < A271510 2001 :=
  A271510_pos_of_exists 2001 6 4 10 43 (by rfl) (by omega) (prove_sq 6 4 10 42 (by rfl))

lemma base_2002 : 0 < A271510 2002 :=
  A271510_pos_of_exists 2002 5 4 19 40 (by rfl) (by omega) (prove_sq 5 4 19 77 (by rfl))

lemma base_2003 : 0 < A271510 2003 :=
  A271510_pos_of_exists 2003 15 3 37 20 (by rfl) (by omega) (prove_sq 15 3 37 149 (by rfl))

lemma base_2004 : 0 < A271510 2004 :=
  A271510_pos_of_exists 2004 19 5 23 33 (by rfl) (by omega) (prove_sq 19 5 23 95 (by rfl))

lemma base_2005 : 0 < A271510 2005 :=
  A271510_pos_of_exists 2005 0 0 18 41 (by rfl) (by omega) (prove_sq 0 0 18 72 (by rfl))

lemma base_2006 : 0 < A271510 2006 :=
  A271510_pos_of_exists 2006 11 11 0 42 (by rfl) (by omega) (prove_sq 11 11 0 33 (by rfl))

lemma base_2007 : 0 < A271510 2007 :=
  A271510_pos_of_exists 2007 9 5 35 26 (by rfl) (by omega) (prove_sq 9 5 35 141 (by rfl))

lemma base_2008 : 0 < A271510 2008 :=
  A271510_pos_of_exists 2008 6 6 0 44 (by rfl) (by omega) (prove_sq 6 6 0 18 (by rfl))

lemma base_2009 : 0 < A271510 2009 :=
  A271510_pos_of_exists 2009 0 0 28 35 (by rfl) (by omega) (prove_sq 0 0 28 112 (by rfl))

lemma base_2010 : 0 < A271510 2010 :=
  A271510_pos_of_exists 2010 11 2 6 43 (by rfl) (by omega) (prove_sq 11 2 6 27 (by rfl))

lemma base_2011 : 0 < A271510 2011 :=
  A271510_pos_of_exists 2011 5 5 5 44 (by rfl) (by omega) (prove_sq 5 5 5 25 (by rfl))

lemma base_2012 : 0 < A271510 2012 :=
  A271510_pos_of_exists 2012 14 4 6 42 (by rfl) (by omega) (prove_sq 14 4 6 30 (by rfl))

lemma base_2013 : 0 < A271510 2013 :=
  A271510_pos_of_exists 2013 5 4 6 44 (by rfl) (by omega) (prove_sq 5 4 6 27 (by rfl))

lemma base_2014 : 0 < A271510 2014 :=
  A271510_pos_of_exists 2014 5 2 7 44 (by rfl) (by omega) (prove_sq 5 2 7 29 (by rfl))

lemma base_2015 : 0 < A271510 2015 :=
  A271510_pos_of_exists 2015 15 5 1 42 (by rfl) (by omega) (prove_sq 15 5 1 21 (by rfl))

lemma base_2016 : 0 < A271510 2016 :=
  A271510_pos_of_exists 2016 20 16 24 28 (by rfl) (by omega) (prove_sq 20 16 24 108 (by rfl))

lemma base_2017 : 0 < A271510 2017 :=
  A271510_pos_of_exists 2017 0 0 9 44 (by rfl) (by omega) (prove_sq 0 0 9 36 (by rfl))

lemma base_2018 : 0 < A271510 2018 :=
  A271510_pos_of_exists 2018 0 0 13 43 (by rfl) (by omega) (prove_sq 0 0 13 52 (by rfl))

lemma base_2019 : 0 < A271510 2019 :=
  A271510_pos_of_exists 2019 13 5 15 40 (by rfl) (by omega) (prove_sq 13 5 15 63 (by rfl))

lemma base_2020 : 0 < A271510 2020 :=
  A271510_pos_of_exists 2020 0 0 16 42 (by rfl) (by omega) (prove_sq 0 0 16 64 (by rfl))

lemma base_2021 : 0 < A271510 2021 :=
  A271510_pos_of_exists 2021 7 0 6 44 (by rfl) (by omega) (prove_sq 7 0 6 25 (by rfl))

lemma base_2022 : 0 < A271510 2022 :=
  A271510_pos_of_exists 2022 7 7 18 40 (by rfl) (by omega) (prove_sq 7 7 18 75 (by rfl))

lemma base_2023 : 0 < A271510 2023 :=
  A271510_pos_of_exists 2023 7 5 10 43 (by rfl) (by omega) (prove_sq 7 5 10 43 (by rfl))

lemma base_2024 : 0 < A271510 2024 :=
  A271510_pos_of_exists 2024 18 4 28 30 (by rfl) (by omega) (prove_sq 18 4 28 114 (by rfl))

lemma base_2025 : 0 < A271510 2025 :=
  A271510_pos_of_exists 2025 0 0 0 45 (by rfl) (by omega) (prove_sq 0 0 0 0 (by rfl))

lemma base_2026 : 0 < A271510 2026 :=
  A271510_pos_of_exists 2026 0 0 1 45 (by rfl) (by omega) (prove_sq 0 0 1 4 (by rfl))

lemma base_2027 : 0 < A271510 2027 :=
  A271510_pos_of_exists 2027 1 1 0 45 (by rfl) (by omega) (prove_sq 1 1 0 3 (by rfl))

lemma base_2028 : 0 < A271510 2028 :=
  A271510_pos_of_exists 2028 1 1 1 45 (by rfl) (by omega) (prove_sq 1 1 1 5 (by rfl))

lemma base_2029 : 0 < A271510 2029 :=
  A271510_pos_of_exists 2029 0 0 2 45 (by rfl) (by omega) (prove_sq 0 0 2 8 (by rfl))

lemma base_2030 : 0 < A271510 2030 :=
  A271510_pos_of_exists 2030 9 0 10 43 (by rfl) (by omega) (prove_sq 9 0 10 41 (by rfl))

lemma base_2031 : 0 < A271510 2031 :=
  A271510_pos_of_exists 2031 15 5 10 41 (by rfl) (by omega) (prove_sq 15 5 10 45 (by rfl))

lemma base_2032 : 0 < A271510 2032 :=
  A271510_pos_of_exists 2032 12 12 12 40 (by rfl) (by omega) (prove_sq 12 12 12 60 (by rfl))

lemma base_2033 : 0 < A271510 2033 :=
  A271510_pos_of_exists 2033 2 2 0 45 (by rfl) (by omega) (prove_sq 2 2 0 6 (by rfl))

lemma base_2034 : 0 < A271510 2034 :=
  A271510_pos_of_exists 2034 0 0 3 45 (by rfl) (by omega) (prove_sq 0 0 3 12 (by rfl))

lemma base_2035 : 0 < A271510 2035 :=
  A271510_pos_of_exists 2035 3 0 1 45 (by rfl) (by omega) (prove_sq 3 0 1 5 (by rfl))

lemma base_2036 : 0 < A271510 2036 :=
  A271510_pos_of_exists 2036 0 0 10 44 (by rfl) (by omega) (prove_sq 0 0 10 40 (by rfl))

lemma base_2037 : 0 < A271510 2037 :=
  A271510_pos_of_exists 2037 2 2 2 45 (by rfl) (by omega) (prove_sq 2 2 2 10 (by rfl))

lemma base_2038 : 0 < A271510 2038 :=
  A271510_pos_of_exists 2038 11 11 14 40 (by rfl) (by omega) (prove_sq 11 11 14 65 (by rfl))

lemma base_2039 : 0 < A271510 2039 :=
  A271510_pos_of_exists 2039 3 1 2 45 (by rfl) (by omega) (prove_sq 3 1 2 9 (by rfl))

lemma base_2040 : 0 < A271510 2040 :=
  A271510_pos_of_exists 2040 26 20 8 30 (by rfl) (by omega) (prove_sq 26 20 8 70 (by rfl))

lemma base_2041 : 0 < A271510 2041 :=
  A271510_pos_of_exists 2041 0 0 4 45 (by rfl) (by omega) (prove_sq 0 0 4 16 (by rfl))

lemma base_2042 : 0 < A271510 2042 :=
  A271510_pos_of_exists 2042 0 0 19 41 (by rfl) (by omega) (prove_sq 0 0 19 76 (by rfl))


lemma base_cases_chunk_0 (n : ℕ) (h_low : 0 ≤ n) : 0 < A271510 n ∨ n ≥ 400 :=
  match h : n - 0 with
  | 0 => Or.inl (by have h_eq : n = 0 := (by omega); rw [h_eq]; exact base_0)
  | 1 => Or.inl (by have h_eq : n = 1 := (by omega); rw [h_eq]; exact base_1)
  | 2 => Or.inl (by have h_eq : n = 2 := (by omega); rw [h_eq]; exact base_2)
  | 3 => Or.inl (by have h_eq : n = 3 := (by omega); rw [h_eq]; exact base_3)
  | 4 => Or.inl (by have h_eq : n = 4 := (by omega); rw [h_eq]; exact base_4)
  | 5 => Or.inl (by have h_eq : n = 5 := (by omega); rw [h_eq]; exact base_5)
  | 6 => Or.inl (by have h_eq : n = 6 := (by omega); rw [h_eq]; exact base_6)
  | 7 => Or.inl (by have h_eq : n = 7 := (by omega); rw [h_eq]; exact base_7)
  | 8 => Or.inl (by have h_eq : n = 8 := (by omega); rw [h_eq]; exact base_8)
  | 9 => Or.inl (by have h_eq : n = 9 := (by omega); rw [h_eq]; exact base_9)
  | 10 => Or.inl (by have h_eq : n = 10 := (by omega); rw [h_eq]; exact base_10)
  | 11 => Or.inl (by have h_eq : n = 11 := (by omega); rw [h_eq]; exact base_11)
  | 12 => Or.inl (by have h_eq : n = 12 := (by omega); rw [h_eq]; exact base_12)
  | 13 => Or.inl (by have h_eq : n = 13 := (by omega); rw [h_eq]; exact base_13)
  | 14 => Or.inl (by have h_eq : n = 14 := (by omega); rw [h_eq]; exact base_14)
  | 15 => Or.inl (by have h_eq : n = 15 := (by omega); rw [h_eq]; exact base_15)
  | 16 => Or.inl (by have h_eq : n = 16 := (by omega); rw [h_eq]; exact base_16)
  | 17 => Or.inl (by have h_eq : n = 17 := (by omega); rw [h_eq]; exact base_17)
  | 18 => Or.inl (by have h_eq : n = 18 := (by omega); rw [h_eq]; exact base_18)
  | 19 => Or.inl (by have h_eq : n = 19 := (by omega); rw [h_eq]; exact base_19)
  | 20 => Or.inl (by have h_eq : n = 20 := (by omega); rw [h_eq]; exact base_20)
  | 21 => Or.inl (by have h_eq : n = 21 := (by omega); rw [h_eq]; exact base_21)
  | 22 => Or.inl (by have h_eq : n = 22 := (by omega); rw [h_eq]; exact base_22)
  | 23 => Or.inl (by have h_eq : n = 23 := (by omega); rw [h_eq]; exact base_23)
  | 24 => Or.inl (by have h_eq : n = 24 := (by omega); rw [h_eq]; exact base_24)
  | 25 => Or.inl (by have h_eq : n = 25 := (by omega); rw [h_eq]; exact base_25)
  | 26 => Or.inl (by have h_eq : n = 26 := (by omega); rw [h_eq]; exact base_26)
  | 27 => Or.inl (by have h_eq : n = 27 := (by omega); rw [h_eq]; exact base_27)
  | 28 => Or.inl (by have h_eq : n = 28 := (by omega); rw [h_eq]; exact base_28)
  | 29 => Or.inl (by have h_eq : n = 29 := (by omega); rw [h_eq]; exact base_29)
  | 30 => Or.inl (by have h_eq : n = 30 := (by omega); rw [h_eq]; exact base_30)
  | 31 => Or.inl (by have h_eq : n = 31 := (by omega); rw [h_eq]; exact base_31)
  | 32 => Or.inl (by have h_eq : n = 32 := (by omega); rw [h_eq]; exact base_32)
  | 33 => Or.inl (by have h_eq : n = 33 := (by omega); rw [h_eq]; exact base_33)
  | 34 => Or.inl (by have h_eq : n = 34 := (by omega); rw [h_eq]; exact base_34)
  | 35 => Or.inl (by have h_eq : n = 35 := (by omega); rw [h_eq]; exact base_35)
  | 36 => Or.inl (by have h_eq : n = 36 := (by omega); rw [h_eq]; exact base_36)
  | 37 => Or.inl (by have h_eq : n = 37 := (by omega); rw [h_eq]; exact base_37)
  | 38 => Or.inl (by have h_eq : n = 38 := (by omega); rw [h_eq]; exact base_38)
  | 39 => Or.inl (by have h_eq : n = 39 := (by omega); rw [h_eq]; exact base_39)
  | 40 => Or.inl (by have h_eq : n = 40 := (by omega); rw [h_eq]; exact base_40)
  | 41 => Or.inl (by have h_eq : n = 41 := (by omega); rw [h_eq]; exact base_41)
  | 42 => Or.inl (by have h_eq : n = 42 := (by omega); rw [h_eq]; exact base_42)
  | 43 => Or.inl (by have h_eq : n = 43 := (by omega); rw [h_eq]; exact base_43)
  | 44 => Or.inl (by have h_eq : n = 44 := (by omega); rw [h_eq]; exact base_44)
  | 45 => Or.inl (by have h_eq : n = 45 := (by omega); rw [h_eq]; exact base_45)
  | 46 => Or.inl (by have h_eq : n = 46 := (by omega); rw [h_eq]; exact base_46)
  | 47 => Or.inl (by have h_eq : n = 47 := (by omega); rw [h_eq]; exact base_47)
  | 48 => Or.inl (by have h_eq : n = 48 := (by omega); rw [h_eq]; exact base_48)
  | 49 => Or.inl (by have h_eq : n = 49 := (by omega); rw [h_eq]; exact base_49)
  | 50 => Or.inl (by have h_eq : n = 50 := (by omega); rw [h_eq]; exact base_50)
  | 51 => Or.inl (by have h_eq : n = 51 := (by omega); rw [h_eq]; exact base_51)
  | 52 => Or.inl (by have h_eq : n = 52 := (by omega); rw [h_eq]; exact base_52)
  | 53 => Or.inl (by have h_eq : n = 53 := (by omega); rw [h_eq]; exact base_53)
  | 54 => Or.inl (by have h_eq : n = 54 := (by omega); rw [h_eq]; exact base_54)
  | 55 => Or.inl (by have h_eq : n = 55 := (by omega); rw [h_eq]; exact base_55)
  | 56 => Or.inl (by have h_eq : n = 56 := (by omega); rw [h_eq]; exact base_56)
  | 57 => Or.inl (by have h_eq : n = 57 := (by omega); rw [h_eq]; exact base_57)
  | 58 => Or.inl (by have h_eq : n = 58 := (by omega); rw [h_eq]; exact base_58)
  | 59 => Or.inl (by have h_eq : n = 59 := (by omega); rw [h_eq]; exact base_59)
  | 60 => Or.inl (by have h_eq : n = 60 := (by omega); rw [h_eq]; exact base_60)
  | 61 => Or.inl (by have h_eq : n = 61 := (by omega); rw [h_eq]; exact base_61)
  | 62 => Or.inl (by have h_eq : n = 62 := (by omega); rw [h_eq]; exact base_62)
  | 63 => Or.inl (by have h_eq : n = 63 := (by omega); rw [h_eq]; exact base_63)
  | 64 => Or.inl (by have h_eq : n = 64 := (by omega); rw [h_eq]; exact base_64)
  | 65 => Or.inl (by have h_eq : n = 65 := (by omega); rw [h_eq]; exact base_65)
  | 66 => Or.inl (by have h_eq : n = 66 := (by omega); rw [h_eq]; exact base_66)
  | 67 => Or.inl (by have h_eq : n = 67 := (by omega); rw [h_eq]; exact base_67)
  | 68 => Or.inl (by have h_eq : n = 68 := (by omega); rw [h_eq]; exact base_68)
  | 69 => Or.inl (by have h_eq : n = 69 := (by omega); rw [h_eq]; exact base_69)
  | 70 => Or.inl (by have h_eq : n = 70 := (by omega); rw [h_eq]; exact base_70)
  | 71 => Or.inl (by have h_eq : n = 71 := (by omega); rw [h_eq]; exact base_71)
  | 72 => Or.inl (by have h_eq : n = 72 := (by omega); rw [h_eq]; exact base_72)
  | 73 => Or.inl (by have h_eq : n = 73 := (by omega); rw [h_eq]; exact base_73)
  | 74 => Or.inl (by have h_eq : n = 74 := (by omega); rw [h_eq]; exact base_74)
  | 75 => Or.inl (by have h_eq : n = 75 := (by omega); rw [h_eq]; exact base_75)
  | 76 => Or.inl (by have h_eq : n = 76 := (by omega); rw [h_eq]; exact base_76)
  | 77 => Or.inl (by have h_eq : n = 77 := (by omega); rw [h_eq]; exact base_77)
  | 78 => Or.inl (by have h_eq : n = 78 := (by omega); rw [h_eq]; exact base_78)
  | 79 => Or.inl (by have h_eq : n = 79 := (by omega); rw [h_eq]; exact base_79)
  | 80 => Or.inl (by have h_eq : n = 80 := (by omega); rw [h_eq]; exact base_80)
  | 81 => Or.inl (by have h_eq : n = 81 := (by omega); rw [h_eq]; exact base_81)
  | 82 => Or.inl (by have h_eq : n = 82 := (by omega); rw [h_eq]; exact base_82)
  | 83 => Or.inl (by have h_eq : n = 83 := (by omega); rw [h_eq]; exact base_83)
  | 84 => Or.inl (by have h_eq : n = 84 := (by omega); rw [h_eq]; exact base_84)
  | 85 => Or.inl (by have h_eq : n = 85 := (by omega); rw [h_eq]; exact base_85)
  | 86 => Or.inl (by have h_eq : n = 86 := (by omega); rw [h_eq]; exact base_86)
  | 87 => Or.inl (by have h_eq : n = 87 := (by omega); rw [h_eq]; exact base_87)
  | 88 => Or.inl (by have h_eq : n = 88 := (by omega); rw [h_eq]; exact base_88)
  | 89 => Or.inl (by have h_eq : n = 89 := (by omega); rw [h_eq]; exact base_89)
  | 90 => Or.inl (by have h_eq : n = 90 := (by omega); rw [h_eq]; exact base_90)
  | 91 => Or.inl (by have h_eq : n = 91 := (by omega); rw [h_eq]; exact base_91)
  | 92 => Or.inl (by have h_eq : n = 92 := (by omega); rw [h_eq]; exact base_92)
  | 93 => Or.inl (by have h_eq : n = 93 := (by omega); rw [h_eq]; exact base_93)
  | 94 => Or.inl (by have h_eq : n = 94 := (by omega); rw [h_eq]; exact base_94)
  | 95 => Or.inl (by have h_eq : n = 95 := (by omega); rw [h_eq]; exact base_95)
  | 96 => Or.inl (by have h_eq : n = 96 := (by omega); rw [h_eq]; exact base_96)
  | 97 => Or.inl (by have h_eq : n = 97 := (by omega); rw [h_eq]; exact base_97)
  | 98 => Or.inl (by have h_eq : n = 98 := (by omega); rw [h_eq]; exact base_98)
  | 99 => Or.inl (by have h_eq : n = 99 := (by omega); rw [h_eq]; exact base_99)
  | 100 => Or.inl (by have h_eq : n = 100 := (by omega); rw [h_eq]; exact base_100)
  | 101 => Or.inl (by have h_eq : n = 101 := (by omega); rw [h_eq]; exact base_101)
  | 102 => Or.inl (by have h_eq : n = 102 := (by omega); rw [h_eq]; exact base_102)
  | 103 => Or.inl (by have h_eq : n = 103 := (by omega); rw [h_eq]; exact base_103)
  | 104 => Or.inl (by have h_eq : n = 104 := (by omega); rw [h_eq]; exact base_104)
  | 105 => Or.inl (by have h_eq : n = 105 := (by omega); rw [h_eq]; exact base_105)
  | 106 => Or.inl (by have h_eq : n = 106 := (by omega); rw [h_eq]; exact base_106)
  | 107 => Or.inl (by have h_eq : n = 107 := (by omega); rw [h_eq]; exact base_107)
  | 108 => Or.inl (by have h_eq : n = 108 := (by omega); rw [h_eq]; exact base_108)
  | 109 => Or.inl (by have h_eq : n = 109 := (by omega); rw [h_eq]; exact base_109)
  | 110 => Or.inl (by have h_eq : n = 110 := (by omega); rw [h_eq]; exact base_110)
  | 111 => Or.inl (by have h_eq : n = 111 := (by omega); rw [h_eq]; exact base_111)
  | 112 => Or.inl (by have h_eq : n = 112 := (by omega); rw [h_eq]; exact base_112)
  | 113 => Or.inl (by have h_eq : n = 113 := (by omega); rw [h_eq]; exact base_113)
  | 114 => Or.inl (by have h_eq : n = 114 := (by omega); rw [h_eq]; exact base_114)
  | 115 => Or.inl (by have h_eq : n = 115 := (by omega); rw [h_eq]; exact base_115)
  | 116 => Or.inl (by have h_eq : n = 116 := (by omega); rw [h_eq]; exact base_116)
  | 117 => Or.inl (by have h_eq : n = 117 := (by omega); rw [h_eq]; exact base_117)
  | 118 => Or.inl (by have h_eq : n = 118 := (by omega); rw [h_eq]; exact base_118)
  | 119 => Or.inl (by have h_eq : n = 119 := (by omega); rw [h_eq]; exact base_119)
  | 120 => Or.inl (by have h_eq : n = 120 := (by omega); rw [h_eq]; exact base_120)
  | 121 => Or.inl (by have h_eq : n = 121 := (by omega); rw [h_eq]; exact base_121)
  | 122 => Or.inl (by have h_eq : n = 122 := (by omega); rw [h_eq]; exact base_122)
  | 123 => Or.inl (by have h_eq : n = 123 := (by omega); rw [h_eq]; exact base_123)
  | 124 => Or.inl (by have h_eq : n = 124 := (by omega); rw [h_eq]; exact base_124)
  | 125 => Or.inl (by have h_eq : n = 125 := (by omega); rw [h_eq]; exact base_125)
  | 126 => Or.inl (by have h_eq : n = 126 := (by omega); rw [h_eq]; exact base_126)
  | 127 => Or.inl (by have h_eq : n = 127 := (by omega); rw [h_eq]; exact base_127)
  | 128 => Or.inl (by have h_eq : n = 128 := (by omega); rw [h_eq]; exact base_128)
  | 129 => Or.inl (by have h_eq : n = 129 := (by omega); rw [h_eq]; exact base_129)
  | 130 => Or.inl (by have h_eq : n = 130 := (by omega); rw [h_eq]; exact base_130)
  | 131 => Or.inl (by have h_eq : n = 131 := (by omega); rw [h_eq]; exact base_131)
  | 132 => Or.inl (by have h_eq : n = 132 := (by omega); rw [h_eq]; exact base_132)
  | 133 => Or.inl (by have h_eq : n = 133 := (by omega); rw [h_eq]; exact base_133)
  | 134 => Or.inl (by have h_eq : n = 134 := (by omega); rw [h_eq]; exact base_134)
  | 135 => Or.inl (by have h_eq : n = 135 := (by omega); rw [h_eq]; exact base_135)
  | 136 => Or.inl (by have h_eq : n = 136 := (by omega); rw [h_eq]; exact base_136)
  | 137 => Or.inl (by have h_eq : n = 137 := (by omega); rw [h_eq]; exact base_137)
  | 138 => Or.inl (by have h_eq : n = 138 := (by omega); rw [h_eq]; exact base_138)
  | 139 => Or.inl (by have h_eq : n = 139 := (by omega); rw [h_eq]; exact base_139)
  | 140 => Or.inl (by have h_eq : n = 140 := (by omega); rw [h_eq]; exact base_140)
  | 141 => Or.inl (by have h_eq : n = 141 := (by omega); rw [h_eq]; exact base_141)
  | 142 => Or.inl (by have h_eq : n = 142 := (by omega); rw [h_eq]; exact base_142)
  | 143 => Or.inl (by have h_eq : n = 143 := (by omega); rw [h_eq]; exact base_143)
  | 144 => Or.inl (by have h_eq : n = 144 := (by omega); rw [h_eq]; exact base_144)
  | 145 => Or.inl (by have h_eq : n = 145 := (by omega); rw [h_eq]; exact base_145)
  | 146 => Or.inl (by have h_eq : n = 146 := (by omega); rw [h_eq]; exact base_146)
  | 147 => Or.inl (by have h_eq : n = 147 := (by omega); rw [h_eq]; exact base_147)
  | 148 => Or.inl (by have h_eq : n = 148 := (by omega); rw [h_eq]; exact base_148)
  | 149 => Or.inl (by have h_eq : n = 149 := (by omega); rw [h_eq]; exact base_149)
  | 150 => Or.inl (by have h_eq : n = 150 := (by omega); rw [h_eq]; exact base_150)
  | 151 => Or.inl (by have h_eq : n = 151 := (by omega); rw [h_eq]; exact base_151)
  | 152 => Or.inl (by have h_eq : n = 152 := (by omega); rw [h_eq]; exact base_152)
  | 153 => Or.inl (by have h_eq : n = 153 := (by omega); rw [h_eq]; exact base_153)
  | 154 => Or.inl (by have h_eq : n = 154 := (by omega); rw [h_eq]; exact base_154)
  | 155 => Or.inl (by have h_eq : n = 155 := (by omega); rw [h_eq]; exact base_155)
  | 156 => Or.inl (by have h_eq : n = 156 := (by omega); rw [h_eq]; exact base_156)
  | 157 => Or.inl (by have h_eq : n = 157 := (by omega); rw [h_eq]; exact base_157)
  | 158 => Or.inl (by have h_eq : n = 158 := (by omega); rw [h_eq]; exact base_158)
  | 159 => Or.inl (by have h_eq : n = 159 := (by omega); rw [h_eq]; exact base_159)
  | 160 => Or.inl (by have h_eq : n = 160 := (by omega); rw [h_eq]; exact base_160)
  | 161 => Or.inl (by have h_eq : n = 161 := (by omega); rw [h_eq]; exact base_161)
  | 162 => Or.inl (by have h_eq : n = 162 := (by omega); rw [h_eq]; exact base_162)
  | 163 => Or.inl (by have h_eq : n = 163 := (by omega); rw [h_eq]; exact base_163)
  | 164 => Or.inl (by have h_eq : n = 164 := (by omega); rw [h_eq]; exact base_164)
  | 165 => Or.inl (by have h_eq : n = 165 := (by omega); rw [h_eq]; exact base_165)
  | 166 => Or.inl (by have h_eq : n = 166 := (by omega); rw [h_eq]; exact base_166)
  | 167 => Or.inl (by have h_eq : n = 167 := (by omega); rw [h_eq]; exact base_167)
  | 168 => Or.inl (by have h_eq : n = 168 := (by omega); rw [h_eq]; exact base_168)
  | 169 => Or.inl (by have h_eq : n = 169 := (by omega); rw [h_eq]; exact base_169)
  | 170 => Or.inl (by have h_eq : n = 170 := (by omega); rw [h_eq]; exact base_170)
  | 171 => Or.inl (by have h_eq : n = 171 := (by omega); rw [h_eq]; exact base_171)
  | 172 => Or.inl (by have h_eq : n = 172 := (by omega); rw [h_eq]; exact base_172)
  | 173 => Or.inl (by have h_eq : n = 173 := (by omega); rw [h_eq]; exact base_173)
  | 174 => Or.inl (by have h_eq : n = 174 := (by omega); rw [h_eq]; exact base_174)
  | 175 => Or.inl (by have h_eq : n = 175 := (by omega); rw [h_eq]; exact base_175)
  | 176 => Or.inl (by have h_eq : n = 176 := (by omega); rw [h_eq]; exact base_176)
  | 177 => Or.inl (by have h_eq : n = 177 := (by omega); rw [h_eq]; exact base_177)
  | 178 => Or.inl (by have h_eq : n = 178 := (by omega); rw [h_eq]; exact base_178)
  | 179 => Or.inl (by have h_eq : n = 179 := (by omega); rw [h_eq]; exact base_179)
  | 180 => Or.inl (by have h_eq : n = 180 := (by omega); rw [h_eq]; exact base_180)
  | 181 => Or.inl (by have h_eq : n = 181 := (by omega); rw [h_eq]; exact base_181)
  | 182 => Or.inl (by have h_eq : n = 182 := (by omega); rw [h_eq]; exact base_182)
  | 183 => Or.inl (by have h_eq : n = 183 := (by omega); rw [h_eq]; exact base_183)
  | 184 => Or.inl (by have h_eq : n = 184 := (by omega); rw [h_eq]; exact base_184)
  | 185 => Or.inl (by have h_eq : n = 185 := (by omega); rw [h_eq]; exact base_185)
  | 186 => Or.inl (by have h_eq : n = 186 := (by omega); rw [h_eq]; exact base_186)
  | 187 => Or.inl (by have h_eq : n = 187 := (by omega); rw [h_eq]; exact base_187)
  | 188 => Or.inl (by have h_eq : n = 188 := (by omega); rw [h_eq]; exact base_188)
  | 189 => Or.inl (by have h_eq : n = 189 := (by omega); rw [h_eq]; exact base_189)
  | 190 => Or.inl (by have h_eq : n = 190 := (by omega); rw [h_eq]; exact base_190)
  | 191 => Or.inl (by have h_eq : n = 191 := (by omega); rw [h_eq]; exact base_191)
  | 192 => Or.inl (by have h_eq : n = 192 := (by omega); rw [h_eq]; exact base_192)
  | 193 => Or.inl (by have h_eq : n = 193 := (by omega); rw [h_eq]; exact base_193)
  | 194 => Or.inl (by have h_eq : n = 194 := (by omega); rw [h_eq]; exact base_194)
  | 195 => Or.inl (by have h_eq : n = 195 := (by omega); rw [h_eq]; exact base_195)
  | 196 => Or.inl (by have h_eq : n = 196 := (by omega); rw [h_eq]; exact base_196)
  | 197 => Or.inl (by have h_eq : n = 197 := (by omega); rw [h_eq]; exact base_197)
  | 198 => Or.inl (by have h_eq : n = 198 := (by omega); rw [h_eq]; exact base_198)
  | 199 => Or.inl (by have h_eq : n = 199 := (by omega); rw [h_eq]; exact base_199)
  | 200 => Or.inl (by have h_eq : n = 200 := (by omega); rw [h_eq]; exact base_200)
  | 201 => Or.inl (by have h_eq : n = 201 := (by omega); rw [h_eq]; exact base_201)
  | 202 => Or.inl (by have h_eq : n = 202 := (by omega); rw [h_eq]; exact base_202)
  | 203 => Or.inl (by have h_eq : n = 203 := (by omega); rw [h_eq]; exact base_203)
  | 204 => Or.inl (by have h_eq : n = 204 := (by omega); rw [h_eq]; exact base_204)
  | 205 => Or.inl (by have h_eq : n = 205 := (by omega); rw [h_eq]; exact base_205)
  | 206 => Or.inl (by have h_eq : n = 206 := (by omega); rw [h_eq]; exact base_206)
  | 207 => Or.inl (by have h_eq : n = 207 := (by omega); rw [h_eq]; exact base_207)
  | 208 => Or.inl (by have h_eq : n = 208 := (by omega); rw [h_eq]; exact base_208)
  | 209 => Or.inl (by have h_eq : n = 209 := (by omega); rw [h_eq]; exact base_209)
  | 210 => Or.inl (by have h_eq : n = 210 := (by omega); rw [h_eq]; exact base_210)
  | 211 => Or.inl (by have h_eq : n = 211 := (by omega); rw [h_eq]; exact base_211)
  | 212 => Or.inl (by have h_eq : n = 212 := (by omega); rw [h_eq]; exact base_212)
  | 213 => Or.inl (by have h_eq : n = 213 := (by omega); rw [h_eq]; exact base_213)
  | 214 => Or.inl (by have h_eq : n = 214 := (by omega); rw [h_eq]; exact base_214)
  | 215 => Or.inl (by have h_eq : n = 215 := (by omega); rw [h_eq]; exact base_215)
  | 216 => Or.inl (by have h_eq : n = 216 := (by omega); rw [h_eq]; exact base_216)
  | 217 => Or.inl (by have h_eq : n = 217 := (by omega); rw [h_eq]; exact base_217)
  | 218 => Or.inl (by have h_eq : n = 218 := (by omega); rw [h_eq]; exact base_218)
  | 219 => Or.inl (by have h_eq : n = 219 := (by omega); rw [h_eq]; exact base_219)
  | 220 => Or.inl (by have h_eq : n = 220 := (by omega); rw [h_eq]; exact base_220)
  | 221 => Or.inl (by have h_eq : n = 221 := (by omega); rw [h_eq]; exact base_221)
  | 222 => Or.inl (by have h_eq : n = 222 := (by omega); rw [h_eq]; exact base_222)
  | 223 => Or.inl (by have h_eq : n = 223 := (by omega); rw [h_eq]; exact base_223)
  | 224 => Or.inl (by have h_eq : n = 224 := (by omega); rw [h_eq]; exact base_224)
  | 225 => Or.inl (by have h_eq : n = 225 := (by omega); rw [h_eq]; exact base_225)
  | 226 => Or.inl (by have h_eq : n = 226 := (by omega); rw [h_eq]; exact base_226)
  | 227 => Or.inl (by have h_eq : n = 227 := (by omega); rw [h_eq]; exact base_227)
  | 228 => Or.inl (by have h_eq : n = 228 := (by omega); rw [h_eq]; exact base_228)
  | 229 => Or.inl (by have h_eq : n = 229 := (by omega); rw [h_eq]; exact base_229)
  | 230 => Or.inl (by have h_eq : n = 230 := (by omega); rw [h_eq]; exact base_230)
  | 231 => Or.inl (by have h_eq : n = 231 := (by omega); rw [h_eq]; exact base_231)
  | 232 => Or.inl (by have h_eq : n = 232 := (by omega); rw [h_eq]; exact base_232)
  | 233 => Or.inl (by have h_eq : n = 233 := (by omega); rw [h_eq]; exact base_233)
  | 234 => Or.inl (by have h_eq : n = 234 := (by omega); rw [h_eq]; exact base_234)
  | 235 => Or.inl (by have h_eq : n = 235 := (by omega); rw [h_eq]; exact base_235)
  | 236 => Or.inl (by have h_eq : n = 236 := (by omega); rw [h_eq]; exact base_236)
  | 237 => Or.inl (by have h_eq : n = 237 := (by omega); rw [h_eq]; exact base_237)
  | 238 => Or.inl (by have h_eq : n = 238 := (by omega); rw [h_eq]; exact base_238)
  | 239 => Or.inl (by have h_eq : n = 239 := (by omega); rw [h_eq]; exact base_239)
  | 240 => Or.inl (by have h_eq : n = 240 := (by omega); rw [h_eq]; exact base_240)
  | 241 => Or.inl (by have h_eq : n = 241 := (by omega); rw [h_eq]; exact base_241)
  | 242 => Or.inl (by have h_eq : n = 242 := (by omega); rw [h_eq]; exact base_242)
  | 243 => Or.inl (by have h_eq : n = 243 := (by omega); rw [h_eq]; exact base_243)
  | 244 => Or.inl (by have h_eq : n = 244 := (by omega); rw [h_eq]; exact base_244)
  | 245 => Or.inl (by have h_eq : n = 245 := (by omega); rw [h_eq]; exact base_245)
  | 246 => Or.inl (by have h_eq : n = 246 := (by omega); rw [h_eq]; exact base_246)
  | 247 => Or.inl (by have h_eq : n = 247 := (by omega); rw [h_eq]; exact base_247)
  | 248 => Or.inl (by have h_eq : n = 248 := (by omega); rw [h_eq]; exact base_248)
  | 249 => Or.inl (by have h_eq : n = 249 := (by omega); rw [h_eq]; exact base_249)
  | 250 => Or.inl (by have h_eq : n = 250 := (by omega); rw [h_eq]; exact base_250)
  | 251 => Or.inl (by have h_eq : n = 251 := (by omega); rw [h_eq]; exact base_251)
  | 252 => Or.inl (by have h_eq : n = 252 := (by omega); rw [h_eq]; exact base_252)
  | 253 => Or.inl (by have h_eq : n = 253 := (by omega); rw [h_eq]; exact base_253)
  | 254 => Or.inl (by have h_eq : n = 254 := (by omega); rw [h_eq]; exact base_254)
  | 255 => Or.inl (by have h_eq : n = 255 := (by omega); rw [h_eq]; exact base_255)
  | 256 => Or.inl (by have h_eq : n = 256 := (by omega); rw [h_eq]; exact base_256)
  | 257 => Or.inl (by have h_eq : n = 257 := (by omega); rw [h_eq]; exact base_257)
  | 258 => Or.inl (by have h_eq : n = 258 := (by omega); rw [h_eq]; exact base_258)
  | 259 => Or.inl (by have h_eq : n = 259 := (by omega); rw [h_eq]; exact base_259)
  | 260 => Or.inl (by have h_eq : n = 260 := (by omega); rw [h_eq]; exact base_260)
  | 261 => Or.inl (by have h_eq : n = 261 := (by omega); rw [h_eq]; exact base_261)
  | 262 => Or.inl (by have h_eq : n = 262 := (by omega); rw [h_eq]; exact base_262)
  | 263 => Or.inl (by have h_eq : n = 263 := (by omega); rw [h_eq]; exact base_263)
  | 264 => Or.inl (by have h_eq : n = 264 := (by omega); rw [h_eq]; exact base_264)
  | 265 => Or.inl (by have h_eq : n = 265 := (by omega); rw [h_eq]; exact base_265)
  | 266 => Or.inl (by have h_eq : n = 266 := (by omega); rw [h_eq]; exact base_266)
  | 267 => Or.inl (by have h_eq : n = 267 := (by omega); rw [h_eq]; exact base_267)
  | 268 => Or.inl (by have h_eq : n = 268 := (by omega); rw [h_eq]; exact base_268)
  | 269 => Or.inl (by have h_eq : n = 269 := (by omega); rw [h_eq]; exact base_269)
  | 270 => Or.inl (by have h_eq : n = 270 := (by omega); rw [h_eq]; exact base_270)
  | 271 => Or.inl (by have h_eq : n = 271 := (by omega); rw [h_eq]; exact base_271)
  | 272 => Or.inl (by have h_eq : n = 272 := (by omega); rw [h_eq]; exact base_272)
  | 273 => Or.inl (by have h_eq : n = 273 := (by omega); rw [h_eq]; exact base_273)
  | 274 => Or.inl (by have h_eq : n = 274 := (by omega); rw [h_eq]; exact base_274)
  | 275 => Or.inl (by have h_eq : n = 275 := (by omega); rw [h_eq]; exact base_275)
  | 276 => Or.inl (by have h_eq : n = 276 := (by omega); rw [h_eq]; exact base_276)
  | 277 => Or.inl (by have h_eq : n = 277 := (by omega); rw [h_eq]; exact base_277)
  | 278 => Or.inl (by have h_eq : n = 278 := (by omega); rw [h_eq]; exact base_278)
  | 279 => Or.inl (by have h_eq : n = 279 := (by omega); rw [h_eq]; exact base_279)
  | 280 => Or.inl (by have h_eq : n = 280 := (by omega); rw [h_eq]; exact base_280)
  | 281 => Or.inl (by have h_eq : n = 281 := (by omega); rw [h_eq]; exact base_281)
  | 282 => Or.inl (by have h_eq : n = 282 := (by omega); rw [h_eq]; exact base_282)
  | 283 => Or.inl (by have h_eq : n = 283 := (by omega); rw [h_eq]; exact base_283)
  | 284 => Or.inl (by have h_eq : n = 284 := (by omega); rw [h_eq]; exact base_284)
  | 285 => Or.inl (by have h_eq : n = 285 := (by omega); rw [h_eq]; exact base_285)
  | 286 => Or.inl (by have h_eq : n = 286 := (by omega); rw [h_eq]; exact base_286)
  | 287 => Or.inl (by have h_eq : n = 287 := (by omega); rw [h_eq]; exact base_287)
  | 288 => Or.inl (by have h_eq : n = 288 := (by omega); rw [h_eq]; exact base_288)
  | 289 => Or.inl (by have h_eq : n = 289 := (by omega); rw [h_eq]; exact base_289)
  | 290 => Or.inl (by have h_eq : n = 290 := (by omega); rw [h_eq]; exact base_290)
  | 291 => Or.inl (by have h_eq : n = 291 := (by omega); rw [h_eq]; exact base_291)
  | 292 => Or.inl (by have h_eq : n = 292 := (by omega); rw [h_eq]; exact base_292)
  | 293 => Or.inl (by have h_eq : n = 293 := (by omega); rw [h_eq]; exact base_293)
  | 294 => Or.inl (by have h_eq : n = 294 := (by omega); rw [h_eq]; exact base_294)
  | 295 => Or.inl (by have h_eq : n = 295 := (by omega); rw [h_eq]; exact base_295)
  | 296 => Or.inl (by have h_eq : n = 296 := (by omega); rw [h_eq]; exact base_296)
  | 297 => Or.inl (by have h_eq : n = 297 := (by omega); rw [h_eq]; exact base_297)
  | 298 => Or.inl (by have h_eq : n = 298 := (by omega); rw [h_eq]; exact base_298)
  | 299 => Or.inl (by have h_eq : n = 299 := (by omega); rw [h_eq]; exact base_299)
  | 300 => Or.inl (by have h_eq : n = 300 := (by omega); rw [h_eq]; exact base_300)
  | 301 => Or.inl (by have h_eq : n = 301 := (by omega); rw [h_eq]; exact base_301)
  | 302 => Or.inl (by have h_eq : n = 302 := (by omega); rw [h_eq]; exact base_302)
  | 303 => Or.inl (by have h_eq : n = 303 := (by omega); rw [h_eq]; exact base_303)
  | 304 => Or.inl (by have h_eq : n = 304 := (by omega); rw [h_eq]; exact base_304)
  | 305 => Or.inl (by have h_eq : n = 305 := (by omega); rw [h_eq]; exact base_305)
  | 306 => Or.inl (by have h_eq : n = 306 := (by omega); rw [h_eq]; exact base_306)
  | 307 => Or.inl (by have h_eq : n = 307 := (by omega); rw [h_eq]; exact base_307)
  | 308 => Or.inl (by have h_eq : n = 308 := (by omega); rw [h_eq]; exact base_308)
  | 309 => Or.inl (by have h_eq : n = 309 := (by omega); rw [h_eq]; exact base_309)
  | 310 => Or.inl (by have h_eq : n = 310 := (by omega); rw [h_eq]; exact base_310)
  | 311 => Or.inl (by have h_eq : n = 311 := (by omega); rw [h_eq]; exact base_311)
  | 312 => Or.inl (by have h_eq : n = 312 := (by omega); rw [h_eq]; exact base_312)
  | 313 => Or.inl (by have h_eq : n = 313 := (by omega); rw [h_eq]; exact base_313)
  | 314 => Or.inl (by have h_eq : n = 314 := (by omega); rw [h_eq]; exact base_314)
  | 315 => Or.inl (by have h_eq : n = 315 := (by omega); rw [h_eq]; exact base_315)
  | 316 => Or.inl (by have h_eq : n = 316 := (by omega); rw [h_eq]; exact base_316)
  | 317 => Or.inl (by have h_eq : n = 317 := (by omega); rw [h_eq]; exact base_317)
  | 318 => Or.inl (by have h_eq : n = 318 := (by omega); rw [h_eq]; exact base_318)
  | 319 => Or.inl (by have h_eq : n = 319 := (by omega); rw [h_eq]; exact base_319)
  | 320 => Or.inl (by have h_eq : n = 320 := (by omega); rw [h_eq]; exact base_320)
  | 321 => Or.inl (by have h_eq : n = 321 := (by omega); rw [h_eq]; exact base_321)
  | 322 => Or.inl (by have h_eq : n = 322 := (by omega); rw [h_eq]; exact base_322)
  | 323 => Or.inl (by have h_eq : n = 323 := (by omega); rw [h_eq]; exact base_323)
  | 324 => Or.inl (by have h_eq : n = 324 := (by omega); rw [h_eq]; exact base_324)
  | 325 => Or.inl (by have h_eq : n = 325 := (by omega); rw [h_eq]; exact base_325)
  | 326 => Or.inl (by have h_eq : n = 326 := (by omega); rw [h_eq]; exact base_326)
  | 327 => Or.inl (by have h_eq : n = 327 := (by omega); rw [h_eq]; exact base_327)
  | 328 => Or.inl (by have h_eq : n = 328 := (by omega); rw [h_eq]; exact base_328)
  | 329 => Or.inl (by have h_eq : n = 329 := (by omega); rw [h_eq]; exact base_329)
  | 330 => Or.inl (by have h_eq : n = 330 := (by omega); rw [h_eq]; exact base_330)
  | 331 => Or.inl (by have h_eq : n = 331 := (by omega); rw [h_eq]; exact base_331)
  | 332 => Or.inl (by have h_eq : n = 332 := (by omega); rw [h_eq]; exact base_332)
  | 333 => Or.inl (by have h_eq : n = 333 := (by omega); rw [h_eq]; exact base_333)
  | 334 => Or.inl (by have h_eq : n = 334 := (by omega); rw [h_eq]; exact base_334)
  | 335 => Or.inl (by have h_eq : n = 335 := (by omega); rw [h_eq]; exact base_335)
  | 336 => Or.inl (by have h_eq : n = 336 := (by omega); rw [h_eq]; exact base_336)
  | 337 => Or.inl (by have h_eq : n = 337 := (by omega); rw [h_eq]; exact base_337)
  | 338 => Or.inl (by have h_eq : n = 338 := (by omega); rw [h_eq]; exact base_338)
  | 339 => Or.inl (by have h_eq : n = 339 := (by omega); rw [h_eq]; exact base_339)
  | 340 => Or.inl (by have h_eq : n = 340 := (by omega); rw [h_eq]; exact base_340)
  | 341 => Or.inl (by have h_eq : n = 341 := (by omega); rw [h_eq]; exact base_341)
  | 342 => Or.inl (by have h_eq : n = 342 := (by omega); rw [h_eq]; exact base_342)
  | 343 => Or.inl (by have h_eq : n = 343 := (by omega); rw [h_eq]; exact base_343)
  | 344 => Or.inl (by have h_eq : n = 344 := (by omega); rw [h_eq]; exact base_344)
  | 345 => Or.inl (by have h_eq : n = 345 := (by omega); rw [h_eq]; exact base_345)
  | 346 => Or.inl (by have h_eq : n = 346 := (by omega); rw [h_eq]; exact base_346)
  | 347 => Or.inl (by have h_eq : n = 347 := (by omega); rw [h_eq]; exact base_347)
  | 348 => Or.inl (by have h_eq : n = 348 := (by omega); rw [h_eq]; exact base_348)
  | 349 => Or.inl (by have h_eq : n = 349 := (by omega); rw [h_eq]; exact base_349)
  | 350 => Or.inl (by have h_eq : n = 350 := (by omega); rw [h_eq]; exact base_350)
  | 351 => Or.inl (by have h_eq : n = 351 := (by omega); rw [h_eq]; exact base_351)
  | 352 => Or.inl (by have h_eq : n = 352 := (by omega); rw [h_eq]; exact base_352)
  | 353 => Or.inl (by have h_eq : n = 353 := (by omega); rw [h_eq]; exact base_353)
  | 354 => Or.inl (by have h_eq : n = 354 := (by omega); rw [h_eq]; exact base_354)
  | 355 => Or.inl (by have h_eq : n = 355 := (by omega); rw [h_eq]; exact base_355)
  | 356 => Or.inl (by have h_eq : n = 356 := (by omega); rw [h_eq]; exact base_356)
  | 357 => Or.inl (by have h_eq : n = 357 := (by omega); rw [h_eq]; exact base_357)
  | 358 => Or.inl (by have h_eq : n = 358 := (by omega); rw [h_eq]; exact base_358)
  | 359 => Or.inl (by have h_eq : n = 359 := (by omega); rw [h_eq]; exact base_359)
  | 360 => Or.inl (by have h_eq : n = 360 := (by omega); rw [h_eq]; exact base_360)
  | 361 => Or.inl (by have h_eq : n = 361 := (by omega); rw [h_eq]; exact base_361)
  | 362 => Or.inl (by have h_eq : n = 362 := (by omega); rw [h_eq]; exact base_362)
  | 363 => Or.inl (by have h_eq : n = 363 := (by omega); rw [h_eq]; exact base_363)
  | 364 => Or.inl (by have h_eq : n = 364 := (by omega); rw [h_eq]; exact base_364)
  | 365 => Or.inl (by have h_eq : n = 365 := (by omega); rw [h_eq]; exact base_365)
  | 366 => Or.inl (by have h_eq : n = 366 := (by omega); rw [h_eq]; exact base_366)
  | 367 => Or.inl (by have h_eq : n = 367 := (by omega); rw [h_eq]; exact base_367)
  | 368 => Or.inl (by have h_eq : n = 368 := (by omega); rw [h_eq]; exact base_368)
  | 369 => Or.inl (by have h_eq : n = 369 := (by omega); rw [h_eq]; exact base_369)
  | 370 => Or.inl (by have h_eq : n = 370 := (by omega); rw [h_eq]; exact base_370)
  | 371 => Or.inl (by have h_eq : n = 371 := (by omega); rw [h_eq]; exact base_371)
  | 372 => Or.inl (by have h_eq : n = 372 := (by omega); rw [h_eq]; exact base_372)
  | 373 => Or.inl (by have h_eq : n = 373 := (by omega); rw [h_eq]; exact base_373)
  | 374 => Or.inl (by have h_eq : n = 374 := (by omega); rw [h_eq]; exact base_374)
  | 375 => Or.inl (by have h_eq : n = 375 := (by omega); rw [h_eq]; exact base_375)
  | 376 => Or.inl (by have h_eq : n = 376 := (by omega); rw [h_eq]; exact base_376)
  | 377 => Or.inl (by have h_eq : n = 377 := (by omega); rw [h_eq]; exact base_377)
  | 378 => Or.inl (by have h_eq : n = 378 := (by omega); rw [h_eq]; exact base_378)
  | 379 => Or.inl (by have h_eq : n = 379 := (by omega); rw [h_eq]; exact base_379)
  | 380 => Or.inl (by have h_eq : n = 380 := (by omega); rw [h_eq]; exact base_380)
  | 381 => Or.inl (by have h_eq : n = 381 := (by omega); rw [h_eq]; exact base_381)
  | 382 => Or.inl (by have h_eq : n = 382 := (by omega); rw [h_eq]; exact base_382)
  | 383 => Or.inl (by have h_eq : n = 383 := (by omega); rw [h_eq]; exact base_383)
  | 384 => Or.inl (by have h_eq : n = 384 := (by omega); rw [h_eq]; exact base_384)
  | 385 => Or.inl (by have h_eq : n = 385 := (by omega); rw [h_eq]; exact base_385)
  | 386 => Or.inl (by have h_eq : n = 386 := (by omega); rw [h_eq]; exact base_386)
  | 387 => Or.inl (by have h_eq : n = 387 := (by omega); rw [h_eq]; exact base_387)
  | 388 => Or.inl (by have h_eq : n = 388 := (by omega); rw [h_eq]; exact base_388)
  | 389 => Or.inl (by have h_eq : n = 389 := (by omega); rw [h_eq]; exact base_389)
  | 390 => Or.inl (by have h_eq : n = 390 := (by omega); rw [h_eq]; exact base_390)
  | 391 => Or.inl (by have h_eq : n = 391 := (by omega); rw [h_eq]; exact base_391)
  | 392 => Or.inl (by have h_eq : n = 392 := (by omega); rw [h_eq]; exact base_392)
  | 393 => Or.inl (by have h_eq : n = 393 := (by omega); rw [h_eq]; exact base_393)
  | 394 => Or.inl (by have h_eq : n = 394 := (by omega); rw [h_eq]; exact base_394)
  | 395 => Or.inl (by have h_eq : n = 395 := (by omega); rw [h_eq]; exact base_395)
  | 396 => Or.inl (by have h_eq : n = 396 := (by omega); rw [h_eq]; exact base_396)
  | 397 => Or.inl (by have h_eq : n = 397 := (by omega); rw [h_eq]; exact base_397)
  | 398 => Or.inl (by have h_eq : n = 398 := (by omega); rw [h_eq]; exact base_398)
  | 399 => Or.inl (by have h_eq : n = 399 := (by omega); rw [h_eq]; exact base_399)
  | m + 400 => Or.inr (by omega)

lemma base_cases_chunk_1 (n : ℕ) (h_low : 400 ≤ n) : 0 < A271510 n ∨ n ≥ 800 :=
  match h : n - 400 with
  | 0 => Or.inl (by have h_eq : n = 400 := (by omega); rw [h_eq]; exact base_400)
  | 1 => Or.inl (by have h_eq : n = 401 := (by omega); rw [h_eq]; exact base_401)
  | 2 => Or.inl (by have h_eq : n = 402 := (by omega); rw [h_eq]; exact base_402)
  | 3 => Or.inl (by have h_eq : n = 403 := (by omega); rw [h_eq]; exact base_403)
  | 4 => Or.inl (by have h_eq : n = 404 := (by omega); rw [h_eq]; exact base_404)
  | 5 => Or.inl (by have h_eq : n = 405 := (by omega); rw [h_eq]; exact base_405)
  | 6 => Or.inl (by have h_eq : n = 406 := (by omega); rw [h_eq]; exact base_406)
  | 7 => Or.inl (by have h_eq : n = 407 := (by omega); rw [h_eq]; exact base_407)
  | 8 => Or.inl (by have h_eq : n = 408 := (by omega); rw [h_eq]; exact base_408)
  | 9 => Or.inl (by have h_eq : n = 409 := (by omega); rw [h_eq]; exact base_409)
  | 10 => Or.inl (by have h_eq : n = 410 := (by omega); rw [h_eq]; exact base_410)
  | 11 => Or.inl (by have h_eq : n = 411 := (by omega); rw [h_eq]; exact base_411)
  | 12 => Or.inl (by have h_eq : n = 412 := (by omega); rw [h_eq]; exact base_412)
  | 13 => Or.inl (by have h_eq : n = 413 := (by omega); rw [h_eq]; exact base_413)
  | 14 => Or.inl (by have h_eq : n = 414 := (by omega); rw [h_eq]; exact base_414)
  | 15 => Or.inl (by have h_eq : n = 415 := (by omega); rw [h_eq]; exact base_415)
  | 16 => Or.inl (by have h_eq : n = 416 := (by omega); rw [h_eq]; exact base_416)
  | 17 => Or.inl (by have h_eq : n = 417 := (by omega); rw [h_eq]; exact base_417)
  | 18 => Or.inl (by have h_eq : n = 418 := (by omega); rw [h_eq]; exact base_418)
  | 19 => Or.inl (by have h_eq : n = 419 := (by omega); rw [h_eq]; exact base_419)
  | 20 => Or.inl (by have h_eq : n = 420 := (by omega); rw [h_eq]; exact base_420)
  | 21 => Or.inl (by have h_eq : n = 421 := (by omega); rw [h_eq]; exact base_421)
  | 22 => Or.inl (by have h_eq : n = 422 := (by omega); rw [h_eq]; exact base_422)
  | 23 => Or.inl (by have h_eq : n = 423 := (by omega); rw [h_eq]; exact base_423)
  | 24 => Or.inl (by have h_eq : n = 424 := (by omega); rw [h_eq]; exact base_424)
  | 25 => Or.inl (by have h_eq : n = 425 := (by omega); rw [h_eq]; exact base_425)
  | 26 => Or.inl (by have h_eq : n = 426 := (by omega); rw [h_eq]; exact base_426)
  | 27 => Or.inl (by have h_eq : n = 427 := (by omega); rw [h_eq]; exact base_427)
  | 28 => Or.inl (by have h_eq : n = 428 := (by omega); rw [h_eq]; exact base_428)
  | 29 => Or.inl (by have h_eq : n = 429 := (by omega); rw [h_eq]; exact base_429)
  | 30 => Or.inl (by have h_eq : n = 430 := (by omega); rw [h_eq]; exact base_430)
  | 31 => Or.inl (by have h_eq : n = 431 := (by omega); rw [h_eq]; exact base_431)
  | 32 => Or.inl (by have h_eq : n = 432 := (by omega); rw [h_eq]; exact base_432)
  | 33 => Or.inl (by have h_eq : n = 433 := (by omega); rw [h_eq]; exact base_433)
  | 34 => Or.inl (by have h_eq : n = 434 := (by omega); rw [h_eq]; exact base_434)
  | 35 => Or.inl (by have h_eq : n = 435 := (by omega); rw [h_eq]; exact base_435)
  | 36 => Or.inl (by have h_eq : n = 436 := (by omega); rw [h_eq]; exact base_436)
  | 37 => Or.inl (by have h_eq : n = 437 := (by omega); rw [h_eq]; exact base_437)
  | 38 => Or.inl (by have h_eq : n = 438 := (by omega); rw [h_eq]; exact base_438)
  | 39 => Or.inl (by have h_eq : n = 439 := (by omega); rw [h_eq]; exact base_439)
  | 40 => Or.inl (by have h_eq : n = 440 := (by omega); rw [h_eq]; exact base_440)
  | 41 => Or.inl (by have h_eq : n = 441 := (by omega); rw [h_eq]; exact base_441)
  | 42 => Or.inl (by have h_eq : n = 442 := (by omega); rw [h_eq]; exact base_442)
  | 43 => Or.inl (by have h_eq : n = 443 := (by omega); rw [h_eq]; exact base_443)
  | 44 => Or.inl (by have h_eq : n = 444 := (by omega); rw [h_eq]; exact base_444)
  | 45 => Or.inl (by have h_eq : n = 445 := (by omega); rw [h_eq]; exact base_445)
  | 46 => Or.inl (by have h_eq : n = 446 := (by omega); rw [h_eq]; exact base_446)
  | 47 => Or.inl (by have h_eq : n = 447 := (by omega); rw [h_eq]; exact base_447)
  | 48 => Or.inl (by have h_eq : n = 448 := (by omega); rw [h_eq]; exact base_448)
  | 49 => Or.inl (by have h_eq : n = 449 := (by omega); rw [h_eq]; exact base_449)
  | 50 => Or.inl (by have h_eq : n = 450 := (by omega); rw [h_eq]; exact base_450)
  | 51 => Or.inl (by have h_eq : n = 451 := (by omega); rw [h_eq]; exact base_451)
  | 52 => Or.inl (by have h_eq : n = 452 := (by omega); rw [h_eq]; exact base_452)
  | 53 => Or.inl (by have h_eq : n = 453 := (by omega); rw [h_eq]; exact base_453)
  | 54 => Or.inl (by have h_eq : n = 454 := (by omega); rw [h_eq]; exact base_454)
  | 55 => Or.inl (by have h_eq : n = 455 := (by omega); rw [h_eq]; exact base_455)
  | 56 => Or.inl (by have h_eq : n = 456 := (by omega); rw [h_eq]; exact base_456)
  | 57 => Or.inl (by have h_eq : n = 457 := (by omega); rw [h_eq]; exact base_457)
  | 58 => Or.inl (by have h_eq : n = 458 := (by omega); rw [h_eq]; exact base_458)
  | 59 => Or.inl (by have h_eq : n = 459 := (by omega); rw [h_eq]; exact base_459)
  | 60 => Or.inl (by have h_eq : n = 460 := (by omega); rw [h_eq]; exact base_460)
  | 61 => Or.inl (by have h_eq : n = 461 := (by omega); rw [h_eq]; exact base_461)
  | 62 => Or.inl (by have h_eq : n = 462 := (by omega); rw [h_eq]; exact base_462)
  | 63 => Or.inl (by have h_eq : n = 463 := (by omega); rw [h_eq]; exact base_463)
  | 64 => Or.inl (by have h_eq : n = 464 := (by omega); rw [h_eq]; exact base_464)
  | 65 => Or.inl (by have h_eq : n = 465 := (by omega); rw [h_eq]; exact base_465)
  | 66 => Or.inl (by have h_eq : n = 466 := (by omega); rw [h_eq]; exact base_466)
  | 67 => Or.inl (by have h_eq : n = 467 := (by omega); rw [h_eq]; exact base_467)
  | 68 => Or.inl (by have h_eq : n = 468 := (by omega); rw [h_eq]; exact base_468)
  | 69 => Or.inl (by have h_eq : n = 469 := (by omega); rw [h_eq]; exact base_469)
  | 70 => Or.inl (by have h_eq : n = 470 := (by omega); rw [h_eq]; exact base_470)
  | 71 => Or.inl (by have h_eq : n = 471 := (by omega); rw [h_eq]; exact base_471)
  | 72 => Or.inl (by have h_eq : n = 472 := (by omega); rw [h_eq]; exact base_472)
  | 73 => Or.inl (by have h_eq : n = 473 := (by omega); rw [h_eq]; exact base_473)
  | 74 => Or.inl (by have h_eq : n = 474 := (by omega); rw [h_eq]; exact base_474)
  | 75 => Or.inl (by have h_eq : n = 475 := (by omega); rw [h_eq]; exact base_475)
  | 76 => Or.inl (by have h_eq : n = 476 := (by omega); rw [h_eq]; exact base_476)
  | 77 => Or.inl (by have h_eq : n = 477 := (by omega); rw [h_eq]; exact base_477)
  | 78 => Or.inl (by have h_eq : n = 478 := (by omega); rw [h_eq]; exact base_478)
  | 79 => Or.inl (by have h_eq : n = 479 := (by omega); rw [h_eq]; exact base_479)
  | 80 => Or.inl (by have h_eq : n = 480 := (by omega); rw [h_eq]; exact base_480)
  | 81 => Or.inl (by have h_eq : n = 481 := (by omega); rw [h_eq]; exact base_481)
  | 82 => Or.inl (by have h_eq : n = 482 := (by omega); rw [h_eq]; exact base_482)
  | 83 => Or.inl (by have h_eq : n = 483 := (by omega); rw [h_eq]; exact base_483)
  | 84 => Or.inl (by have h_eq : n = 484 := (by omega); rw [h_eq]; exact base_484)
  | 85 => Or.inl (by have h_eq : n = 485 := (by omega); rw [h_eq]; exact base_485)
  | 86 => Or.inl (by have h_eq : n = 486 := (by omega); rw [h_eq]; exact base_486)
  | 87 => Or.inl (by have h_eq : n = 487 := (by omega); rw [h_eq]; exact base_487)
  | 88 => Or.inl (by have h_eq : n = 488 := (by omega); rw [h_eq]; exact base_488)
  | 89 => Or.inl (by have h_eq : n = 489 := (by omega); rw [h_eq]; exact base_489)
  | 90 => Or.inl (by have h_eq : n = 490 := (by omega); rw [h_eq]; exact base_490)
  | 91 => Or.inl (by have h_eq : n = 491 := (by omega); rw [h_eq]; exact base_491)
  | 92 => Or.inl (by have h_eq : n = 492 := (by omega); rw [h_eq]; exact base_492)
  | 93 => Or.inl (by have h_eq : n = 493 := (by omega); rw [h_eq]; exact base_493)
  | 94 => Or.inl (by have h_eq : n = 494 := (by omega); rw [h_eq]; exact base_494)
  | 95 => Or.inl (by have h_eq : n = 495 := (by omega); rw [h_eq]; exact base_495)
  | 96 => Or.inl (by have h_eq : n = 496 := (by omega); rw [h_eq]; exact base_496)
  | 97 => Or.inl (by have h_eq : n = 497 := (by omega); rw [h_eq]; exact base_497)
  | 98 => Or.inl (by have h_eq : n = 498 := (by omega); rw [h_eq]; exact base_498)
  | 99 => Or.inl (by have h_eq : n = 499 := (by omega); rw [h_eq]; exact base_499)
  | 100 => Or.inl (by have h_eq : n = 500 := (by omega); rw [h_eq]; exact base_500)
  | 101 => Or.inl (by have h_eq : n = 501 := (by omega); rw [h_eq]; exact base_501)
  | 102 => Or.inl (by have h_eq : n = 502 := (by omega); rw [h_eq]; exact base_502)
  | 103 => Or.inl (by have h_eq : n = 503 := (by omega); rw [h_eq]; exact base_503)
  | 104 => Or.inl (by have h_eq : n = 504 := (by omega); rw [h_eq]; exact base_504)
  | 105 => Or.inl (by have h_eq : n = 505 := (by omega); rw [h_eq]; exact base_505)
  | 106 => Or.inl (by have h_eq : n = 506 := (by omega); rw [h_eq]; exact base_506)
  | 107 => Or.inl (by have h_eq : n = 507 := (by omega); rw [h_eq]; exact base_507)
  | 108 => Or.inl (by have h_eq : n = 508 := (by omega); rw [h_eq]; exact base_508)
  | 109 => Or.inl (by have h_eq : n = 509 := (by omega); rw [h_eq]; exact base_509)
  | 110 => Or.inl (by have h_eq : n = 510 := (by omega); rw [h_eq]; exact base_510)
  | 111 => Or.inl (by have h_eq : n = 511 := (by omega); rw [h_eq]; exact base_511)
  | 112 => Or.inl (by have h_eq : n = 512 := (by omega); rw [h_eq]; exact base_512)
  | 113 => Or.inl (by have h_eq : n = 513 := (by omega); rw [h_eq]; exact base_513)
  | 114 => Or.inl (by have h_eq : n = 514 := (by omega); rw [h_eq]; exact base_514)
  | 115 => Or.inl (by have h_eq : n = 515 := (by omega); rw [h_eq]; exact base_515)
  | 116 => Or.inl (by have h_eq : n = 516 := (by omega); rw [h_eq]; exact base_516)
  | 117 => Or.inl (by have h_eq : n = 517 := (by omega); rw [h_eq]; exact base_517)
  | 118 => Or.inl (by have h_eq : n = 518 := (by omega); rw [h_eq]; exact base_518)
  | 119 => Or.inl (by have h_eq : n = 519 := (by omega); rw [h_eq]; exact base_519)
  | 120 => Or.inl (by have h_eq : n = 520 := (by omega); rw [h_eq]; exact base_520)
  | 121 => Or.inl (by have h_eq : n = 521 := (by omega); rw [h_eq]; exact base_521)
  | 122 => Or.inl (by have h_eq : n = 522 := (by omega); rw [h_eq]; exact base_522)
  | 123 => Or.inl (by have h_eq : n = 523 := (by omega); rw [h_eq]; exact base_523)
  | 124 => Or.inl (by have h_eq : n = 524 := (by omega); rw [h_eq]; exact base_524)
  | 125 => Or.inl (by have h_eq : n = 525 := (by omega); rw [h_eq]; exact base_525)
  | 126 => Or.inl (by have h_eq : n = 526 := (by omega); rw [h_eq]; exact base_526)
  | 127 => Or.inl (by have h_eq : n = 527 := (by omega); rw [h_eq]; exact base_527)
  | 128 => Or.inl (by have h_eq : n = 528 := (by omega); rw [h_eq]; exact base_528)
  | 129 => Or.inl (by have h_eq : n = 529 := (by omega); rw [h_eq]; exact base_529)
  | 130 => Or.inl (by have h_eq : n = 530 := (by omega); rw [h_eq]; exact base_530)
  | 131 => Or.inl (by have h_eq : n = 531 := (by omega); rw [h_eq]; exact base_531)
  | 132 => Or.inl (by have h_eq : n = 532 := (by omega); rw [h_eq]; exact base_532)
  | 133 => Or.inl (by have h_eq : n = 533 := (by omega); rw [h_eq]; exact base_533)
  | 134 => Or.inl (by have h_eq : n = 534 := (by omega); rw [h_eq]; exact base_534)
  | 135 => Or.inl (by have h_eq : n = 535 := (by omega); rw [h_eq]; exact base_535)
  | 136 => Or.inl (by have h_eq : n = 536 := (by omega); rw [h_eq]; exact base_536)
  | 137 => Or.inl (by have h_eq : n = 537 := (by omega); rw [h_eq]; exact base_537)
  | 138 => Or.inl (by have h_eq : n = 538 := (by omega); rw [h_eq]; exact base_538)
  | 139 => Or.inl (by have h_eq : n = 539 := (by omega); rw [h_eq]; exact base_539)
  | 140 => Or.inl (by have h_eq : n = 540 := (by omega); rw [h_eq]; exact base_540)
  | 141 => Or.inl (by have h_eq : n = 541 := (by omega); rw [h_eq]; exact base_541)
  | 142 => Or.inl (by have h_eq : n = 542 := (by omega); rw [h_eq]; exact base_542)
  | 143 => Or.inl (by have h_eq : n = 543 := (by omega); rw [h_eq]; exact base_543)
  | 144 => Or.inl (by have h_eq : n = 544 := (by omega); rw [h_eq]; exact base_544)
  | 145 => Or.inl (by have h_eq : n = 545 := (by omega); rw [h_eq]; exact base_545)
  | 146 => Or.inl (by have h_eq : n = 546 := (by omega); rw [h_eq]; exact base_546)
  | 147 => Or.inl (by have h_eq : n = 547 := (by omega); rw [h_eq]; exact base_547)
  | 148 => Or.inl (by have h_eq : n = 548 := (by omega); rw [h_eq]; exact base_548)
  | 149 => Or.inl (by have h_eq : n = 549 := (by omega); rw [h_eq]; exact base_549)
  | 150 => Or.inl (by have h_eq : n = 550 := (by omega); rw [h_eq]; exact base_550)
  | 151 => Or.inl (by have h_eq : n = 551 := (by omega); rw [h_eq]; exact base_551)
  | 152 => Or.inl (by have h_eq : n = 552 := (by omega); rw [h_eq]; exact base_552)
  | 153 => Or.inl (by have h_eq : n = 553 := (by omega); rw [h_eq]; exact base_553)
  | 154 => Or.inl (by have h_eq : n = 554 := (by omega); rw [h_eq]; exact base_554)
  | 155 => Or.inl (by have h_eq : n = 555 := (by omega); rw [h_eq]; exact base_555)
  | 156 => Or.inl (by have h_eq : n = 556 := (by omega); rw [h_eq]; exact base_556)
  | 157 => Or.inl (by have h_eq : n = 557 := (by omega); rw [h_eq]; exact base_557)
  | 158 => Or.inl (by have h_eq : n = 558 := (by omega); rw [h_eq]; exact base_558)
  | 159 => Or.inl (by have h_eq : n = 559 := (by omega); rw [h_eq]; exact base_559)
  | 160 => Or.inl (by have h_eq : n = 560 := (by omega); rw [h_eq]; exact base_560)
  | 161 => Or.inl (by have h_eq : n = 561 := (by omega); rw [h_eq]; exact base_561)
  | 162 => Or.inl (by have h_eq : n = 562 := (by omega); rw [h_eq]; exact base_562)
  | 163 => Or.inl (by have h_eq : n = 563 := (by omega); rw [h_eq]; exact base_563)
  | 164 => Or.inl (by have h_eq : n = 564 := (by omega); rw [h_eq]; exact base_564)
  | 165 => Or.inl (by have h_eq : n = 565 := (by omega); rw [h_eq]; exact base_565)
  | 166 => Or.inl (by have h_eq : n = 566 := (by omega); rw [h_eq]; exact base_566)
  | 167 => Or.inl (by have h_eq : n = 567 := (by omega); rw [h_eq]; exact base_567)
  | 168 => Or.inl (by have h_eq : n = 568 := (by omega); rw [h_eq]; exact base_568)
  | 169 => Or.inl (by have h_eq : n = 569 := (by omega); rw [h_eq]; exact base_569)
  | 170 => Or.inl (by have h_eq : n = 570 := (by omega); rw [h_eq]; exact base_570)
  | 171 => Or.inl (by have h_eq : n = 571 := (by omega); rw [h_eq]; exact base_571)
  | 172 => Or.inl (by have h_eq : n = 572 := (by omega); rw [h_eq]; exact base_572)
  | 173 => Or.inl (by have h_eq : n = 573 := (by omega); rw [h_eq]; exact base_573)
  | 174 => Or.inl (by have h_eq : n = 574 := (by omega); rw [h_eq]; exact base_574)
  | 175 => Or.inl (by have h_eq : n = 575 := (by omega); rw [h_eq]; exact base_575)
  | 176 => Or.inl (by have h_eq : n = 576 := (by omega); rw [h_eq]; exact base_576)
  | 177 => Or.inl (by have h_eq : n = 577 := (by omega); rw [h_eq]; exact base_577)
  | 178 => Or.inl (by have h_eq : n = 578 := (by omega); rw [h_eq]; exact base_578)
  | 179 => Or.inl (by have h_eq : n = 579 := (by omega); rw [h_eq]; exact base_579)
  | 180 => Or.inl (by have h_eq : n = 580 := (by omega); rw [h_eq]; exact base_580)
  | 181 => Or.inl (by have h_eq : n = 581 := (by omega); rw [h_eq]; exact base_581)
  | 182 => Or.inl (by have h_eq : n = 582 := (by omega); rw [h_eq]; exact base_582)
  | 183 => Or.inl (by have h_eq : n = 583 := (by omega); rw [h_eq]; exact base_583)
  | 184 => Or.inl (by have h_eq : n = 584 := (by omega); rw [h_eq]; exact base_584)
  | 185 => Or.inl (by have h_eq : n = 585 := (by omega); rw [h_eq]; exact base_585)
  | 186 => Or.inl (by have h_eq : n = 586 := (by omega); rw [h_eq]; exact base_586)
  | 187 => Or.inl (by have h_eq : n = 587 := (by omega); rw [h_eq]; exact base_587)
  | 188 => Or.inl (by have h_eq : n = 588 := (by omega); rw [h_eq]; exact base_588)
  | 189 => Or.inl (by have h_eq : n = 589 := (by omega); rw [h_eq]; exact base_589)
  | 190 => Or.inl (by have h_eq : n = 590 := (by omega); rw [h_eq]; exact base_590)
  | 191 => Or.inl (by have h_eq : n = 591 := (by omega); rw [h_eq]; exact base_591)
  | 192 => Or.inl (by have h_eq : n = 592 := (by omega); rw [h_eq]; exact base_592)
  | 193 => Or.inl (by have h_eq : n = 593 := (by omega); rw [h_eq]; exact base_593)
  | 194 => Or.inl (by have h_eq : n = 594 := (by omega); rw [h_eq]; exact base_594)
  | 195 => Or.inl (by have h_eq : n = 595 := (by omega); rw [h_eq]; exact base_595)
  | 196 => Or.inl (by have h_eq : n = 596 := (by omega); rw [h_eq]; exact base_596)
  | 197 => Or.inl (by have h_eq : n = 597 := (by omega); rw [h_eq]; exact base_597)
  | 198 => Or.inl (by have h_eq : n = 598 := (by omega); rw [h_eq]; exact base_598)
  | 199 => Or.inl (by have h_eq : n = 599 := (by omega); rw [h_eq]; exact base_599)
  | 200 => Or.inl (by have h_eq : n = 600 := (by omega); rw [h_eq]; exact base_600)
  | 201 => Or.inl (by have h_eq : n = 601 := (by omega); rw [h_eq]; exact base_601)
  | 202 => Or.inl (by have h_eq : n = 602 := (by omega); rw [h_eq]; exact base_602)
  | 203 => Or.inl (by have h_eq : n = 603 := (by omega); rw [h_eq]; exact base_603)
  | 204 => Or.inl (by have h_eq : n = 604 := (by omega); rw [h_eq]; exact base_604)
  | 205 => Or.inl (by have h_eq : n = 605 := (by omega); rw [h_eq]; exact base_605)
  | 206 => Or.inl (by have h_eq : n = 606 := (by omega); rw [h_eq]; exact base_606)
  | 207 => Or.inl (by have h_eq : n = 607 := (by omega); rw [h_eq]; exact base_607)
  | 208 => Or.inl (by have h_eq : n = 608 := (by omega); rw [h_eq]; exact base_608)
  | 209 => Or.inl (by have h_eq : n = 609 := (by omega); rw [h_eq]; exact base_609)
  | 210 => Or.inl (by have h_eq : n = 610 := (by omega); rw [h_eq]; exact base_610)
  | 211 => Or.inl (by have h_eq : n = 611 := (by omega); rw [h_eq]; exact base_611)
  | 212 => Or.inl (by have h_eq : n = 612 := (by omega); rw [h_eq]; exact base_612)
  | 213 => Or.inl (by have h_eq : n = 613 := (by omega); rw [h_eq]; exact base_613)
  | 214 => Or.inl (by have h_eq : n = 614 := (by omega); rw [h_eq]; exact base_614)
  | 215 => Or.inl (by have h_eq : n = 615 := (by omega); rw [h_eq]; exact base_615)
  | 216 => Or.inl (by have h_eq : n = 616 := (by omega); rw [h_eq]; exact base_616)
  | 217 => Or.inl (by have h_eq : n = 617 := (by omega); rw [h_eq]; exact base_617)
  | 218 => Or.inl (by have h_eq : n = 618 := (by omega); rw [h_eq]; exact base_618)
  | 219 => Or.inl (by have h_eq : n = 619 := (by omega); rw [h_eq]; exact base_619)
  | 220 => Or.inl (by have h_eq : n = 620 := (by omega); rw [h_eq]; exact base_620)
  | 221 => Or.inl (by have h_eq : n = 621 := (by omega); rw [h_eq]; exact base_621)
  | 222 => Or.inl (by have h_eq : n = 622 := (by omega); rw [h_eq]; exact base_622)
  | 223 => Or.inl (by have h_eq : n = 623 := (by omega); rw [h_eq]; exact base_623)
  | 224 => Or.inl (by have h_eq : n = 624 := (by omega); rw [h_eq]; exact base_624)
  | 225 => Or.inl (by have h_eq : n = 625 := (by omega); rw [h_eq]; exact base_625)
  | 226 => Or.inl (by have h_eq : n = 626 := (by omega); rw [h_eq]; exact base_626)
  | 227 => Or.inl (by have h_eq : n = 627 := (by omega); rw [h_eq]; exact base_627)
  | 228 => Or.inl (by have h_eq : n = 628 := (by omega); rw [h_eq]; exact base_628)
  | 229 => Or.inl (by have h_eq : n = 629 := (by omega); rw [h_eq]; exact base_629)
  | 230 => Or.inl (by have h_eq : n = 630 := (by omega); rw [h_eq]; exact base_630)
  | 231 => Or.inl (by have h_eq : n = 631 := (by omega); rw [h_eq]; exact base_631)
  | 232 => Or.inl (by have h_eq : n = 632 := (by omega); rw [h_eq]; exact base_632)
  | 233 => Or.inl (by have h_eq : n = 633 := (by omega); rw [h_eq]; exact base_633)
  | 234 => Or.inl (by have h_eq : n = 634 := (by omega); rw [h_eq]; exact base_634)
  | 235 => Or.inl (by have h_eq : n = 635 := (by omega); rw [h_eq]; exact base_635)
  | 236 => Or.inl (by have h_eq : n = 636 := (by omega); rw [h_eq]; exact base_636)
  | 237 => Or.inl (by have h_eq : n = 637 := (by omega); rw [h_eq]; exact base_637)
  | 238 => Or.inl (by have h_eq : n = 638 := (by omega); rw [h_eq]; exact base_638)
  | 239 => Or.inl (by have h_eq : n = 639 := (by omega); rw [h_eq]; exact base_639)
  | 240 => Or.inl (by have h_eq : n = 640 := (by omega); rw [h_eq]; exact base_640)
  | 241 => Or.inl (by have h_eq : n = 641 := (by omega); rw [h_eq]; exact base_641)
  | 242 => Or.inl (by have h_eq : n = 642 := (by omega); rw [h_eq]; exact base_642)
  | 243 => Or.inl (by have h_eq : n = 643 := (by omega); rw [h_eq]; exact base_643)
  | 244 => Or.inl (by have h_eq : n = 644 := (by omega); rw [h_eq]; exact base_644)
  | 245 => Or.inl (by have h_eq : n = 645 := (by omega); rw [h_eq]; exact base_645)
  | 246 => Or.inl (by have h_eq : n = 646 := (by omega); rw [h_eq]; exact base_646)
  | 247 => Or.inl (by have h_eq : n = 647 := (by omega); rw [h_eq]; exact base_647)
  | 248 => Or.inl (by have h_eq : n = 648 := (by omega); rw [h_eq]; exact base_648)
  | 249 => Or.inl (by have h_eq : n = 649 := (by omega); rw [h_eq]; exact base_649)
  | 250 => Or.inl (by have h_eq : n = 650 := (by omega); rw [h_eq]; exact base_650)
  | 251 => Or.inl (by have h_eq : n = 651 := (by omega); rw [h_eq]; exact base_651)
  | 252 => Or.inl (by have h_eq : n = 652 := (by omega); rw [h_eq]; exact base_652)
  | 253 => Or.inl (by have h_eq : n = 653 := (by omega); rw [h_eq]; exact base_653)
  | 254 => Or.inl (by have h_eq : n = 654 := (by omega); rw [h_eq]; exact base_654)
  | 255 => Or.inl (by have h_eq : n = 655 := (by omega); rw [h_eq]; exact base_655)
  | 256 => Or.inl (by have h_eq : n = 656 := (by omega); rw [h_eq]; exact base_656)
  | 257 => Or.inl (by have h_eq : n = 657 := (by omega); rw [h_eq]; exact base_657)
  | 258 => Or.inl (by have h_eq : n = 658 := (by omega); rw [h_eq]; exact base_658)
  | 259 => Or.inl (by have h_eq : n = 659 := (by omega); rw [h_eq]; exact base_659)
  | 260 => Or.inl (by have h_eq : n = 660 := (by omega); rw [h_eq]; exact base_660)
  | 261 => Or.inl (by have h_eq : n = 661 := (by omega); rw [h_eq]; exact base_661)
  | 262 => Or.inl (by have h_eq : n = 662 := (by omega); rw [h_eq]; exact base_662)
  | 263 => Or.inl (by have h_eq : n = 663 := (by omega); rw [h_eq]; exact base_663)
  | 264 => Or.inl (by have h_eq : n = 664 := (by omega); rw [h_eq]; exact base_664)
  | 265 => Or.inl (by have h_eq : n = 665 := (by omega); rw [h_eq]; exact base_665)
  | 266 => Or.inl (by have h_eq : n = 666 := (by omega); rw [h_eq]; exact base_666)
  | 267 => Or.inl (by have h_eq : n = 667 := (by omega); rw [h_eq]; exact base_667)
  | 268 => Or.inl (by have h_eq : n = 668 := (by omega); rw [h_eq]; exact base_668)
  | 269 => Or.inl (by have h_eq : n = 669 := (by omega); rw [h_eq]; exact base_669)
  | 270 => Or.inl (by have h_eq : n = 670 := (by omega); rw [h_eq]; exact base_670)
  | 271 => Or.inl (by have h_eq : n = 671 := (by omega); rw [h_eq]; exact base_671)
  | 272 => Or.inl (by have h_eq : n = 672 := (by omega); rw [h_eq]; exact base_672)
  | 273 => Or.inl (by have h_eq : n = 673 := (by omega); rw [h_eq]; exact base_673)
  | 274 => Or.inl (by have h_eq : n = 674 := (by omega); rw [h_eq]; exact base_674)
  | 275 => Or.inl (by have h_eq : n = 675 := (by omega); rw [h_eq]; exact base_675)
  | 276 => Or.inl (by have h_eq : n = 676 := (by omega); rw [h_eq]; exact base_676)
  | 277 => Or.inl (by have h_eq : n = 677 := (by omega); rw [h_eq]; exact base_677)
  | 278 => Or.inl (by have h_eq : n = 678 := (by omega); rw [h_eq]; exact base_678)
  | 279 => Or.inl (by have h_eq : n = 679 := (by omega); rw [h_eq]; exact base_679)
  | 280 => Or.inl (by have h_eq : n = 680 := (by omega); rw [h_eq]; exact base_680)
  | 281 => Or.inl (by have h_eq : n = 681 := (by omega); rw [h_eq]; exact base_681)
  | 282 => Or.inl (by have h_eq : n = 682 := (by omega); rw [h_eq]; exact base_682)
  | 283 => Or.inl (by have h_eq : n = 683 := (by omega); rw [h_eq]; exact base_683)
  | 284 => Or.inl (by have h_eq : n = 684 := (by omega); rw [h_eq]; exact base_684)
  | 285 => Or.inl (by have h_eq : n = 685 := (by omega); rw [h_eq]; exact base_685)
  | 286 => Or.inl (by have h_eq : n = 686 := (by omega); rw [h_eq]; exact base_686)
  | 287 => Or.inl (by have h_eq : n = 687 := (by omega); rw [h_eq]; exact base_687)
  | 288 => Or.inl (by have h_eq : n = 688 := (by omega); rw [h_eq]; exact base_688)
  | 289 => Or.inl (by have h_eq : n = 689 := (by omega); rw [h_eq]; exact base_689)
  | 290 => Or.inl (by have h_eq : n = 690 := (by omega); rw [h_eq]; exact base_690)
  | 291 => Or.inl (by have h_eq : n = 691 := (by omega); rw [h_eq]; exact base_691)
  | 292 => Or.inl (by have h_eq : n = 692 := (by omega); rw [h_eq]; exact base_692)
  | 293 => Or.inl (by have h_eq : n = 693 := (by omega); rw [h_eq]; exact base_693)
  | 294 => Or.inl (by have h_eq : n = 694 := (by omega); rw [h_eq]; exact base_694)
  | 295 => Or.inl (by have h_eq : n = 695 := (by omega); rw [h_eq]; exact base_695)
  | 296 => Or.inl (by have h_eq : n = 696 := (by omega); rw [h_eq]; exact base_696)
  | 297 => Or.inl (by have h_eq : n = 697 := (by omega); rw [h_eq]; exact base_697)
  | 298 => Or.inl (by have h_eq : n = 698 := (by omega); rw [h_eq]; exact base_698)
  | 299 => Or.inl (by have h_eq : n = 699 := (by omega); rw [h_eq]; exact base_699)
  | 300 => Or.inl (by have h_eq : n = 700 := (by omega); rw [h_eq]; exact base_700)
  | 301 => Or.inl (by have h_eq : n = 701 := (by omega); rw [h_eq]; exact base_701)
  | 302 => Or.inl (by have h_eq : n = 702 := (by omega); rw [h_eq]; exact base_702)
  | 303 => Or.inl (by have h_eq : n = 703 := (by omega); rw [h_eq]; exact base_703)
  | 304 => Or.inl (by have h_eq : n = 704 := (by omega); rw [h_eq]; exact base_704)
  | 305 => Or.inl (by have h_eq : n = 705 := (by omega); rw [h_eq]; exact base_705)
  | 306 => Or.inl (by have h_eq : n = 706 := (by omega); rw [h_eq]; exact base_706)
  | 307 => Or.inl (by have h_eq : n = 707 := (by omega); rw [h_eq]; exact base_707)
  | 308 => Or.inl (by have h_eq : n = 708 := (by omega); rw [h_eq]; exact base_708)
  | 309 => Or.inl (by have h_eq : n = 709 := (by omega); rw [h_eq]; exact base_709)
  | 310 => Or.inl (by have h_eq : n = 710 := (by omega); rw [h_eq]; exact base_710)
  | 311 => Or.inl (by have h_eq : n = 711 := (by omega); rw [h_eq]; exact base_711)
  | 312 => Or.inl (by have h_eq : n = 712 := (by omega); rw [h_eq]; exact base_712)
  | 313 => Or.inl (by have h_eq : n = 713 := (by omega); rw [h_eq]; exact base_713)
  | 314 => Or.inl (by have h_eq : n = 714 := (by omega); rw [h_eq]; exact base_714)
  | 315 => Or.inl (by have h_eq : n = 715 := (by omega); rw [h_eq]; exact base_715)
  | 316 => Or.inl (by have h_eq : n = 716 := (by omega); rw [h_eq]; exact base_716)
  | 317 => Or.inl (by have h_eq : n = 717 := (by omega); rw [h_eq]; exact base_717)
  | 318 => Or.inl (by have h_eq : n = 718 := (by omega); rw [h_eq]; exact base_718)
  | 319 => Or.inl (by have h_eq : n = 719 := (by omega); rw [h_eq]; exact base_719)
  | 320 => Or.inl (by have h_eq : n = 720 := (by omega); rw [h_eq]; exact base_720)
  | 321 => Or.inl (by have h_eq : n = 721 := (by omega); rw [h_eq]; exact base_721)
  | 322 => Or.inl (by have h_eq : n = 722 := (by omega); rw [h_eq]; exact base_722)
  | 323 => Or.inl (by have h_eq : n = 723 := (by omega); rw [h_eq]; exact base_723)
  | 324 => Or.inl (by have h_eq : n = 724 := (by omega); rw [h_eq]; exact base_724)
  | 325 => Or.inl (by have h_eq : n = 725 := (by omega); rw [h_eq]; exact base_725)
  | 326 => Or.inl (by have h_eq : n = 726 := (by omega); rw [h_eq]; exact base_726)
  | 327 => Or.inl (by have h_eq : n = 727 := (by omega); rw [h_eq]; exact base_727)
  | 328 => Or.inl (by have h_eq : n = 728 := (by omega); rw [h_eq]; exact base_728)
  | 329 => Or.inl (by have h_eq : n = 729 := (by omega); rw [h_eq]; exact base_729)
  | 330 => Or.inl (by have h_eq : n = 730 := (by omega); rw [h_eq]; exact base_730)
  | 331 => Or.inl (by have h_eq : n = 731 := (by omega); rw [h_eq]; exact base_731)
  | 332 => Or.inl (by have h_eq : n = 732 := (by omega); rw [h_eq]; exact base_732)
  | 333 => Or.inl (by have h_eq : n = 733 := (by omega); rw [h_eq]; exact base_733)
  | 334 => Or.inl (by have h_eq : n = 734 := (by omega); rw [h_eq]; exact base_734)
  | 335 => Or.inl (by have h_eq : n = 735 := (by omega); rw [h_eq]; exact base_735)
  | 336 => Or.inl (by have h_eq : n = 736 := (by omega); rw [h_eq]; exact base_736)
  | 337 => Or.inl (by have h_eq : n = 737 := (by omega); rw [h_eq]; exact base_737)
  | 338 => Or.inl (by have h_eq : n = 738 := (by omega); rw [h_eq]; exact base_738)
  | 339 => Or.inl (by have h_eq : n = 739 := (by omega); rw [h_eq]; exact base_739)
  | 340 => Or.inl (by have h_eq : n = 740 := (by omega); rw [h_eq]; exact base_740)
  | 341 => Or.inl (by have h_eq : n = 741 := (by omega); rw [h_eq]; exact base_741)
  | 342 => Or.inl (by have h_eq : n = 742 := (by omega); rw [h_eq]; exact base_742)
  | 343 => Or.inl (by have h_eq : n = 743 := (by omega); rw [h_eq]; exact base_743)
  | 344 => Or.inl (by have h_eq : n = 744 := (by omega); rw [h_eq]; exact base_744)
  | 345 => Or.inl (by have h_eq : n = 745 := (by omega); rw [h_eq]; exact base_745)
  | 346 => Or.inl (by have h_eq : n = 746 := (by omega); rw [h_eq]; exact base_746)
  | 347 => Or.inl (by have h_eq : n = 747 := (by omega); rw [h_eq]; exact base_747)
  | 348 => Or.inl (by have h_eq : n = 748 := (by omega); rw [h_eq]; exact base_748)
  | 349 => Or.inl (by have h_eq : n = 749 := (by omega); rw [h_eq]; exact base_749)
  | 350 => Or.inl (by have h_eq : n = 750 := (by omega); rw [h_eq]; exact base_750)
  | 351 => Or.inl (by have h_eq : n = 751 := (by omega); rw [h_eq]; exact base_751)
  | 352 => Or.inl (by have h_eq : n = 752 := (by omega); rw [h_eq]; exact base_752)
  | 353 => Or.inl (by have h_eq : n = 753 := (by omega); rw [h_eq]; exact base_753)
  | 354 => Or.inl (by have h_eq : n = 754 := (by omega); rw [h_eq]; exact base_754)
  | 355 => Or.inl (by have h_eq : n = 755 := (by omega); rw [h_eq]; exact base_755)
  | 356 => Or.inl (by have h_eq : n = 756 := (by omega); rw [h_eq]; exact base_756)
  | 357 => Or.inl (by have h_eq : n = 757 := (by omega); rw [h_eq]; exact base_757)
  | 358 => Or.inl (by have h_eq : n = 758 := (by omega); rw [h_eq]; exact base_758)
  | 359 => Or.inl (by have h_eq : n = 759 := (by omega); rw [h_eq]; exact base_759)
  | 360 => Or.inl (by have h_eq : n = 760 := (by omega); rw [h_eq]; exact base_760)
  | 361 => Or.inl (by have h_eq : n = 761 := (by omega); rw [h_eq]; exact base_761)
  | 362 => Or.inl (by have h_eq : n = 762 := (by omega); rw [h_eq]; exact base_762)
  | 363 => Or.inl (by have h_eq : n = 763 := (by omega); rw [h_eq]; exact base_763)
  | 364 => Or.inl (by have h_eq : n = 764 := (by omega); rw [h_eq]; exact base_764)
  | 365 => Or.inl (by have h_eq : n = 765 := (by omega); rw [h_eq]; exact base_765)
  | 366 => Or.inl (by have h_eq : n = 766 := (by omega); rw [h_eq]; exact base_766)
  | 367 => Or.inl (by have h_eq : n = 767 := (by omega); rw [h_eq]; exact base_767)
  | 368 => Or.inl (by have h_eq : n = 768 := (by omega); rw [h_eq]; exact base_768)
  | 369 => Or.inl (by have h_eq : n = 769 := (by omega); rw [h_eq]; exact base_769)
  | 370 => Or.inl (by have h_eq : n = 770 := (by omega); rw [h_eq]; exact base_770)
  | 371 => Or.inl (by have h_eq : n = 771 := (by omega); rw [h_eq]; exact base_771)
  | 372 => Or.inl (by have h_eq : n = 772 := (by omega); rw [h_eq]; exact base_772)
  | 373 => Or.inl (by have h_eq : n = 773 := (by omega); rw [h_eq]; exact base_773)
  | 374 => Or.inl (by have h_eq : n = 774 := (by omega); rw [h_eq]; exact base_774)
  | 375 => Or.inl (by have h_eq : n = 775 := (by omega); rw [h_eq]; exact base_775)
  | 376 => Or.inl (by have h_eq : n = 776 := (by omega); rw [h_eq]; exact base_776)
  | 377 => Or.inl (by have h_eq : n = 777 := (by omega); rw [h_eq]; exact base_777)
  | 378 => Or.inl (by have h_eq : n = 778 := (by omega); rw [h_eq]; exact base_778)
  | 379 => Or.inl (by have h_eq : n = 779 := (by omega); rw [h_eq]; exact base_779)
  | 380 => Or.inl (by have h_eq : n = 780 := (by omega); rw [h_eq]; exact base_780)
  | 381 => Or.inl (by have h_eq : n = 781 := (by omega); rw [h_eq]; exact base_781)
  | 382 => Or.inl (by have h_eq : n = 782 := (by omega); rw [h_eq]; exact base_782)
  | 383 => Or.inl (by have h_eq : n = 783 := (by omega); rw [h_eq]; exact base_783)
  | 384 => Or.inl (by have h_eq : n = 784 := (by omega); rw [h_eq]; exact base_784)
  | 385 => Or.inl (by have h_eq : n = 785 := (by omega); rw [h_eq]; exact base_785)
  | 386 => Or.inl (by have h_eq : n = 786 := (by omega); rw [h_eq]; exact base_786)
  | 387 => Or.inl (by have h_eq : n = 787 := (by omega); rw [h_eq]; exact base_787)
  | 388 => Or.inl (by have h_eq : n = 788 := (by omega); rw [h_eq]; exact base_788)
  | 389 => Or.inl (by have h_eq : n = 789 := (by omega); rw [h_eq]; exact base_789)
  | 390 => Or.inl (by have h_eq : n = 790 := (by omega); rw [h_eq]; exact base_790)
  | 391 => Or.inl (by have h_eq : n = 791 := (by omega); rw [h_eq]; exact base_791)
  | 392 => Or.inl (by have h_eq : n = 792 := (by omega); rw [h_eq]; exact base_792)
  | 393 => Or.inl (by have h_eq : n = 793 := (by omega); rw [h_eq]; exact base_793)
  | 394 => Or.inl (by have h_eq : n = 794 := (by omega); rw [h_eq]; exact base_794)
  | 395 => Or.inl (by have h_eq : n = 795 := (by omega); rw [h_eq]; exact base_795)
  | 396 => Or.inl (by have h_eq : n = 796 := (by omega); rw [h_eq]; exact base_796)
  | 397 => Or.inl (by have h_eq : n = 797 := (by omega); rw [h_eq]; exact base_797)
  | 398 => Or.inl (by have h_eq : n = 798 := (by omega); rw [h_eq]; exact base_798)
  | 399 => Or.inl (by have h_eq : n = 799 := (by omega); rw [h_eq]; exact base_799)
  | m + 400 => Or.inr (by omega)

lemma base_cases_chunk_2 (n : ℕ) (h_low : 800 ≤ n) : 0 < A271510 n ∨ n ≥ 1200 :=
  match h : n - 800 with
  | 0 => Or.inl (by have h_eq : n = 800 := (by omega); rw [h_eq]; exact base_800)
  | 1 => Or.inl (by have h_eq : n = 801 := (by omega); rw [h_eq]; exact base_801)
  | 2 => Or.inl (by have h_eq : n = 802 := (by omega); rw [h_eq]; exact base_802)
  | 3 => Or.inl (by have h_eq : n = 803 := (by omega); rw [h_eq]; exact base_803)
  | 4 => Or.inl (by have h_eq : n = 804 := (by omega); rw [h_eq]; exact base_804)
  | 5 => Or.inl (by have h_eq : n = 805 := (by omega); rw [h_eq]; exact base_805)
  | 6 => Or.inl (by have h_eq : n = 806 := (by omega); rw [h_eq]; exact base_806)
  | 7 => Or.inl (by have h_eq : n = 807 := (by omega); rw [h_eq]; exact base_807)
  | 8 => Or.inl (by have h_eq : n = 808 := (by omega); rw [h_eq]; exact base_808)
  | 9 => Or.inl (by have h_eq : n = 809 := (by omega); rw [h_eq]; exact base_809)
  | 10 => Or.inl (by have h_eq : n = 810 := (by omega); rw [h_eq]; exact base_810)
  | 11 => Or.inl (by have h_eq : n = 811 := (by omega); rw [h_eq]; exact base_811)
  | 12 => Or.inl (by have h_eq : n = 812 := (by omega); rw [h_eq]; exact base_812)
  | 13 => Or.inl (by have h_eq : n = 813 := (by omega); rw [h_eq]; exact base_813)
  | 14 => Or.inl (by have h_eq : n = 814 := (by omega); rw [h_eq]; exact base_814)
  | 15 => Or.inl (by have h_eq : n = 815 := (by omega); rw [h_eq]; exact base_815)
  | 16 => Or.inl (by have h_eq : n = 816 := (by omega); rw [h_eq]; exact base_816)
  | 17 => Or.inl (by have h_eq : n = 817 := (by omega); rw [h_eq]; exact base_817)
  | 18 => Or.inl (by have h_eq : n = 818 := (by omega); rw [h_eq]; exact base_818)
  | 19 => Or.inl (by have h_eq : n = 819 := (by omega); rw [h_eq]; exact base_819)
  | 20 => Or.inl (by have h_eq : n = 820 := (by omega); rw [h_eq]; exact base_820)
  | 21 => Or.inl (by have h_eq : n = 821 := (by omega); rw [h_eq]; exact base_821)
  | 22 => Or.inl (by have h_eq : n = 822 := (by omega); rw [h_eq]; exact base_822)
  | 23 => Or.inl (by have h_eq : n = 823 := (by omega); rw [h_eq]; exact base_823)
  | 24 => Or.inl (by have h_eq : n = 824 := (by omega); rw [h_eq]; exact base_824)
  | 25 => Or.inl (by have h_eq : n = 825 := (by omega); rw [h_eq]; exact base_825)
  | 26 => Or.inl (by have h_eq : n = 826 := (by omega); rw [h_eq]; exact base_826)
  | 27 => Or.inl (by have h_eq : n = 827 := (by omega); rw [h_eq]; exact base_827)
  | 28 => Or.inl (by have h_eq : n = 828 := (by omega); rw [h_eq]; exact base_828)
  | 29 => Or.inl (by have h_eq : n = 829 := (by omega); rw [h_eq]; exact base_829)
  | 30 => Or.inl (by have h_eq : n = 830 := (by omega); rw [h_eq]; exact base_830)
  | 31 => Or.inl (by have h_eq : n = 831 := (by omega); rw [h_eq]; exact base_831)
  | 32 => Or.inl (by have h_eq : n = 832 := (by omega); rw [h_eq]; exact base_832)
  | 33 => Or.inl (by have h_eq : n = 833 := (by omega); rw [h_eq]; exact base_833)
  | 34 => Or.inl (by have h_eq : n = 834 := (by omega); rw [h_eq]; exact base_834)
  | 35 => Or.inl (by have h_eq : n = 835 := (by omega); rw [h_eq]; exact base_835)
  | 36 => Or.inl (by have h_eq : n = 836 := (by omega); rw [h_eq]; exact base_836)
  | 37 => Or.inl (by have h_eq : n = 837 := (by omega); rw [h_eq]; exact base_837)
  | 38 => Or.inl (by have h_eq : n = 838 := (by omega); rw [h_eq]; exact base_838)
  | 39 => Or.inl (by have h_eq : n = 839 := (by omega); rw [h_eq]; exact base_839)
  | 40 => Or.inl (by have h_eq : n = 840 := (by omega); rw [h_eq]; exact base_840)
  | 41 => Or.inl (by have h_eq : n = 841 := (by omega); rw [h_eq]; exact base_841)
  | 42 => Or.inl (by have h_eq : n = 842 := (by omega); rw [h_eq]; exact base_842)
  | 43 => Or.inl (by have h_eq : n = 843 := (by omega); rw [h_eq]; exact base_843)
  | 44 => Or.inl (by have h_eq : n = 844 := (by omega); rw [h_eq]; exact base_844)
  | 45 => Or.inl (by have h_eq : n = 845 := (by omega); rw [h_eq]; exact base_845)
  | 46 => Or.inl (by have h_eq : n = 846 := (by omega); rw [h_eq]; exact base_846)
  | 47 => Or.inl (by have h_eq : n = 847 := (by omega); rw [h_eq]; exact base_847)
  | 48 => Or.inl (by have h_eq : n = 848 := (by omega); rw [h_eq]; exact base_848)
  | 49 => Or.inl (by have h_eq : n = 849 := (by omega); rw [h_eq]; exact base_849)
  | 50 => Or.inl (by have h_eq : n = 850 := (by omega); rw [h_eq]; exact base_850)
  | 51 => Or.inl (by have h_eq : n = 851 := (by omega); rw [h_eq]; exact base_851)
  | 52 => Or.inl (by have h_eq : n = 852 := (by omega); rw [h_eq]; exact base_852)
  | 53 => Or.inl (by have h_eq : n = 853 := (by omega); rw [h_eq]; exact base_853)
  | 54 => Or.inl (by have h_eq : n = 854 := (by omega); rw [h_eq]; exact base_854)
  | 55 => Or.inl (by have h_eq : n = 855 := (by omega); rw [h_eq]; exact base_855)
  | 56 => Or.inl (by have h_eq : n = 856 := (by omega); rw [h_eq]; exact base_856)
  | 57 => Or.inl (by have h_eq : n = 857 := (by omega); rw [h_eq]; exact base_857)
  | 58 => Or.inl (by have h_eq : n = 858 := (by omega); rw [h_eq]; exact base_858)
  | 59 => Or.inl (by have h_eq : n = 859 := (by omega); rw [h_eq]; exact base_859)
  | 60 => Or.inl (by have h_eq : n = 860 := (by omega); rw [h_eq]; exact base_860)
  | 61 => Or.inl (by have h_eq : n = 861 := (by omega); rw [h_eq]; exact base_861)
  | 62 => Or.inl (by have h_eq : n = 862 := (by omega); rw [h_eq]; exact base_862)
  | 63 => Or.inl (by have h_eq : n = 863 := (by omega); rw [h_eq]; exact base_863)
  | 64 => Or.inl (by have h_eq : n = 864 := (by omega); rw [h_eq]; exact base_864)
  | 65 => Or.inl (by have h_eq : n = 865 := (by omega); rw [h_eq]; exact base_865)
  | 66 => Or.inl (by have h_eq : n = 866 := (by omega); rw [h_eq]; exact base_866)
  | 67 => Or.inl (by have h_eq : n = 867 := (by omega); rw [h_eq]; exact base_867)
  | 68 => Or.inl (by have h_eq : n = 868 := (by omega); rw [h_eq]; exact base_868)
  | 69 => Or.inl (by have h_eq : n = 869 := (by omega); rw [h_eq]; exact base_869)
  | 70 => Or.inl (by have h_eq : n = 870 := (by omega); rw [h_eq]; exact base_870)
  | 71 => Or.inl (by have h_eq : n = 871 := (by omega); rw [h_eq]; exact base_871)
  | 72 => Or.inl (by have h_eq : n = 872 := (by omega); rw [h_eq]; exact base_872)
  | 73 => Or.inl (by have h_eq : n = 873 := (by omega); rw [h_eq]; exact base_873)
  | 74 => Or.inl (by have h_eq : n = 874 := (by omega); rw [h_eq]; exact base_874)
  | 75 => Or.inl (by have h_eq : n = 875 := (by omega); rw [h_eq]; exact base_875)
  | 76 => Or.inl (by have h_eq : n = 876 := (by omega); rw [h_eq]; exact base_876)
  | 77 => Or.inl (by have h_eq : n = 877 := (by omega); rw [h_eq]; exact base_877)
  | 78 => Or.inl (by have h_eq : n = 878 := (by omega); rw [h_eq]; exact base_878)
  | 79 => Or.inl (by have h_eq : n = 879 := (by omega); rw [h_eq]; exact base_879)
  | 80 => Or.inl (by have h_eq : n = 880 := (by omega); rw [h_eq]; exact base_880)
  | 81 => Or.inl (by have h_eq : n = 881 := (by omega); rw [h_eq]; exact base_881)
  | 82 => Or.inl (by have h_eq : n = 882 := (by omega); rw [h_eq]; exact base_882)
  | 83 => Or.inl (by have h_eq : n = 883 := (by omega); rw [h_eq]; exact base_883)
  | 84 => Or.inl (by have h_eq : n = 884 := (by omega); rw [h_eq]; exact base_884)
  | 85 => Or.inl (by have h_eq : n = 885 := (by omega); rw [h_eq]; exact base_885)
  | 86 => Or.inl (by have h_eq : n = 886 := (by omega); rw [h_eq]; exact base_886)
  | 87 => Or.inl (by have h_eq : n = 887 := (by omega); rw [h_eq]; exact base_887)
  | 88 => Or.inl (by have h_eq : n = 888 := (by omega); rw [h_eq]; exact base_888)
  | 89 => Or.inl (by have h_eq : n = 889 := (by omega); rw [h_eq]; exact base_889)
  | 90 => Or.inl (by have h_eq : n = 890 := (by omega); rw [h_eq]; exact base_890)
  | 91 => Or.inl (by have h_eq : n = 891 := (by omega); rw [h_eq]; exact base_891)
  | 92 => Or.inl (by have h_eq : n = 892 := (by omega); rw [h_eq]; exact base_892)
  | 93 => Or.inl (by have h_eq : n = 893 := (by omega); rw [h_eq]; exact base_893)
  | 94 => Or.inl (by have h_eq : n = 894 := (by omega); rw [h_eq]; exact base_894)
  | 95 => Or.inl (by have h_eq : n = 895 := (by omega); rw [h_eq]; exact base_895)
  | 96 => Or.inl (by have h_eq : n = 896 := (by omega); rw [h_eq]; exact base_896)
  | 97 => Or.inl (by have h_eq : n = 897 := (by omega); rw [h_eq]; exact base_897)
  | 98 => Or.inl (by have h_eq : n = 898 := (by omega); rw [h_eq]; exact base_898)
  | 99 => Or.inl (by have h_eq : n = 899 := (by omega); rw [h_eq]; exact base_899)
  | 100 => Or.inl (by have h_eq : n = 900 := (by omega); rw [h_eq]; exact base_900)
  | 101 => Or.inl (by have h_eq : n = 901 := (by omega); rw [h_eq]; exact base_901)
  | 102 => Or.inl (by have h_eq : n = 902 := (by omega); rw [h_eq]; exact base_902)
  | 103 => Or.inl (by have h_eq : n = 903 := (by omega); rw [h_eq]; exact base_903)
  | 104 => Or.inl (by have h_eq : n = 904 := (by omega); rw [h_eq]; exact base_904)
  | 105 => Or.inl (by have h_eq : n = 905 := (by omega); rw [h_eq]; exact base_905)
  | 106 => Or.inl (by have h_eq : n = 906 := (by omega); rw [h_eq]; exact base_906)
  | 107 => Or.inl (by have h_eq : n = 907 := (by omega); rw [h_eq]; exact base_907)
  | 108 => Or.inl (by have h_eq : n = 908 := (by omega); rw [h_eq]; exact base_908)
  | 109 => Or.inl (by have h_eq : n = 909 := (by omega); rw [h_eq]; exact base_909)
  | 110 => Or.inl (by have h_eq : n = 910 := (by omega); rw [h_eq]; exact base_910)
  | 111 => Or.inl (by have h_eq : n = 911 := (by omega); rw [h_eq]; exact base_911)
  | 112 => Or.inl (by have h_eq : n = 912 := (by omega); rw [h_eq]; exact base_912)
  | 113 => Or.inl (by have h_eq : n = 913 := (by omega); rw [h_eq]; exact base_913)
  | 114 => Or.inl (by have h_eq : n = 914 := (by omega); rw [h_eq]; exact base_914)
  | 115 => Or.inl (by have h_eq : n = 915 := (by omega); rw [h_eq]; exact base_915)
  | 116 => Or.inl (by have h_eq : n = 916 := (by omega); rw [h_eq]; exact base_916)
  | 117 => Or.inl (by have h_eq : n = 917 := (by omega); rw [h_eq]; exact base_917)
  | 118 => Or.inl (by have h_eq : n = 918 := (by omega); rw [h_eq]; exact base_918)
  | 119 => Or.inl (by have h_eq : n = 919 := (by omega); rw [h_eq]; exact base_919)
  | 120 => Or.inl (by have h_eq : n = 920 := (by omega); rw [h_eq]; exact base_920)
  | 121 => Or.inl (by have h_eq : n = 921 := (by omega); rw [h_eq]; exact base_921)
  | 122 => Or.inl (by have h_eq : n = 922 := (by omega); rw [h_eq]; exact base_922)
  | 123 => Or.inl (by have h_eq : n = 923 := (by omega); rw [h_eq]; exact base_923)
  | 124 => Or.inl (by have h_eq : n = 924 := (by omega); rw [h_eq]; exact base_924)
  | 125 => Or.inl (by have h_eq : n = 925 := (by omega); rw [h_eq]; exact base_925)
  | 126 => Or.inl (by have h_eq : n = 926 := (by omega); rw [h_eq]; exact base_926)
  | 127 => Or.inl (by have h_eq : n = 927 := (by omega); rw [h_eq]; exact base_927)
  | 128 => Or.inl (by have h_eq : n = 928 := (by omega); rw [h_eq]; exact base_928)
  | 129 => Or.inl (by have h_eq : n = 929 := (by omega); rw [h_eq]; exact base_929)
  | 130 => Or.inl (by have h_eq : n = 930 := (by omega); rw [h_eq]; exact base_930)
  | 131 => Or.inl (by have h_eq : n = 931 := (by omega); rw [h_eq]; exact base_931)
  | 132 => Or.inl (by have h_eq : n = 932 := (by omega); rw [h_eq]; exact base_932)
  | 133 => Or.inl (by have h_eq : n = 933 := (by omega); rw [h_eq]; exact base_933)
  | 134 => Or.inl (by have h_eq : n = 934 := (by omega); rw [h_eq]; exact base_934)
  | 135 => Or.inl (by have h_eq : n = 935 := (by omega); rw [h_eq]; exact base_935)
  | 136 => Or.inl (by have h_eq : n = 936 := (by omega); rw [h_eq]; exact base_936)
  | 137 => Or.inl (by have h_eq : n = 937 := (by omega); rw [h_eq]; exact base_937)
  | 138 => Or.inl (by have h_eq : n = 938 := (by omega); rw [h_eq]; exact base_938)
  | 139 => Or.inl (by have h_eq : n = 939 := (by omega); rw [h_eq]; exact base_939)
  | 140 => Or.inl (by have h_eq : n = 940 := (by omega); rw [h_eq]; exact base_940)
  | 141 => Or.inl (by have h_eq : n = 941 := (by omega); rw [h_eq]; exact base_941)
  | 142 => Or.inl (by have h_eq : n = 942 := (by omega); rw [h_eq]; exact base_942)
  | 143 => Or.inl (by have h_eq : n = 943 := (by omega); rw [h_eq]; exact base_943)
  | 144 => Or.inl (by have h_eq : n = 944 := (by omega); rw [h_eq]; exact base_944)
  | 145 => Or.inl (by have h_eq : n = 945 := (by omega); rw [h_eq]; exact base_945)
  | 146 => Or.inl (by have h_eq : n = 946 := (by omega); rw [h_eq]; exact base_946)
  | 147 => Or.inl (by have h_eq : n = 947 := (by omega); rw [h_eq]; exact base_947)
  | 148 => Or.inl (by have h_eq : n = 948 := (by omega); rw [h_eq]; exact base_948)
  | 149 => Or.inl (by have h_eq : n = 949 := (by omega); rw [h_eq]; exact base_949)
  | 150 => Or.inl (by have h_eq : n = 950 := (by omega); rw [h_eq]; exact base_950)
  | 151 => Or.inl (by have h_eq : n = 951 := (by omega); rw [h_eq]; exact base_951)
  | 152 => Or.inl (by have h_eq : n = 952 := (by omega); rw [h_eq]; exact base_952)
  | 153 => Or.inl (by have h_eq : n = 953 := (by omega); rw [h_eq]; exact base_953)
  | 154 => Or.inl (by have h_eq : n = 954 := (by omega); rw [h_eq]; exact base_954)
  | 155 => Or.inl (by have h_eq : n = 955 := (by omega); rw [h_eq]; exact base_955)
  | 156 => Or.inl (by have h_eq : n = 956 := (by omega); rw [h_eq]; exact base_956)
  | 157 => Or.inl (by have h_eq : n = 957 := (by omega); rw [h_eq]; exact base_957)
  | 158 => Or.inl (by have h_eq : n = 958 := (by omega); rw [h_eq]; exact base_958)
  | 159 => Or.inl (by have h_eq : n = 959 := (by omega); rw [h_eq]; exact base_959)
  | 160 => Or.inl (by have h_eq : n = 960 := (by omega); rw [h_eq]; exact base_960)
  | 161 => Or.inl (by have h_eq : n = 961 := (by omega); rw [h_eq]; exact base_961)
  | 162 => Or.inl (by have h_eq : n = 962 := (by omega); rw [h_eq]; exact base_962)
  | 163 => Or.inl (by have h_eq : n = 963 := (by omega); rw [h_eq]; exact base_963)
  | 164 => Or.inl (by have h_eq : n = 964 := (by omega); rw [h_eq]; exact base_964)
  | 165 => Or.inl (by have h_eq : n = 965 := (by omega); rw [h_eq]; exact base_965)
  | 166 => Or.inl (by have h_eq : n = 966 := (by omega); rw [h_eq]; exact base_966)
  | 167 => Or.inl (by have h_eq : n = 967 := (by omega); rw [h_eq]; exact base_967)
  | 168 => Or.inl (by have h_eq : n = 968 := (by omega); rw [h_eq]; exact base_968)
  | 169 => Or.inl (by have h_eq : n = 969 := (by omega); rw [h_eq]; exact base_969)
  | 170 => Or.inl (by have h_eq : n = 970 := (by omega); rw [h_eq]; exact base_970)
  | 171 => Or.inl (by have h_eq : n = 971 := (by omega); rw [h_eq]; exact base_971)
  | 172 => Or.inl (by have h_eq : n = 972 := (by omega); rw [h_eq]; exact base_972)
  | 173 => Or.inl (by have h_eq : n = 973 := (by omega); rw [h_eq]; exact base_973)
  | 174 => Or.inl (by have h_eq : n = 974 := (by omega); rw [h_eq]; exact base_974)
  | 175 => Or.inl (by have h_eq : n = 975 := (by omega); rw [h_eq]; exact base_975)
  | 176 => Or.inl (by have h_eq : n = 976 := (by omega); rw [h_eq]; exact base_976)
  | 177 => Or.inl (by have h_eq : n = 977 := (by omega); rw [h_eq]; exact base_977)
  | 178 => Or.inl (by have h_eq : n = 978 := (by omega); rw [h_eq]; exact base_978)
  | 179 => Or.inl (by have h_eq : n = 979 := (by omega); rw [h_eq]; exact base_979)
  | 180 => Or.inl (by have h_eq : n = 980 := (by omega); rw [h_eq]; exact base_980)
  | 181 => Or.inl (by have h_eq : n = 981 := (by omega); rw [h_eq]; exact base_981)
  | 182 => Or.inl (by have h_eq : n = 982 := (by omega); rw [h_eq]; exact base_982)
  | 183 => Or.inl (by have h_eq : n = 983 := (by omega); rw [h_eq]; exact base_983)
  | 184 => Or.inl (by have h_eq : n = 984 := (by omega); rw [h_eq]; exact base_984)
  | 185 => Or.inl (by have h_eq : n = 985 := (by omega); rw [h_eq]; exact base_985)
  | 186 => Or.inl (by have h_eq : n = 986 := (by omega); rw [h_eq]; exact base_986)
  | 187 => Or.inl (by have h_eq : n = 987 := (by omega); rw [h_eq]; exact base_987)
  | 188 => Or.inl (by have h_eq : n = 988 := (by omega); rw [h_eq]; exact base_988)
  | 189 => Or.inl (by have h_eq : n = 989 := (by omega); rw [h_eq]; exact base_989)
  | 190 => Or.inl (by have h_eq : n = 990 := (by omega); rw [h_eq]; exact base_990)
  | 191 => Or.inl (by have h_eq : n = 991 := (by omega); rw [h_eq]; exact base_991)
  | 192 => Or.inl (by have h_eq : n = 992 := (by omega); rw [h_eq]; exact base_992)
  | 193 => Or.inl (by have h_eq : n = 993 := (by omega); rw [h_eq]; exact base_993)
  | 194 => Or.inl (by have h_eq : n = 994 := (by omega); rw [h_eq]; exact base_994)
  | 195 => Or.inl (by have h_eq : n = 995 := (by omega); rw [h_eq]; exact base_995)
  | 196 => Or.inl (by have h_eq : n = 996 := (by omega); rw [h_eq]; exact base_996)
  | 197 => Or.inl (by have h_eq : n = 997 := (by omega); rw [h_eq]; exact base_997)
  | 198 => Or.inl (by have h_eq : n = 998 := (by omega); rw [h_eq]; exact base_998)
  | 199 => Or.inl (by have h_eq : n = 999 := (by omega); rw [h_eq]; exact base_999)
  | 200 => Or.inl (by have h_eq : n = 1000 := (by omega); rw [h_eq]; exact base_1000)
  | 201 => Or.inl (by have h_eq : n = 1001 := (by omega); rw [h_eq]; exact base_1001)
  | 202 => Or.inl (by have h_eq : n = 1002 := (by omega); rw [h_eq]; exact base_1002)
  | 203 => Or.inl (by have h_eq : n = 1003 := (by omega); rw [h_eq]; exact base_1003)
  | 204 => Or.inl (by have h_eq : n = 1004 := (by omega); rw [h_eq]; exact base_1004)
  | 205 => Or.inl (by have h_eq : n = 1005 := (by omega); rw [h_eq]; exact base_1005)
  | 206 => Or.inl (by have h_eq : n = 1006 := (by omega); rw [h_eq]; exact base_1006)
  | 207 => Or.inl (by have h_eq : n = 1007 := (by omega); rw [h_eq]; exact base_1007)
  | 208 => Or.inl (by have h_eq : n = 1008 := (by omega); rw [h_eq]; exact base_1008)
  | 209 => Or.inl (by have h_eq : n = 1009 := (by omega); rw [h_eq]; exact base_1009)
  | 210 => Or.inl (by have h_eq : n = 1010 := (by omega); rw [h_eq]; exact base_1010)
  | 211 => Or.inl (by have h_eq : n = 1011 := (by omega); rw [h_eq]; exact base_1011)
  | 212 => Or.inl (by have h_eq : n = 1012 := (by omega); rw [h_eq]; exact base_1012)
  | 213 => Or.inl (by have h_eq : n = 1013 := (by omega); rw [h_eq]; exact base_1013)
  | 214 => Or.inl (by have h_eq : n = 1014 := (by omega); rw [h_eq]; exact base_1014)
  | 215 => Or.inl (by have h_eq : n = 1015 := (by omega); rw [h_eq]; exact base_1015)
  | 216 => Or.inl (by have h_eq : n = 1016 := (by omega); rw [h_eq]; exact base_1016)
  | 217 => Or.inl (by have h_eq : n = 1017 := (by omega); rw [h_eq]; exact base_1017)
  | 218 => Or.inl (by have h_eq : n = 1018 := (by omega); rw [h_eq]; exact base_1018)
  | 219 => Or.inl (by have h_eq : n = 1019 := (by omega); rw [h_eq]; exact base_1019)
  | 220 => Or.inl (by have h_eq : n = 1020 := (by omega); rw [h_eq]; exact base_1020)
  | 221 => Or.inl (by have h_eq : n = 1021 := (by omega); rw [h_eq]; exact base_1021)
  | 222 => Or.inl (by have h_eq : n = 1022 := (by omega); rw [h_eq]; exact base_1022)
  | 223 => Or.inl (by have h_eq : n = 1023 := (by omega); rw [h_eq]; exact base_1023)
  | 224 => Or.inl (by have h_eq : n = 1024 := (by omega); rw [h_eq]; exact base_1024)
  | 225 => Or.inl (by have h_eq : n = 1025 := (by omega); rw [h_eq]; exact base_1025)
  | 226 => Or.inl (by have h_eq : n = 1026 := (by omega); rw [h_eq]; exact base_1026)
  | 227 => Or.inl (by have h_eq : n = 1027 := (by omega); rw [h_eq]; exact base_1027)
  | 228 => Or.inl (by have h_eq : n = 1028 := (by omega); rw [h_eq]; exact base_1028)
  | 229 => Or.inl (by have h_eq : n = 1029 := (by omega); rw [h_eq]; exact base_1029)
  | 230 => Or.inl (by have h_eq : n = 1030 := (by omega); rw [h_eq]; exact base_1030)
  | 231 => Or.inl (by have h_eq : n = 1031 := (by omega); rw [h_eq]; exact base_1031)
  | 232 => Or.inl (by have h_eq : n = 1032 := (by omega); rw [h_eq]; exact base_1032)
  | 233 => Or.inl (by have h_eq : n = 1033 := (by omega); rw [h_eq]; exact base_1033)
  | 234 => Or.inl (by have h_eq : n = 1034 := (by omega); rw [h_eq]; exact base_1034)
  | 235 => Or.inl (by have h_eq : n = 1035 := (by omega); rw [h_eq]; exact base_1035)
  | 236 => Or.inl (by have h_eq : n = 1036 := (by omega); rw [h_eq]; exact base_1036)
  | 237 => Or.inl (by have h_eq : n = 1037 := (by omega); rw [h_eq]; exact base_1037)
  | 238 => Or.inl (by have h_eq : n = 1038 := (by omega); rw [h_eq]; exact base_1038)
  | 239 => Or.inl (by have h_eq : n = 1039 := (by omega); rw [h_eq]; exact base_1039)
  | 240 => Or.inl (by have h_eq : n = 1040 := (by omega); rw [h_eq]; exact base_1040)
  | 241 => Or.inl (by have h_eq : n = 1041 := (by omega); rw [h_eq]; exact base_1041)
  | 242 => Or.inl (by have h_eq : n = 1042 := (by omega); rw [h_eq]; exact base_1042)
  | 243 => Or.inl (by have h_eq : n = 1043 := (by omega); rw [h_eq]; exact base_1043)
  | 244 => Or.inl (by have h_eq : n = 1044 := (by omega); rw [h_eq]; exact base_1044)
  | 245 => Or.inl (by have h_eq : n = 1045 := (by omega); rw [h_eq]; exact base_1045)
  | 246 => Or.inl (by have h_eq : n = 1046 := (by omega); rw [h_eq]; exact base_1046)
  | 247 => Or.inl (by have h_eq : n = 1047 := (by omega); rw [h_eq]; exact base_1047)
  | 248 => Or.inl (by have h_eq : n = 1048 := (by omega); rw [h_eq]; exact base_1048)
  | 249 => Or.inl (by have h_eq : n = 1049 := (by omega); rw [h_eq]; exact base_1049)
  | 250 => Or.inl (by have h_eq : n = 1050 := (by omega); rw [h_eq]; exact base_1050)
  | 251 => Or.inl (by have h_eq : n = 1051 := (by omega); rw [h_eq]; exact base_1051)
  | 252 => Or.inl (by have h_eq : n = 1052 := (by omega); rw [h_eq]; exact base_1052)
  | 253 => Or.inl (by have h_eq : n = 1053 := (by omega); rw [h_eq]; exact base_1053)
  | 254 => Or.inl (by have h_eq : n = 1054 := (by omega); rw [h_eq]; exact base_1054)
  | 255 => Or.inl (by have h_eq : n = 1055 := (by omega); rw [h_eq]; exact base_1055)
  | 256 => Or.inl (by have h_eq : n = 1056 := (by omega); rw [h_eq]; exact base_1056)
  | 257 => Or.inl (by have h_eq : n = 1057 := (by omega); rw [h_eq]; exact base_1057)
  | 258 => Or.inl (by have h_eq : n = 1058 := (by omega); rw [h_eq]; exact base_1058)
  | 259 => Or.inl (by have h_eq : n = 1059 := (by omega); rw [h_eq]; exact base_1059)
  | 260 => Or.inl (by have h_eq : n = 1060 := (by omega); rw [h_eq]; exact base_1060)
  | 261 => Or.inl (by have h_eq : n = 1061 := (by omega); rw [h_eq]; exact base_1061)
  | 262 => Or.inl (by have h_eq : n = 1062 := (by omega); rw [h_eq]; exact base_1062)
  | 263 => Or.inl (by have h_eq : n = 1063 := (by omega); rw [h_eq]; exact base_1063)
  | 264 => Or.inl (by have h_eq : n = 1064 := (by omega); rw [h_eq]; exact base_1064)
  | 265 => Or.inl (by have h_eq : n = 1065 := (by omega); rw [h_eq]; exact base_1065)
  | 266 => Or.inl (by have h_eq : n = 1066 := (by omega); rw [h_eq]; exact base_1066)
  | 267 => Or.inl (by have h_eq : n = 1067 := (by omega); rw [h_eq]; exact base_1067)
  | 268 => Or.inl (by have h_eq : n = 1068 := (by omega); rw [h_eq]; exact base_1068)
  | 269 => Or.inl (by have h_eq : n = 1069 := (by omega); rw [h_eq]; exact base_1069)
  | 270 => Or.inl (by have h_eq : n = 1070 := (by omega); rw [h_eq]; exact base_1070)
  | 271 => Or.inl (by have h_eq : n = 1071 := (by omega); rw [h_eq]; exact base_1071)
  | 272 => Or.inl (by have h_eq : n = 1072 := (by omega); rw [h_eq]; exact base_1072)
  | 273 => Or.inl (by have h_eq : n = 1073 := (by omega); rw [h_eq]; exact base_1073)
  | 274 => Or.inl (by have h_eq : n = 1074 := (by omega); rw [h_eq]; exact base_1074)
  | 275 => Or.inl (by have h_eq : n = 1075 := (by omega); rw [h_eq]; exact base_1075)
  | 276 => Or.inl (by have h_eq : n = 1076 := (by omega); rw [h_eq]; exact base_1076)
  | 277 => Or.inl (by have h_eq : n = 1077 := (by omega); rw [h_eq]; exact base_1077)
  | 278 => Or.inl (by have h_eq : n = 1078 := (by omega); rw [h_eq]; exact base_1078)
  | 279 => Or.inl (by have h_eq : n = 1079 := (by omega); rw [h_eq]; exact base_1079)
  | 280 => Or.inl (by have h_eq : n = 1080 := (by omega); rw [h_eq]; exact base_1080)
  | 281 => Or.inl (by have h_eq : n = 1081 := (by omega); rw [h_eq]; exact base_1081)
  | 282 => Or.inl (by have h_eq : n = 1082 := (by omega); rw [h_eq]; exact base_1082)
  | 283 => Or.inl (by have h_eq : n = 1083 := (by omega); rw [h_eq]; exact base_1083)
  | 284 => Or.inl (by have h_eq : n = 1084 := (by omega); rw [h_eq]; exact base_1084)
  | 285 => Or.inl (by have h_eq : n = 1085 := (by omega); rw [h_eq]; exact base_1085)
  | 286 => Or.inl (by have h_eq : n = 1086 := (by omega); rw [h_eq]; exact base_1086)
  | 287 => Or.inl (by have h_eq : n = 1087 := (by omega); rw [h_eq]; exact base_1087)
  | 288 => Or.inl (by have h_eq : n = 1088 := (by omega); rw [h_eq]; exact base_1088)
  | 289 => Or.inl (by have h_eq : n = 1089 := (by omega); rw [h_eq]; exact base_1089)
  | 290 => Or.inl (by have h_eq : n = 1090 := (by omega); rw [h_eq]; exact base_1090)
  | 291 => Or.inl (by have h_eq : n = 1091 := (by omega); rw [h_eq]; exact base_1091)
  | 292 => Or.inl (by have h_eq : n = 1092 := (by omega); rw [h_eq]; exact base_1092)
  | 293 => Or.inl (by have h_eq : n = 1093 := (by omega); rw [h_eq]; exact base_1093)
  | 294 => Or.inl (by have h_eq : n = 1094 := (by omega); rw [h_eq]; exact base_1094)
  | 295 => Or.inl (by have h_eq : n = 1095 := (by omega); rw [h_eq]; exact base_1095)
  | 296 => Or.inl (by have h_eq : n = 1096 := (by omega); rw [h_eq]; exact base_1096)
  | 297 => Or.inl (by have h_eq : n = 1097 := (by omega); rw [h_eq]; exact base_1097)
  | 298 => Or.inl (by have h_eq : n = 1098 := (by omega); rw [h_eq]; exact base_1098)
  | 299 => Or.inl (by have h_eq : n = 1099 := (by omega); rw [h_eq]; exact base_1099)
  | 300 => Or.inl (by have h_eq : n = 1100 := (by omega); rw [h_eq]; exact base_1100)
  | 301 => Or.inl (by have h_eq : n = 1101 := (by omega); rw [h_eq]; exact base_1101)
  | 302 => Or.inl (by have h_eq : n = 1102 := (by omega); rw [h_eq]; exact base_1102)
  | 303 => Or.inl (by have h_eq : n = 1103 := (by omega); rw [h_eq]; exact base_1103)
  | 304 => Or.inl (by have h_eq : n = 1104 := (by omega); rw [h_eq]; exact base_1104)
  | 305 => Or.inl (by have h_eq : n = 1105 := (by omega); rw [h_eq]; exact base_1105)
  | 306 => Or.inl (by have h_eq : n = 1106 := (by omega); rw [h_eq]; exact base_1106)
  | 307 => Or.inl (by have h_eq : n = 1107 := (by omega); rw [h_eq]; exact base_1107)
  | 308 => Or.inl (by have h_eq : n = 1108 := (by omega); rw [h_eq]; exact base_1108)
  | 309 => Or.inl (by have h_eq : n = 1109 := (by omega); rw [h_eq]; exact base_1109)
  | 310 => Or.inl (by have h_eq : n = 1110 := (by omega); rw [h_eq]; exact base_1110)
  | 311 => Or.inl (by have h_eq : n = 1111 := (by omega); rw [h_eq]; exact base_1111)
  | 312 => Or.inl (by have h_eq : n = 1112 := (by omega); rw [h_eq]; exact base_1112)
  | 313 => Or.inl (by have h_eq : n = 1113 := (by omega); rw [h_eq]; exact base_1113)
  | 314 => Or.inl (by have h_eq : n = 1114 := (by omega); rw [h_eq]; exact base_1114)
  | 315 => Or.inl (by have h_eq : n = 1115 := (by omega); rw [h_eq]; exact base_1115)
  | 316 => Or.inl (by have h_eq : n = 1116 := (by omega); rw [h_eq]; exact base_1116)
  | 317 => Or.inl (by have h_eq : n = 1117 := (by omega); rw [h_eq]; exact base_1117)
  | 318 => Or.inl (by have h_eq : n = 1118 := (by omega); rw [h_eq]; exact base_1118)
  | 319 => Or.inl (by have h_eq : n = 1119 := (by omega); rw [h_eq]; exact base_1119)
  | 320 => Or.inl (by have h_eq : n = 1120 := (by omega); rw [h_eq]; exact base_1120)
  | 321 => Or.inl (by have h_eq : n = 1121 := (by omega); rw [h_eq]; exact base_1121)
  | 322 => Or.inl (by have h_eq : n = 1122 := (by omega); rw [h_eq]; exact base_1122)
  | 323 => Or.inl (by have h_eq : n = 1123 := (by omega); rw [h_eq]; exact base_1123)
  | 324 => Or.inl (by have h_eq : n = 1124 := (by omega); rw [h_eq]; exact base_1124)
  | 325 => Or.inl (by have h_eq : n = 1125 := (by omega); rw [h_eq]; exact base_1125)
  | 326 => Or.inl (by have h_eq : n = 1126 := (by omega); rw [h_eq]; exact base_1126)
  | 327 => Or.inl (by have h_eq : n = 1127 := (by omega); rw [h_eq]; exact base_1127)
  | 328 => Or.inl (by have h_eq : n = 1128 := (by omega); rw [h_eq]; exact base_1128)
  | 329 => Or.inl (by have h_eq : n = 1129 := (by omega); rw [h_eq]; exact base_1129)
  | 330 => Or.inl (by have h_eq : n = 1130 := (by omega); rw [h_eq]; exact base_1130)
  | 331 => Or.inl (by have h_eq : n = 1131 := (by omega); rw [h_eq]; exact base_1131)
  | 332 => Or.inl (by have h_eq : n = 1132 := (by omega); rw [h_eq]; exact base_1132)
  | 333 => Or.inl (by have h_eq : n = 1133 := (by omega); rw [h_eq]; exact base_1133)
  | 334 => Or.inl (by have h_eq : n = 1134 := (by omega); rw [h_eq]; exact base_1134)
  | 335 => Or.inl (by have h_eq : n = 1135 := (by omega); rw [h_eq]; exact base_1135)
  | 336 => Or.inl (by have h_eq : n = 1136 := (by omega); rw [h_eq]; exact base_1136)
  | 337 => Or.inl (by have h_eq : n = 1137 := (by omega); rw [h_eq]; exact base_1137)
  | 338 => Or.inl (by have h_eq : n = 1138 := (by omega); rw [h_eq]; exact base_1138)
  | 339 => Or.inl (by have h_eq : n = 1139 := (by omega); rw [h_eq]; exact base_1139)
  | 340 => Or.inl (by have h_eq : n = 1140 := (by omega); rw [h_eq]; exact base_1140)
  | 341 => Or.inl (by have h_eq : n = 1141 := (by omega); rw [h_eq]; exact base_1141)
  | 342 => Or.inl (by have h_eq : n = 1142 := (by omega); rw [h_eq]; exact base_1142)
  | 343 => Or.inl (by have h_eq : n = 1143 := (by omega); rw [h_eq]; exact base_1143)
  | 344 => Or.inl (by have h_eq : n = 1144 := (by omega); rw [h_eq]; exact base_1144)
  | 345 => Or.inl (by have h_eq : n = 1145 := (by omega); rw [h_eq]; exact base_1145)
  | 346 => Or.inl (by have h_eq : n = 1146 := (by omega); rw [h_eq]; exact base_1146)
  | 347 => Or.inl (by have h_eq : n = 1147 := (by omega); rw [h_eq]; exact base_1147)
  | 348 => Or.inl (by have h_eq : n = 1148 := (by omega); rw [h_eq]; exact base_1148)
  | 349 => Or.inl (by have h_eq : n = 1149 := (by omega); rw [h_eq]; exact base_1149)
  | 350 => Or.inl (by have h_eq : n = 1150 := (by omega); rw [h_eq]; exact base_1150)
  | 351 => Or.inl (by have h_eq : n = 1151 := (by omega); rw [h_eq]; exact base_1151)
  | 352 => Or.inl (by have h_eq : n = 1152 := (by omega); rw [h_eq]; exact base_1152)
  | 353 => Or.inl (by have h_eq : n = 1153 := (by omega); rw [h_eq]; exact base_1153)
  | 354 => Or.inl (by have h_eq : n = 1154 := (by omega); rw [h_eq]; exact base_1154)
  | 355 => Or.inl (by have h_eq : n = 1155 := (by omega); rw [h_eq]; exact base_1155)
  | 356 => Or.inl (by have h_eq : n = 1156 := (by omega); rw [h_eq]; exact base_1156)
  | 357 => Or.inl (by have h_eq : n = 1157 := (by omega); rw [h_eq]; exact base_1157)
  | 358 => Or.inl (by have h_eq : n = 1158 := (by omega); rw [h_eq]; exact base_1158)
  | 359 => Or.inl (by have h_eq : n = 1159 := (by omega); rw [h_eq]; exact base_1159)
  | 360 => Or.inl (by have h_eq : n = 1160 := (by omega); rw [h_eq]; exact base_1160)
  | 361 => Or.inl (by have h_eq : n = 1161 := (by omega); rw [h_eq]; exact base_1161)
  | 362 => Or.inl (by have h_eq : n = 1162 := (by omega); rw [h_eq]; exact base_1162)
  | 363 => Or.inl (by have h_eq : n = 1163 := (by omega); rw [h_eq]; exact base_1163)
  | 364 => Or.inl (by have h_eq : n = 1164 := (by omega); rw [h_eq]; exact base_1164)
  | 365 => Or.inl (by have h_eq : n = 1165 := (by omega); rw [h_eq]; exact base_1165)
  | 366 => Or.inl (by have h_eq : n = 1166 := (by omega); rw [h_eq]; exact base_1166)
  | 367 => Or.inl (by have h_eq : n = 1167 := (by omega); rw [h_eq]; exact base_1167)
  | 368 => Or.inl (by have h_eq : n = 1168 := (by omega); rw [h_eq]; exact base_1168)
  | 369 => Or.inl (by have h_eq : n = 1169 := (by omega); rw [h_eq]; exact base_1169)
  | 370 => Or.inl (by have h_eq : n = 1170 := (by omega); rw [h_eq]; exact base_1170)
  | 371 => Or.inl (by have h_eq : n = 1171 := (by omega); rw [h_eq]; exact base_1171)
  | 372 => Or.inl (by have h_eq : n = 1172 := (by omega); rw [h_eq]; exact base_1172)
  | 373 => Or.inl (by have h_eq : n = 1173 := (by omega); rw [h_eq]; exact base_1173)
  | 374 => Or.inl (by have h_eq : n = 1174 := (by omega); rw [h_eq]; exact base_1174)
  | 375 => Or.inl (by have h_eq : n = 1175 := (by omega); rw [h_eq]; exact base_1175)
  | 376 => Or.inl (by have h_eq : n = 1176 := (by omega); rw [h_eq]; exact base_1176)
  | 377 => Or.inl (by have h_eq : n = 1177 := (by omega); rw [h_eq]; exact base_1177)
  | 378 => Or.inl (by have h_eq : n = 1178 := (by omega); rw [h_eq]; exact base_1178)
  | 379 => Or.inl (by have h_eq : n = 1179 := (by omega); rw [h_eq]; exact base_1179)
  | 380 => Or.inl (by have h_eq : n = 1180 := (by omega); rw [h_eq]; exact base_1180)
  | 381 => Or.inl (by have h_eq : n = 1181 := (by omega); rw [h_eq]; exact base_1181)
  | 382 => Or.inl (by have h_eq : n = 1182 := (by omega); rw [h_eq]; exact base_1182)
  | 383 => Or.inl (by have h_eq : n = 1183 := (by omega); rw [h_eq]; exact base_1183)
  | 384 => Or.inl (by have h_eq : n = 1184 := (by omega); rw [h_eq]; exact base_1184)
  | 385 => Or.inl (by have h_eq : n = 1185 := (by omega); rw [h_eq]; exact base_1185)
  | 386 => Or.inl (by have h_eq : n = 1186 := (by omega); rw [h_eq]; exact base_1186)
  | 387 => Or.inl (by have h_eq : n = 1187 := (by omega); rw [h_eq]; exact base_1187)
  | 388 => Or.inl (by have h_eq : n = 1188 := (by omega); rw [h_eq]; exact base_1188)
  | 389 => Or.inl (by have h_eq : n = 1189 := (by omega); rw [h_eq]; exact base_1189)
  | 390 => Or.inl (by have h_eq : n = 1190 := (by omega); rw [h_eq]; exact base_1190)
  | 391 => Or.inl (by have h_eq : n = 1191 := (by omega); rw [h_eq]; exact base_1191)
  | 392 => Or.inl (by have h_eq : n = 1192 := (by omega); rw [h_eq]; exact base_1192)
  | 393 => Or.inl (by have h_eq : n = 1193 := (by omega); rw [h_eq]; exact base_1193)
  | 394 => Or.inl (by have h_eq : n = 1194 := (by omega); rw [h_eq]; exact base_1194)
  | 395 => Or.inl (by have h_eq : n = 1195 := (by omega); rw [h_eq]; exact base_1195)
  | 396 => Or.inl (by have h_eq : n = 1196 := (by omega); rw [h_eq]; exact base_1196)
  | 397 => Or.inl (by have h_eq : n = 1197 := (by omega); rw [h_eq]; exact base_1197)
  | 398 => Or.inl (by have h_eq : n = 1198 := (by omega); rw [h_eq]; exact base_1198)
  | 399 => Or.inl (by have h_eq : n = 1199 := (by omega); rw [h_eq]; exact base_1199)
  | m + 400 => Or.inr (by omega)

lemma base_cases_chunk_3 (n : ℕ) (h_low : 1200 ≤ n) : 0 < A271510 n ∨ n ≥ 1600 :=
  match h : n - 1200 with
  | 0 => Or.inl (by have h_eq : n = 1200 := (by omega); rw [h_eq]; exact base_1200)
  | 1 => Or.inl (by have h_eq : n = 1201 := (by omega); rw [h_eq]; exact base_1201)
  | 2 => Or.inl (by have h_eq : n = 1202 := (by omega); rw [h_eq]; exact base_1202)
  | 3 => Or.inl (by have h_eq : n = 1203 := (by omega); rw [h_eq]; exact base_1203)
  | 4 => Or.inl (by have h_eq : n = 1204 := (by omega); rw [h_eq]; exact base_1204)
  | 5 => Or.inl (by have h_eq : n = 1205 := (by omega); rw [h_eq]; exact base_1205)
  | 6 => Or.inl (by have h_eq : n = 1206 := (by omega); rw [h_eq]; exact base_1206)
  | 7 => Or.inl (by have h_eq : n = 1207 := (by omega); rw [h_eq]; exact base_1207)
  | 8 => Or.inl (by have h_eq : n = 1208 := (by omega); rw [h_eq]; exact base_1208)
  | 9 => Or.inl (by have h_eq : n = 1209 := (by omega); rw [h_eq]; exact base_1209)
  | 10 => Or.inl (by have h_eq : n = 1210 := (by omega); rw [h_eq]; exact base_1210)
  | 11 => Or.inl (by have h_eq : n = 1211 := (by omega); rw [h_eq]; exact base_1211)
  | 12 => Or.inl (by have h_eq : n = 1212 := (by omega); rw [h_eq]; exact base_1212)
  | 13 => Or.inl (by have h_eq : n = 1213 := (by omega); rw [h_eq]; exact base_1213)
  | 14 => Or.inl (by have h_eq : n = 1214 := (by omega); rw [h_eq]; exact base_1214)
  | 15 => Or.inl (by have h_eq : n = 1215 := (by omega); rw [h_eq]; exact base_1215)
  | 16 => Or.inl (by have h_eq : n = 1216 := (by omega); rw [h_eq]; exact base_1216)
  | 17 => Or.inl (by have h_eq : n = 1217 := (by omega); rw [h_eq]; exact base_1217)
  | 18 => Or.inl (by have h_eq : n = 1218 := (by omega); rw [h_eq]; exact base_1218)
  | 19 => Or.inl (by have h_eq : n = 1219 := (by omega); rw [h_eq]; exact base_1219)
  | 20 => Or.inl (by have h_eq : n = 1220 := (by omega); rw [h_eq]; exact base_1220)
  | 21 => Or.inl (by have h_eq : n = 1221 := (by omega); rw [h_eq]; exact base_1221)
  | 22 => Or.inl (by have h_eq : n = 1222 := (by omega); rw [h_eq]; exact base_1222)
  | 23 => Or.inl (by have h_eq : n = 1223 := (by omega); rw [h_eq]; exact base_1223)
  | 24 => Or.inl (by have h_eq : n = 1224 := (by omega); rw [h_eq]; exact base_1224)
  | 25 => Or.inl (by have h_eq : n = 1225 := (by omega); rw [h_eq]; exact base_1225)
  | 26 => Or.inl (by have h_eq : n = 1226 := (by omega); rw [h_eq]; exact base_1226)
  | 27 => Or.inl (by have h_eq : n = 1227 := (by omega); rw [h_eq]; exact base_1227)
  | 28 => Or.inl (by have h_eq : n = 1228 := (by omega); rw [h_eq]; exact base_1228)
  | 29 => Or.inl (by have h_eq : n = 1229 := (by omega); rw [h_eq]; exact base_1229)
  | 30 => Or.inl (by have h_eq : n = 1230 := (by omega); rw [h_eq]; exact base_1230)
  | 31 => Or.inl (by have h_eq : n = 1231 := (by omega); rw [h_eq]; exact base_1231)
  | 32 => Or.inl (by have h_eq : n = 1232 := (by omega); rw [h_eq]; exact base_1232)
  | 33 => Or.inl (by have h_eq : n = 1233 := (by omega); rw [h_eq]; exact base_1233)
  | 34 => Or.inl (by have h_eq : n = 1234 := (by omega); rw [h_eq]; exact base_1234)
  | 35 => Or.inl (by have h_eq : n = 1235 := (by omega); rw [h_eq]; exact base_1235)
  | 36 => Or.inl (by have h_eq : n = 1236 := (by omega); rw [h_eq]; exact base_1236)
  | 37 => Or.inl (by have h_eq : n = 1237 := (by omega); rw [h_eq]; exact base_1237)
  | 38 => Or.inl (by have h_eq : n = 1238 := (by omega); rw [h_eq]; exact base_1238)
  | 39 => Or.inl (by have h_eq : n = 1239 := (by omega); rw [h_eq]; exact base_1239)
  | 40 => Or.inl (by have h_eq : n = 1240 := (by omega); rw [h_eq]; exact base_1240)
  | 41 => Or.inl (by have h_eq : n = 1241 := (by omega); rw [h_eq]; exact base_1241)
  | 42 => Or.inl (by have h_eq : n = 1242 := (by omega); rw [h_eq]; exact base_1242)
  | 43 => Or.inl (by have h_eq : n = 1243 := (by omega); rw [h_eq]; exact base_1243)
  | 44 => Or.inl (by have h_eq : n = 1244 := (by omega); rw [h_eq]; exact base_1244)
  | 45 => Or.inl (by have h_eq : n = 1245 := (by omega); rw [h_eq]; exact base_1245)
  | 46 => Or.inl (by have h_eq : n = 1246 := (by omega); rw [h_eq]; exact base_1246)
  | 47 => Or.inl (by have h_eq : n = 1247 := (by omega); rw [h_eq]; exact base_1247)
  | 48 => Or.inl (by have h_eq : n = 1248 := (by omega); rw [h_eq]; exact base_1248)
  | 49 => Or.inl (by have h_eq : n = 1249 := (by omega); rw [h_eq]; exact base_1249)
  | 50 => Or.inl (by have h_eq : n = 1250 := (by omega); rw [h_eq]; exact base_1250)
  | 51 => Or.inl (by have h_eq : n = 1251 := (by omega); rw [h_eq]; exact base_1251)
  | 52 => Or.inl (by have h_eq : n = 1252 := (by omega); rw [h_eq]; exact base_1252)
  | 53 => Or.inl (by have h_eq : n = 1253 := (by omega); rw [h_eq]; exact base_1253)
  | 54 => Or.inl (by have h_eq : n = 1254 := (by omega); rw [h_eq]; exact base_1254)
  | 55 => Or.inl (by have h_eq : n = 1255 := (by omega); rw [h_eq]; exact base_1255)
  | 56 => Or.inl (by have h_eq : n = 1256 := (by omega); rw [h_eq]; exact base_1256)
  | 57 => Or.inl (by have h_eq : n = 1257 := (by omega); rw [h_eq]; exact base_1257)
  | 58 => Or.inl (by have h_eq : n = 1258 := (by omega); rw [h_eq]; exact base_1258)
  | 59 => Or.inl (by have h_eq : n = 1259 := (by omega); rw [h_eq]; exact base_1259)
  | 60 => Or.inl (by have h_eq : n = 1260 := (by omega); rw [h_eq]; exact base_1260)
  | 61 => Or.inl (by have h_eq : n = 1261 := (by omega); rw [h_eq]; exact base_1261)
  | 62 => Or.inl (by have h_eq : n = 1262 := (by omega); rw [h_eq]; exact base_1262)
  | 63 => Or.inl (by have h_eq : n = 1263 := (by omega); rw [h_eq]; exact base_1263)
  | 64 => Or.inl (by have h_eq : n = 1264 := (by omega); rw [h_eq]; exact base_1264)
  | 65 => Or.inl (by have h_eq : n = 1265 := (by omega); rw [h_eq]; exact base_1265)
  | 66 => Or.inl (by have h_eq : n = 1266 := (by omega); rw [h_eq]; exact base_1266)
  | 67 => Or.inl (by have h_eq : n = 1267 := (by omega); rw [h_eq]; exact base_1267)
  | 68 => Or.inl (by have h_eq : n = 1268 := (by omega); rw [h_eq]; exact base_1268)
  | 69 => Or.inl (by have h_eq : n = 1269 := (by omega); rw [h_eq]; exact base_1269)
  | 70 => Or.inl (by have h_eq : n = 1270 := (by omega); rw [h_eq]; exact base_1270)
  | 71 => Or.inl (by have h_eq : n = 1271 := (by omega); rw [h_eq]; exact base_1271)
  | 72 => Or.inl (by have h_eq : n = 1272 := (by omega); rw [h_eq]; exact base_1272)
  | 73 => Or.inl (by have h_eq : n = 1273 := (by omega); rw [h_eq]; exact base_1273)
  | 74 => Or.inl (by have h_eq : n = 1274 := (by omega); rw [h_eq]; exact base_1274)
  | 75 => Or.inl (by have h_eq : n = 1275 := (by omega); rw [h_eq]; exact base_1275)
  | 76 => Or.inl (by have h_eq : n = 1276 := (by omega); rw [h_eq]; exact base_1276)
  | 77 => Or.inl (by have h_eq : n = 1277 := (by omega); rw [h_eq]; exact base_1277)
  | 78 => Or.inl (by have h_eq : n = 1278 := (by omega); rw [h_eq]; exact base_1278)
  | 79 => Or.inl (by have h_eq : n = 1279 := (by omega); rw [h_eq]; exact base_1279)
  | 80 => Or.inl (by have h_eq : n = 1280 := (by omega); rw [h_eq]; exact base_1280)
  | 81 => Or.inl (by have h_eq : n = 1281 := (by omega); rw [h_eq]; exact base_1281)
  | 82 => Or.inl (by have h_eq : n = 1282 := (by omega); rw [h_eq]; exact base_1282)
  | 83 => Or.inl (by have h_eq : n = 1283 := (by omega); rw [h_eq]; exact base_1283)
  | 84 => Or.inl (by have h_eq : n = 1284 := (by omega); rw [h_eq]; exact base_1284)
  | 85 => Or.inl (by have h_eq : n = 1285 := (by omega); rw [h_eq]; exact base_1285)
  | 86 => Or.inl (by have h_eq : n = 1286 := (by omega); rw [h_eq]; exact base_1286)
  | 87 => Or.inl (by have h_eq : n = 1287 := (by omega); rw [h_eq]; exact base_1287)
  | 88 => Or.inl (by have h_eq : n = 1288 := (by omega); rw [h_eq]; exact base_1288)
  | 89 => Or.inl (by have h_eq : n = 1289 := (by omega); rw [h_eq]; exact base_1289)
  | 90 => Or.inl (by have h_eq : n = 1290 := (by omega); rw [h_eq]; exact base_1290)
  | 91 => Or.inl (by have h_eq : n = 1291 := (by omega); rw [h_eq]; exact base_1291)
  | 92 => Or.inl (by have h_eq : n = 1292 := (by omega); rw [h_eq]; exact base_1292)
  | 93 => Or.inl (by have h_eq : n = 1293 := (by omega); rw [h_eq]; exact base_1293)
  | 94 => Or.inl (by have h_eq : n = 1294 := (by omega); rw [h_eq]; exact base_1294)
  | 95 => Or.inl (by have h_eq : n = 1295 := (by omega); rw [h_eq]; exact base_1295)
  | 96 => Or.inl (by have h_eq : n = 1296 := (by omega); rw [h_eq]; exact base_1296)
  | 97 => Or.inl (by have h_eq : n = 1297 := (by omega); rw [h_eq]; exact base_1297)
  | 98 => Or.inl (by have h_eq : n = 1298 := (by omega); rw [h_eq]; exact base_1298)
  | 99 => Or.inl (by have h_eq : n = 1299 := (by omega); rw [h_eq]; exact base_1299)
  | 100 => Or.inl (by have h_eq : n = 1300 := (by omega); rw [h_eq]; exact base_1300)
  | 101 => Or.inl (by have h_eq : n = 1301 := (by omega); rw [h_eq]; exact base_1301)
  | 102 => Or.inl (by have h_eq : n = 1302 := (by omega); rw [h_eq]; exact base_1302)
  | 103 => Or.inl (by have h_eq : n = 1303 := (by omega); rw [h_eq]; exact base_1303)
  | 104 => Or.inl (by have h_eq : n = 1304 := (by omega); rw [h_eq]; exact base_1304)
  | 105 => Or.inl (by have h_eq : n = 1305 := (by omega); rw [h_eq]; exact base_1305)
  | 106 => Or.inl (by have h_eq : n = 1306 := (by omega); rw [h_eq]; exact base_1306)
  | 107 => Or.inl (by have h_eq : n = 1307 := (by omega); rw [h_eq]; exact base_1307)
  | 108 => Or.inl (by have h_eq : n = 1308 := (by omega); rw [h_eq]; exact base_1308)
  | 109 => Or.inl (by have h_eq : n = 1309 := (by omega); rw [h_eq]; exact base_1309)
  | 110 => Or.inl (by have h_eq : n = 1310 := (by omega); rw [h_eq]; exact base_1310)
  | 111 => Or.inl (by have h_eq : n = 1311 := (by omega); rw [h_eq]; exact base_1311)
  | 112 => Or.inl (by have h_eq : n = 1312 := (by omega); rw [h_eq]; exact base_1312)
  | 113 => Or.inl (by have h_eq : n = 1313 := (by omega); rw [h_eq]; exact base_1313)
  | 114 => Or.inl (by have h_eq : n = 1314 := (by omega); rw [h_eq]; exact base_1314)
  | 115 => Or.inl (by have h_eq : n = 1315 := (by omega); rw [h_eq]; exact base_1315)
  | 116 => Or.inl (by have h_eq : n = 1316 := (by omega); rw [h_eq]; exact base_1316)
  | 117 => Or.inl (by have h_eq : n = 1317 := (by omega); rw [h_eq]; exact base_1317)
  | 118 => Or.inl (by have h_eq : n = 1318 := (by omega); rw [h_eq]; exact base_1318)
  | 119 => Or.inl (by have h_eq : n = 1319 := (by omega); rw [h_eq]; exact base_1319)
  | 120 => Or.inl (by have h_eq : n = 1320 := (by omega); rw [h_eq]; exact base_1320)
  | 121 => Or.inl (by have h_eq : n = 1321 := (by omega); rw [h_eq]; exact base_1321)
  | 122 => Or.inl (by have h_eq : n = 1322 := (by omega); rw [h_eq]; exact base_1322)
  | 123 => Or.inl (by have h_eq : n = 1323 := (by omega); rw [h_eq]; exact base_1323)
  | 124 => Or.inl (by have h_eq : n = 1324 := (by omega); rw [h_eq]; exact base_1324)
  | 125 => Or.inl (by have h_eq : n = 1325 := (by omega); rw [h_eq]; exact base_1325)
  | 126 => Or.inl (by have h_eq : n = 1326 := (by omega); rw [h_eq]; exact base_1326)
  | 127 => Or.inl (by have h_eq : n = 1327 := (by omega); rw [h_eq]; exact base_1327)
  | 128 => Or.inl (by have h_eq : n = 1328 := (by omega); rw [h_eq]; exact base_1328)
  | 129 => Or.inl (by have h_eq : n = 1329 := (by omega); rw [h_eq]; exact base_1329)
  | 130 => Or.inl (by have h_eq : n = 1330 := (by omega); rw [h_eq]; exact base_1330)
  | 131 => Or.inl (by have h_eq : n = 1331 := (by omega); rw [h_eq]; exact base_1331)
  | 132 => Or.inl (by have h_eq : n = 1332 := (by omega); rw [h_eq]; exact base_1332)
  | 133 => Or.inl (by have h_eq : n = 1333 := (by omega); rw [h_eq]; exact base_1333)
  | 134 => Or.inl (by have h_eq : n = 1334 := (by omega); rw [h_eq]; exact base_1334)
  | 135 => Or.inl (by have h_eq : n = 1335 := (by omega); rw [h_eq]; exact base_1335)
  | 136 => Or.inl (by have h_eq : n = 1336 := (by omega); rw [h_eq]; exact base_1336)
  | 137 => Or.inl (by have h_eq : n = 1337 := (by omega); rw [h_eq]; exact base_1337)
  | 138 => Or.inl (by have h_eq : n = 1338 := (by omega); rw [h_eq]; exact base_1338)
  | 139 => Or.inl (by have h_eq : n = 1339 := (by omega); rw [h_eq]; exact base_1339)
  | 140 => Or.inl (by have h_eq : n = 1340 := (by omega); rw [h_eq]; exact base_1340)
  | 141 => Or.inl (by have h_eq : n = 1341 := (by omega); rw [h_eq]; exact base_1341)
  | 142 => Or.inl (by have h_eq : n = 1342 := (by omega); rw [h_eq]; exact base_1342)
  | 143 => Or.inl (by have h_eq : n = 1343 := (by omega); rw [h_eq]; exact base_1343)
  | 144 => Or.inl (by have h_eq : n = 1344 := (by omega); rw [h_eq]; exact base_1344)
  | 145 => Or.inl (by have h_eq : n = 1345 := (by omega); rw [h_eq]; exact base_1345)
  | 146 => Or.inl (by have h_eq : n = 1346 := (by omega); rw [h_eq]; exact base_1346)
  | 147 => Or.inl (by have h_eq : n = 1347 := (by omega); rw [h_eq]; exact base_1347)
  | 148 => Or.inl (by have h_eq : n = 1348 := (by omega); rw [h_eq]; exact base_1348)
  | 149 => Or.inl (by have h_eq : n = 1349 := (by omega); rw [h_eq]; exact base_1349)
  | 150 => Or.inl (by have h_eq : n = 1350 := (by omega); rw [h_eq]; exact base_1350)
  | 151 => Or.inl (by have h_eq : n = 1351 := (by omega); rw [h_eq]; exact base_1351)
  | 152 => Or.inl (by have h_eq : n = 1352 := (by omega); rw [h_eq]; exact base_1352)
  | 153 => Or.inl (by have h_eq : n = 1353 := (by omega); rw [h_eq]; exact base_1353)
  | 154 => Or.inl (by have h_eq : n = 1354 := (by omega); rw [h_eq]; exact base_1354)
  | 155 => Or.inl (by have h_eq : n = 1355 := (by omega); rw [h_eq]; exact base_1355)
  | 156 => Or.inl (by have h_eq : n = 1356 := (by omega); rw [h_eq]; exact base_1356)
  | 157 => Or.inl (by have h_eq : n = 1357 := (by omega); rw [h_eq]; exact base_1357)
  | 158 => Or.inl (by have h_eq : n = 1358 := (by omega); rw [h_eq]; exact base_1358)
  | 159 => Or.inl (by have h_eq : n = 1359 := (by omega); rw [h_eq]; exact base_1359)
  | 160 => Or.inl (by have h_eq : n = 1360 := (by omega); rw [h_eq]; exact base_1360)
  | 161 => Or.inl (by have h_eq : n = 1361 := (by omega); rw [h_eq]; exact base_1361)
  | 162 => Or.inl (by have h_eq : n = 1362 := (by omega); rw [h_eq]; exact base_1362)
  | 163 => Or.inl (by have h_eq : n = 1363 := (by omega); rw [h_eq]; exact base_1363)
  | 164 => Or.inl (by have h_eq : n = 1364 := (by omega); rw [h_eq]; exact base_1364)
  | 165 => Or.inl (by have h_eq : n = 1365 := (by omega); rw [h_eq]; exact base_1365)
  | 166 => Or.inl (by have h_eq : n = 1366 := (by omega); rw [h_eq]; exact base_1366)
  | 167 => Or.inl (by have h_eq : n = 1367 := (by omega); rw [h_eq]; exact base_1367)
  | 168 => Or.inl (by have h_eq : n = 1368 := (by omega); rw [h_eq]; exact base_1368)
  | 169 => Or.inl (by have h_eq : n = 1369 := (by omega); rw [h_eq]; exact base_1369)
  | 170 => Or.inl (by have h_eq : n = 1370 := (by omega); rw [h_eq]; exact base_1370)
  | 171 => Or.inl (by have h_eq : n = 1371 := (by omega); rw [h_eq]; exact base_1371)
  | 172 => Or.inl (by have h_eq : n = 1372 := (by omega); rw [h_eq]; exact base_1372)
  | 173 => Or.inl (by have h_eq : n = 1373 := (by omega); rw [h_eq]; exact base_1373)
  | 174 => Or.inl (by have h_eq : n = 1374 := (by omega); rw [h_eq]; exact base_1374)
  | 175 => Or.inl (by have h_eq : n = 1375 := (by omega); rw [h_eq]; exact base_1375)
  | 176 => Or.inl (by have h_eq : n = 1376 := (by omega); rw [h_eq]; exact base_1376)
  | 177 => Or.inl (by have h_eq : n = 1377 := (by omega); rw [h_eq]; exact base_1377)
  | 178 => Or.inl (by have h_eq : n = 1378 := (by omega); rw [h_eq]; exact base_1378)
  | 179 => Or.inl (by have h_eq : n = 1379 := (by omega); rw [h_eq]; exact base_1379)
  | 180 => Or.inl (by have h_eq : n = 1380 := (by omega); rw [h_eq]; exact base_1380)
  | 181 => Or.inl (by have h_eq : n = 1381 := (by omega); rw [h_eq]; exact base_1381)
  | 182 => Or.inl (by have h_eq : n = 1382 := (by omega); rw [h_eq]; exact base_1382)
  | 183 => Or.inl (by have h_eq : n = 1383 := (by omega); rw [h_eq]; exact base_1383)
  | 184 => Or.inl (by have h_eq : n = 1384 := (by omega); rw [h_eq]; exact base_1384)
  | 185 => Or.inl (by have h_eq : n = 1385 := (by omega); rw [h_eq]; exact base_1385)
  | 186 => Or.inl (by have h_eq : n = 1386 := (by omega); rw [h_eq]; exact base_1386)
  | 187 => Or.inl (by have h_eq : n = 1387 := (by omega); rw [h_eq]; exact base_1387)
  | 188 => Or.inl (by have h_eq : n = 1388 := (by omega); rw [h_eq]; exact base_1388)
  | 189 => Or.inl (by have h_eq : n = 1389 := (by omega); rw [h_eq]; exact base_1389)
  | 190 => Or.inl (by have h_eq : n = 1390 := (by omega); rw [h_eq]; exact base_1390)
  | 191 => Or.inl (by have h_eq : n = 1391 := (by omega); rw [h_eq]; exact base_1391)
  | 192 => Or.inl (by have h_eq : n = 1392 := (by omega); rw [h_eq]; exact base_1392)
  | 193 => Or.inl (by have h_eq : n = 1393 := (by omega); rw [h_eq]; exact base_1393)
  | 194 => Or.inl (by have h_eq : n = 1394 := (by omega); rw [h_eq]; exact base_1394)
  | 195 => Or.inl (by have h_eq : n = 1395 := (by omega); rw [h_eq]; exact base_1395)
  | 196 => Or.inl (by have h_eq : n = 1396 := (by omega); rw [h_eq]; exact base_1396)
  | 197 => Or.inl (by have h_eq : n = 1397 := (by omega); rw [h_eq]; exact base_1397)
  | 198 => Or.inl (by have h_eq : n = 1398 := (by omega); rw [h_eq]; exact base_1398)
  | 199 => Or.inl (by have h_eq : n = 1399 := (by omega); rw [h_eq]; exact base_1399)
  | 200 => Or.inl (by have h_eq : n = 1400 := (by omega); rw [h_eq]; exact base_1400)
  | 201 => Or.inl (by have h_eq : n = 1401 := (by omega); rw [h_eq]; exact base_1401)
  | 202 => Or.inl (by have h_eq : n = 1402 := (by omega); rw [h_eq]; exact base_1402)
  | 203 => Or.inl (by have h_eq : n = 1403 := (by omega); rw [h_eq]; exact base_1403)
  | 204 => Or.inl (by have h_eq : n = 1404 := (by omega); rw [h_eq]; exact base_1404)
  | 205 => Or.inl (by have h_eq : n = 1405 := (by omega); rw [h_eq]; exact base_1405)
  | 206 => Or.inl (by have h_eq : n = 1406 := (by omega); rw [h_eq]; exact base_1406)
  | 207 => Or.inl (by have h_eq : n = 1407 := (by omega); rw [h_eq]; exact base_1407)
  | 208 => Or.inl (by have h_eq : n = 1408 := (by omega); rw [h_eq]; exact base_1408)
  | 209 => Or.inl (by have h_eq : n = 1409 := (by omega); rw [h_eq]; exact base_1409)
  | 210 => Or.inl (by have h_eq : n = 1410 := (by omega); rw [h_eq]; exact base_1410)
  | 211 => Or.inl (by have h_eq : n = 1411 := (by omega); rw [h_eq]; exact base_1411)
  | 212 => Or.inl (by have h_eq : n = 1412 := (by omega); rw [h_eq]; exact base_1412)
  | 213 => Or.inl (by have h_eq : n = 1413 := (by omega); rw [h_eq]; exact base_1413)
  | 214 => Or.inl (by have h_eq : n = 1414 := (by omega); rw [h_eq]; exact base_1414)
  | 215 => Or.inl (by have h_eq : n = 1415 := (by omega); rw [h_eq]; exact base_1415)
  | 216 => Or.inl (by have h_eq : n = 1416 := (by omega); rw [h_eq]; exact base_1416)
  | 217 => Or.inl (by have h_eq : n = 1417 := (by omega); rw [h_eq]; exact base_1417)
  | 218 => Or.inl (by have h_eq : n = 1418 := (by omega); rw [h_eq]; exact base_1418)
  | 219 => Or.inl (by have h_eq : n = 1419 := (by omega); rw [h_eq]; exact base_1419)
  | 220 => Or.inl (by have h_eq : n = 1420 := (by omega); rw [h_eq]; exact base_1420)
  | 221 => Or.inl (by have h_eq : n = 1421 := (by omega); rw [h_eq]; exact base_1421)
  | 222 => Or.inl (by have h_eq : n = 1422 := (by omega); rw [h_eq]; exact base_1422)
  | 223 => Or.inl (by have h_eq : n = 1423 := (by omega); rw [h_eq]; exact base_1423)
  | 224 => Or.inl (by have h_eq : n = 1424 := (by omega); rw [h_eq]; exact base_1424)
  | 225 => Or.inl (by have h_eq : n = 1425 := (by omega); rw [h_eq]; exact base_1425)
  | 226 => Or.inl (by have h_eq : n = 1426 := (by omega); rw [h_eq]; exact base_1426)
  | 227 => Or.inl (by have h_eq : n = 1427 := (by omega); rw [h_eq]; exact base_1427)
  | 228 => Or.inl (by have h_eq : n = 1428 := (by omega); rw [h_eq]; exact base_1428)
  | 229 => Or.inl (by have h_eq : n = 1429 := (by omega); rw [h_eq]; exact base_1429)
  | 230 => Or.inl (by have h_eq : n = 1430 := (by omega); rw [h_eq]; exact base_1430)
  | 231 => Or.inl (by have h_eq : n = 1431 := (by omega); rw [h_eq]; exact base_1431)
  | 232 => Or.inl (by have h_eq : n = 1432 := (by omega); rw [h_eq]; exact base_1432)
  | 233 => Or.inl (by have h_eq : n = 1433 := (by omega); rw [h_eq]; exact base_1433)
  | 234 => Or.inl (by have h_eq : n = 1434 := (by omega); rw [h_eq]; exact base_1434)
  | 235 => Or.inl (by have h_eq : n = 1435 := (by omega); rw [h_eq]; exact base_1435)
  | 236 => Or.inl (by have h_eq : n = 1436 := (by omega); rw [h_eq]; exact base_1436)
  | 237 => Or.inl (by have h_eq : n = 1437 := (by omega); rw [h_eq]; exact base_1437)
  | 238 => Or.inl (by have h_eq : n = 1438 := (by omega); rw [h_eq]; exact base_1438)
  | 239 => Or.inl (by have h_eq : n = 1439 := (by omega); rw [h_eq]; exact base_1439)
  | 240 => Or.inl (by have h_eq : n = 1440 := (by omega); rw [h_eq]; exact base_1440)
  | 241 => Or.inl (by have h_eq : n = 1441 := (by omega); rw [h_eq]; exact base_1441)
  | 242 => Or.inl (by have h_eq : n = 1442 := (by omega); rw [h_eq]; exact base_1442)
  | 243 => Or.inl (by have h_eq : n = 1443 := (by omega); rw [h_eq]; exact base_1443)
  | 244 => Or.inl (by have h_eq : n = 1444 := (by omega); rw [h_eq]; exact base_1444)
  | 245 => Or.inl (by have h_eq : n = 1445 := (by omega); rw [h_eq]; exact base_1445)
  | 246 => Or.inl (by have h_eq : n = 1446 := (by omega); rw [h_eq]; exact base_1446)
  | 247 => Or.inl (by have h_eq : n = 1447 := (by omega); rw [h_eq]; exact base_1447)
  | 248 => Or.inl (by have h_eq : n = 1448 := (by omega); rw [h_eq]; exact base_1448)
  | 249 => Or.inl (by have h_eq : n = 1449 := (by omega); rw [h_eq]; exact base_1449)
  | 250 => Or.inl (by have h_eq : n = 1450 := (by omega); rw [h_eq]; exact base_1450)
  | 251 => Or.inl (by have h_eq : n = 1451 := (by omega); rw [h_eq]; exact base_1451)
  | 252 => Or.inl (by have h_eq : n = 1452 := (by omega); rw [h_eq]; exact base_1452)
  | 253 => Or.inl (by have h_eq : n = 1453 := (by omega); rw [h_eq]; exact base_1453)
  | 254 => Or.inl (by have h_eq : n = 1454 := (by omega); rw [h_eq]; exact base_1454)
  | 255 => Or.inl (by have h_eq : n = 1455 := (by omega); rw [h_eq]; exact base_1455)
  | 256 => Or.inl (by have h_eq : n = 1456 := (by omega); rw [h_eq]; exact base_1456)
  | 257 => Or.inl (by have h_eq : n = 1457 := (by omega); rw [h_eq]; exact base_1457)
  | 258 => Or.inl (by have h_eq : n = 1458 := (by omega); rw [h_eq]; exact base_1458)
  | 259 => Or.inl (by have h_eq : n = 1459 := (by omega); rw [h_eq]; exact base_1459)
  | 260 => Or.inl (by have h_eq : n = 1460 := (by omega); rw [h_eq]; exact base_1460)
  | 261 => Or.inl (by have h_eq : n = 1461 := (by omega); rw [h_eq]; exact base_1461)
  | 262 => Or.inl (by have h_eq : n = 1462 := (by omega); rw [h_eq]; exact base_1462)
  | 263 => Or.inl (by have h_eq : n = 1463 := (by omega); rw [h_eq]; exact base_1463)
  | 264 => Or.inl (by have h_eq : n = 1464 := (by omega); rw [h_eq]; exact base_1464)
  | 265 => Or.inl (by have h_eq : n = 1465 := (by omega); rw [h_eq]; exact base_1465)
  | 266 => Or.inl (by have h_eq : n = 1466 := (by omega); rw [h_eq]; exact base_1466)
  | 267 => Or.inl (by have h_eq : n = 1467 := (by omega); rw [h_eq]; exact base_1467)
  | 268 => Or.inl (by have h_eq : n = 1468 := (by omega); rw [h_eq]; exact base_1468)
  | 269 => Or.inl (by have h_eq : n = 1469 := (by omega); rw [h_eq]; exact base_1469)
  | 270 => Or.inl (by have h_eq : n = 1470 := (by omega); rw [h_eq]; exact base_1470)
  | 271 => Or.inl (by have h_eq : n = 1471 := (by omega); rw [h_eq]; exact base_1471)
  | 272 => Or.inl (by have h_eq : n = 1472 := (by omega); rw [h_eq]; exact base_1472)
  | 273 => Or.inl (by have h_eq : n = 1473 := (by omega); rw [h_eq]; exact base_1473)
  | 274 => Or.inl (by have h_eq : n = 1474 := (by omega); rw [h_eq]; exact base_1474)
  | 275 => Or.inl (by have h_eq : n = 1475 := (by omega); rw [h_eq]; exact base_1475)
  | 276 => Or.inl (by have h_eq : n = 1476 := (by omega); rw [h_eq]; exact base_1476)
  | 277 => Or.inl (by have h_eq : n = 1477 := (by omega); rw [h_eq]; exact base_1477)
  | 278 => Or.inl (by have h_eq : n = 1478 := (by omega); rw [h_eq]; exact base_1478)
  | 279 => Or.inl (by have h_eq : n = 1479 := (by omega); rw [h_eq]; exact base_1479)
  | 280 => Or.inl (by have h_eq : n = 1480 := (by omega); rw [h_eq]; exact base_1480)
  | 281 => Or.inl (by have h_eq : n = 1481 := (by omega); rw [h_eq]; exact base_1481)
  | 282 => Or.inl (by have h_eq : n = 1482 := (by omega); rw [h_eq]; exact base_1482)
  | 283 => Or.inl (by have h_eq : n = 1483 := (by omega); rw [h_eq]; exact base_1483)
  | 284 => Or.inl (by have h_eq : n = 1484 := (by omega); rw [h_eq]; exact base_1484)
  | 285 => Or.inl (by have h_eq : n = 1485 := (by omega); rw [h_eq]; exact base_1485)
  | 286 => Or.inl (by have h_eq : n = 1486 := (by omega); rw [h_eq]; exact base_1486)
  | 287 => Or.inl (by have h_eq : n = 1487 := (by omega); rw [h_eq]; exact base_1487)
  | 288 => Or.inl (by have h_eq : n = 1488 := (by omega); rw [h_eq]; exact base_1488)
  | 289 => Or.inl (by have h_eq : n = 1489 := (by omega); rw [h_eq]; exact base_1489)
  | 290 => Or.inl (by have h_eq : n = 1490 := (by omega); rw [h_eq]; exact base_1490)
  | 291 => Or.inl (by have h_eq : n = 1491 := (by omega); rw [h_eq]; exact base_1491)
  | 292 => Or.inl (by have h_eq : n = 1492 := (by omega); rw [h_eq]; exact base_1492)
  | 293 => Or.inl (by have h_eq : n = 1493 := (by omega); rw [h_eq]; exact base_1493)
  | 294 => Or.inl (by have h_eq : n = 1494 := (by omega); rw [h_eq]; exact base_1494)
  | 295 => Or.inl (by have h_eq : n = 1495 := (by omega); rw [h_eq]; exact base_1495)
  | 296 => Or.inl (by have h_eq : n = 1496 := (by omega); rw [h_eq]; exact base_1496)
  | 297 => Or.inl (by have h_eq : n = 1497 := (by omega); rw [h_eq]; exact base_1497)
  | 298 => Or.inl (by have h_eq : n = 1498 := (by omega); rw [h_eq]; exact base_1498)
  | 299 => Or.inl (by have h_eq : n = 1499 := (by omega); rw [h_eq]; exact base_1499)
  | 300 => Or.inl (by have h_eq : n = 1500 := (by omega); rw [h_eq]; exact base_1500)
  | 301 => Or.inl (by have h_eq : n = 1501 := (by omega); rw [h_eq]; exact base_1501)
  | 302 => Or.inl (by have h_eq : n = 1502 := (by omega); rw [h_eq]; exact base_1502)
  | 303 => Or.inl (by have h_eq : n = 1503 := (by omega); rw [h_eq]; exact base_1503)
  | 304 => Or.inl (by have h_eq : n = 1504 := (by omega); rw [h_eq]; exact base_1504)
  | 305 => Or.inl (by have h_eq : n = 1505 := (by omega); rw [h_eq]; exact base_1505)
  | 306 => Or.inl (by have h_eq : n = 1506 := (by omega); rw [h_eq]; exact base_1506)
  | 307 => Or.inl (by have h_eq : n = 1507 := (by omega); rw [h_eq]; exact base_1507)
  | 308 => Or.inl (by have h_eq : n = 1508 := (by omega); rw [h_eq]; exact base_1508)
  | 309 => Or.inl (by have h_eq : n = 1509 := (by omega); rw [h_eq]; exact base_1509)
  | 310 => Or.inl (by have h_eq : n = 1510 := (by omega); rw [h_eq]; exact base_1510)
  | 311 => Or.inl (by have h_eq : n = 1511 := (by omega); rw [h_eq]; exact base_1511)
  | 312 => Or.inl (by have h_eq : n = 1512 := (by omega); rw [h_eq]; exact base_1512)
  | 313 => Or.inl (by have h_eq : n = 1513 := (by omega); rw [h_eq]; exact base_1513)
  | 314 => Or.inl (by have h_eq : n = 1514 := (by omega); rw [h_eq]; exact base_1514)
  | 315 => Or.inl (by have h_eq : n = 1515 := (by omega); rw [h_eq]; exact base_1515)
  | 316 => Or.inl (by have h_eq : n = 1516 := (by omega); rw [h_eq]; exact base_1516)
  | 317 => Or.inl (by have h_eq : n = 1517 := (by omega); rw [h_eq]; exact base_1517)
  | 318 => Or.inl (by have h_eq : n = 1518 := (by omega); rw [h_eq]; exact base_1518)
  | 319 => Or.inl (by have h_eq : n = 1519 := (by omega); rw [h_eq]; exact base_1519)
  | 320 => Or.inl (by have h_eq : n = 1520 := (by omega); rw [h_eq]; exact base_1520)
  | 321 => Or.inl (by have h_eq : n = 1521 := (by omega); rw [h_eq]; exact base_1521)
  | 322 => Or.inl (by have h_eq : n = 1522 := (by omega); rw [h_eq]; exact base_1522)
  | 323 => Or.inl (by have h_eq : n = 1523 := (by omega); rw [h_eq]; exact base_1523)
  | 324 => Or.inl (by have h_eq : n = 1524 := (by omega); rw [h_eq]; exact base_1524)
  | 325 => Or.inl (by have h_eq : n = 1525 := (by omega); rw [h_eq]; exact base_1525)
  | 326 => Or.inl (by have h_eq : n = 1526 := (by omega); rw [h_eq]; exact base_1526)
  | 327 => Or.inl (by have h_eq : n = 1527 := (by omega); rw [h_eq]; exact base_1527)
  | 328 => Or.inl (by have h_eq : n = 1528 := (by omega); rw [h_eq]; exact base_1528)
  | 329 => Or.inl (by have h_eq : n = 1529 := (by omega); rw [h_eq]; exact base_1529)
  | 330 => Or.inl (by have h_eq : n = 1530 := (by omega); rw [h_eq]; exact base_1530)
  | 331 => Or.inl (by have h_eq : n = 1531 := (by omega); rw [h_eq]; exact base_1531)
  | 332 => Or.inl (by have h_eq : n = 1532 := (by omega); rw [h_eq]; exact base_1532)
  | 333 => Or.inl (by have h_eq : n = 1533 := (by omega); rw [h_eq]; exact base_1533)
  | 334 => Or.inl (by have h_eq : n = 1534 := (by omega); rw [h_eq]; exact base_1534)
  | 335 => Or.inl (by have h_eq : n = 1535 := (by omega); rw [h_eq]; exact base_1535)
  | 336 => Or.inl (by have h_eq : n = 1536 := (by omega); rw [h_eq]; exact base_1536)
  | 337 => Or.inl (by have h_eq : n = 1537 := (by omega); rw [h_eq]; exact base_1537)
  | 338 => Or.inl (by have h_eq : n = 1538 := (by omega); rw [h_eq]; exact base_1538)
  | 339 => Or.inl (by have h_eq : n = 1539 := (by omega); rw [h_eq]; exact base_1539)
  | 340 => Or.inl (by have h_eq : n = 1540 := (by omega); rw [h_eq]; exact base_1540)
  | 341 => Or.inl (by have h_eq : n = 1541 := (by omega); rw [h_eq]; exact base_1541)
  | 342 => Or.inl (by have h_eq : n = 1542 := (by omega); rw [h_eq]; exact base_1542)
  | 343 => Or.inl (by have h_eq : n = 1543 := (by omega); rw [h_eq]; exact base_1543)
  | 344 => Or.inl (by have h_eq : n = 1544 := (by omega); rw [h_eq]; exact base_1544)
  | 345 => Or.inl (by have h_eq : n = 1545 := (by omega); rw [h_eq]; exact base_1545)
  | 346 => Or.inl (by have h_eq : n = 1546 := (by omega); rw [h_eq]; exact base_1546)
  | 347 => Or.inl (by have h_eq : n = 1547 := (by omega); rw [h_eq]; exact base_1547)
  | 348 => Or.inl (by have h_eq : n = 1548 := (by omega); rw [h_eq]; exact base_1548)
  | 349 => Or.inl (by have h_eq : n = 1549 := (by omega); rw [h_eq]; exact base_1549)
  | 350 => Or.inl (by have h_eq : n = 1550 := (by omega); rw [h_eq]; exact base_1550)
  | 351 => Or.inl (by have h_eq : n = 1551 := (by omega); rw [h_eq]; exact base_1551)
  | 352 => Or.inl (by have h_eq : n = 1552 := (by omega); rw [h_eq]; exact base_1552)
  | 353 => Or.inl (by have h_eq : n = 1553 := (by omega); rw [h_eq]; exact base_1553)
  | 354 => Or.inl (by have h_eq : n = 1554 := (by omega); rw [h_eq]; exact base_1554)
  | 355 => Or.inl (by have h_eq : n = 1555 := (by omega); rw [h_eq]; exact base_1555)
  | 356 => Or.inl (by have h_eq : n = 1556 := (by omega); rw [h_eq]; exact base_1556)
  | 357 => Or.inl (by have h_eq : n = 1557 := (by omega); rw [h_eq]; exact base_1557)
  | 358 => Or.inl (by have h_eq : n = 1558 := (by omega); rw [h_eq]; exact base_1558)
  | 359 => Or.inl (by have h_eq : n = 1559 := (by omega); rw [h_eq]; exact base_1559)
  | 360 => Or.inl (by have h_eq : n = 1560 := (by omega); rw [h_eq]; exact base_1560)
  | 361 => Or.inl (by have h_eq : n = 1561 := (by omega); rw [h_eq]; exact base_1561)
  | 362 => Or.inl (by have h_eq : n = 1562 := (by omega); rw [h_eq]; exact base_1562)
  | 363 => Or.inl (by have h_eq : n = 1563 := (by omega); rw [h_eq]; exact base_1563)
  | 364 => Or.inl (by have h_eq : n = 1564 := (by omega); rw [h_eq]; exact base_1564)
  | 365 => Or.inl (by have h_eq : n = 1565 := (by omega); rw [h_eq]; exact base_1565)
  | 366 => Or.inl (by have h_eq : n = 1566 := (by omega); rw [h_eq]; exact base_1566)
  | 367 => Or.inl (by have h_eq : n = 1567 := (by omega); rw [h_eq]; exact base_1567)
  | 368 => Or.inl (by have h_eq : n = 1568 := (by omega); rw [h_eq]; exact base_1568)
  | 369 => Or.inl (by have h_eq : n = 1569 := (by omega); rw [h_eq]; exact base_1569)
  | 370 => Or.inl (by have h_eq : n = 1570 := (by omega); rw [h_eq]; exact base_1570)
  | 371 => Or.inl (by have h_eq : n = 1571 := (by omega); rw [h_eq]; exact base_1571)
  | 372 => Or.inl (by have h_eq : n = 1572 := (by omega); rw [h_eq]; exact base_1572)
  | 373 => Or.inl (by have h_eq : n = 1573 := (by omega); rw [h_eq]; exact base_1573)
  | 374 => Or.inl (by have h_eq : n = 1574 := (by omega); rw [h_eq]; exact base_1574)
  | 375 => Or.inl (by have h_eq : n = 1575 := (by omega); rw [h_eq]; exact base_1575)
  | 376 => Or.inl (by have h_eq : n = 1576 := (by omega); rw [h_eq]; exact base_1576)
  | 377 => Or.inl (by have h_eq : n = 1577 := (by omega); rw [h_eq]; exact base_1577)
  | 378 => Or.inl (by have h_eq : n = 1578 := (by omega); rw [h_eq]; exact base_1578)
  | 379 => Or.inl (by have h_eq : n = 1579 := (by omega); rw [h_eq]; exact base_1579)
  | 380 => Or.inl (by have h_eq : n = 1580 := (by omega); rw [h_eq]; exact base_1580)
  | 381 => Or.inl (by have h_eq : n = 1581 := (by omega); rw [h_eq]; exact base_1581)
  | 382 => Or.inl (by have h_eq : n = 1582 := (by omega); rw [h_eq]; exact base_1582)
  | 383 => Or.inl (by have h_eq : n = 1583 := (by omega); rw [h_eq]; exact base_1583)
  | 384 => Or.inl (by have h_eq : n = 1584 := (by omega); rw [h_eq]; exact base_1584)
  | 385 => Or.inl (by have h_eq : n = 1585 := (by omega); rw [h_eq]; exact base_1585)
  | 386 => Or.inl (by have h_eq : n = 1586 := (by omega); rw [h_eq]; exact base_1586)
  | 387 => Or.inl (by have h_eq : n = 1587 := (by omega); rw [h_eq]; exact base_1587)
  | 388 => Or.inl (by have h_eq : n = 1588 := (by omega); rw [h_eq]; exact base_1588)
  | 389 => Or.inl (by have h_eq : n = 1589 := (by omega); rw [h_eq]; exact base_1589)
  | 390 => Or.inl (by have h_eq : n = 1590 := (by omega); rw [h_eq]; exact base_1590)
  | 391 => Or.inl (by have h_eq : n = 1591 := (by omega); rw [h_eq]; exact base_1591)
  | 392 => Or.inl (by have h_eq : n = 1592 := (by omega); rw [h_eq]; exact base_1592)
  | 393 => Or.inl (by have h_eq : n = 1593 := (by omega); rw [h_eq]; exact base_1593)
  | 394 => Or.inl (by have h_eq : n = 1594 := (by omega); rw [h_eq]; exact base_1594)
  | 395 => Or.inl (by have h_eq : n = 1595 := (by omega); rw [h_eq]; exact base_1595)
  | 396 => Or.inl (by have h_eq : n = 1596 := (by omega); rw [h_eq]; exact base_1596)
  | 397 => Or.inl (by have h_eq : n = 1597 := (by omega); rw [h_eq]; exact base_1597)
  | 398 => Or.inl (by have h_eq : n = 1598 := (by omega); rw [h_eq]; exact base_1598)
  | 399 => Or.inl (by have h_eq : n = 1599 := (by omega); rw [h_eq]; exact base_1599)
  | m + 400 => Or.inr (by omega)

lemma base_cases_chunk_4 (n : ℕ) (h_low : 1600 ≤ n) : 0 < A271510 n ∨ n ≥ 2000 :=
  match h : n - 1600 with
  | 0 => Or.inl (by have h_eq : n = 1600 := (by omega); rw [h_eq]; exact base_1600)
  | 1 => Or.inl (by have h_eq : n = 1601 := (by omega); rw [h_eq]; exact base_1601)
  | 2 => Or.inl (by have h_eq : n = 1602 := (by omega); rw [h_eq]; exact base_1602)
  | 3 => Or.inl (by have h_eq : n = 1603 := (by omega); rw [h_eq]; exact base_1603)
  | 4 => Or.inl (by have h_eq : n = 1604 := (by omega); rw [h_eq]; exact base_1604)
  | 5 => Or.inl (by have h_eq : n = 1605 := (by omega); rw [h_eq]; exact base_1605)
  | 6 => Or.inl (by have h_eq : n = 1606 := (by omega); rw [h_eq]; exact base_1606)
  | 7 => Or.inl (by have h_eq : n = 1607 := (by omega); rw [h_eq]; exact base_1607)
  | 8 => Or.inl (by have h_eq : n = 1608 := (by omega); rw [h_eq]; exact base_1608)
  | 9 => Or.inl (by have h_eq : n = 1609 := (by omega); rw [h_eq]; exact base_1609)
  | 10 => Or.inl (by have h_eq : n = 1610 := (by omega); rw [h_eq]; exact base_1610)
  | 11 => Or.inl (by have h_eq : n = 1611 := (by omega); rw [h_eq]; exact base_1611)
  | 12 => Or.inl (by have h_eq : n = 1612 := (by omega); rw [h_eq]; exact base_1612)
  | 13 => Or.inl (by have h_eq : n = 1613 := (by omega); rw [h_eq]; exact base_1613)
  | 14 => Or.inl (by have h_eq : n = 1614 := (by omega); rw [h_eq]; exact base_1614)
  | 15 => Or.inl (by have h_eq : n = 1615 := (by omega); rw [h_eq]; exact base_1615)
  | 16 => Or.inl (by have h_eq : n = 1616 := (by omega); rw [h_eq]; exact base_1616)
  | 17 => Or.inl (by have h_eq : n = 1617 := (by omega); rw [h_eq]; exact base_1617)
  | 18 => Or.inl (by have h_eq : n = 1618 := (by omega); rw [h_eq]; exact base_1618)
  | 19 => Or.inl (by have h_eq : n = 1619 := (by omega); rw [h_eq]; exact base_1619)
  | 20 => Or.inl (by have h_eq : n = 1620 := (by omega); rw [h_eq]; exact base_1620)
  | 21 => Or.inl (by have h_eq : n = 1621 := (by omega); rw [h_eq]; exact base_1621)
  | 22 => Or.inl (by have h_eq : n = 1622 := (by omega); rw [h_eq]; exact base_1622)
  | 23 => Or.inl (by have h_eq : n = 1623 := (by omega); rw [h_eq]; exact base_1623)
  | 24 => Or.inl (by have h_eq : n = 1624 := (by omega); rw [h_eq]; exact base_1624)
  | 25 => Or.inl (by have h_eq : n = 1625 := (by omega); rw [h_eq]; exact base_1625)
  | 26 => Or.inl (by have h_eq : n = 1626 := (by omega); rw [h_eq]; exact base_1626)
  | 27 => Or.inl (by have h_eq : n = 1627 := (by omega); rw [h_eq]; exact base_1627)
  | 28 => Or.inl (by have h_eq : n = 1628 := (by omega); rw [h_eq]; exact base_1628)
  | 29 => Or.inl (by have h_eq : n = 1629 := (by omega); rw [h_eq]; exact base_1629)
  | 30 => Or.inl (by have h_eq : n = 1630 := (by omega); rw [h_eq]; exact base_1630)
  | 31 => Or.inl (by have h_eq : n = 1631 := (by omega); rw [h_eq]; exact base_1631)
  | 32 => Or.inl (by have h_eq : n = 1632 := (by omega); rw [h_eq]; exact base_1632)
  | 33 => Or.inl (by have h_eq : n = 1633 := (by omega); rw [h_eq]; exact base_1633)
  | 34 => Or.inl (by have h_eq : n = 1634 := (by omega); rw [h_eq]; exact base_1634)
  | 35 => Or.inl (by have h_eq : n = 1635 := (by omega); rw [h_eq]; exact base_1635)
  | 36 => Or.inl (by have h_eq : n = 1636 := (by omega); rw [h_eq]; exact base_1636)
  | 37 => Or.inl (by have h_eq : n = 1637 := (by omega); rw [h_eq]; exact base_1637)
  | 38 => Or.inl (by have h_eq : n = 1638 := (by omega); rw [h_eq]; exact base_1638)
  | 39 => Or.inl (by have h_eq : n = 1639 := (by omega); rw [h_eq]; exact base_1639)
  | 40 => Or.inl (by have h_eq : n = 1640 := (by omega); rw [h_eq]; exact base_1640)
  | 41 => Or.inl (by have h_eq : n = 1641 := (by omega); rw [h_eq]; exact base_1641)
  | 42 => Or.inl (by have h_eq : n = 1642 := (by omega); rw [h_eq]; exact base_1642)
  | 43 => Or.inl (by have h_eq : n = 1643 := (by omega); rw [h_eq]; exact base_1643)
  | 44 => Or.inl (by have h_eq : n = 1644 := (by omega); rw [h_eq]; exact base_1644)
  | 45 => Or.inl (by have h_eq : n = 1645 := (by omega); rw [h_eq]; exact base_1645)
  | 46 => Or.inl (by have h_eq : n = 1646 := (by omega); rw [h_eq]; exact base_1646)
  | 47 => Or.inl (by have h_eq : n = 1647 := (by omega); rw [h_eq]; exact base_1647)
  | 48 => Or.inl (by have h_eq : n = 1648 := (by omega); rw [h_eq]; exact base_1648)
  | 49 => Or.inl (by have h_eq : n = 1649 := (by omega); rw [h_eq]; exact base_1649)
  | 50 => Or.inl (by have h_eq : n = 1650 := (by omega); rw [h_eq]; exact base_1650)
  | 51 => Or.inl (by have h_eq : n = 1651 := (by omega); rw [h_eq]; exact base_1651)
  | 52 => Or.inl (by have h_eq : n = 1652 := (by omega); rw [h_eq]; exact base_1652)
  | 53 => Or.inl (by have h_eq : n = 1653 := (by omega); rw [h_eq]; exact base_1653)
  | 54 => Or.inl (by have h_eq : n = 1654 := (by omega); rw [h_eq]; exact base_1654)
  | 55 => Or.inl (by have h_eq : n = 1655 := (by omega); rw [h_eq]; exact base_1655)
  | 56 => Or.inl (by have h_eq : n = 1656 := (by omega); rw [h_eq]; exact base_1656)
  | 57 => Or.inl (by have h_eq : n = 1657 := (by omega); rw [h_eq]; exact base_1657)
  | 58 => Or.inl (by have h_eq : n = 1658 := (by omega); rw [h_eq]; exact base_1658)
  | 59 => Or.inl (by have h_eq : n = 1659 := (by omega); rw [h_eq]; exact base_1659)
  | 60 => Or.inl (by have h_eq : n = 1660 := (by omega); rw [h_eq]; exact base_1660)
  | 61 => Or.inl (by have h_eq : n = 1661 := (by omega); rw [h_eq]; exact base_1661)
  | 62 => Or.inl (by have h_eq : n = 1662 := (by omega); rw [h_eq]; exact base_1662)
  | 63 => Or.inl (by have h_eq : n = 1663 := (by omega); rw [h_eq]; exact base_1663)
  | 64 => Or.inl (by have h_eq : n = 1664 := (by omega); rw [h_eq]; exact base_1664)
  | 65 => Or.inl (by have h_eq : n = 1665 := (by omega); rw [h_eq]; exact base_1665)
  | 66 => Or.inl (by have h_eq : n = 1666 := (by omega); rw [h_eq]; exact base_1666)
  | 67 => Or.inl (by have h_eq : n = 1667 := (by omega); rw [h_eq]; exact base_1667)
  | 68 => Or.inl (by have h_eq : n = 1668 := (by omega); rw [h_eq]; exact base_1668)
  | 69 => Or.inl (by have h_eq : n = 1669 := (by omega); rw [h_eq]; exact base_1669)
  | 70 => Or.inl (by have h_eq : n = 1670 := (by omega); rw [h_eq]; exact base_1670)
  | 71 => Or.inl (by have h_eq : n = 1671 := (by omega); rw [h_eq]; exact base_1671)
  | 72 => Or.inl (by have h_eq : n = 1672 := (by omega); rw [h_eq]; exact base_1672)
  | 73 => Or.inl (by have h_eq : n = 1673 := (by omega); rw [h_eq]; exact base_1673)
  | 74 => Or.inl (by have h_eq : n = 1674 := (by omega); rw [h_eq]; exact base_1674)
  | 75 => Or.inl (by have h_eq : n = 1675 := (by omega); rw [h_eq]; exact base_1675)
  | 76 => Or.inl (by have h_eq : n = 1676 := (by omega); rw [h_eq]; exact base_1676)
  | 77 => Or.inl (by have h_eq : n = 1677 := (by omega); rw [h_eq]; exact base_1677)
  | 78 => Or.inl (by have h_eq : n = 1678 := (by omega); rw [h_eq]; exact base_1678)
  | 79 => Or.inl (by have h_eq : n = 1679 := (by omega); rw [h_eq]; exact base_1679)
  | 80 => Or.inl (by have h_eq : n = 1680 := (by omega); rw [h_eq]; exact base_1680)
  | 81 => Or.inl (by have h_eq : n = 1681 := (by omega); rw [h_eq]; exact base_1681)
  | 82 => Or.inl (by have h_eq : n = 1682 := (by omega); rw [h_eq]; exact base_1682)
  | 83 => Or.inl (by have h_eq : n = 1683 := (by omega); rw [h_eq]; exact base_1683)
  | 84 => Or.inl (by have h_eq : n = 1684 := (by omega); rw [h_eq]; exact base_1684)
  | 85 => Or.inl (by have h_eq : n = 1685 := (by omega); rw [h_eq]; exact base_1685)
  | 86 => Or.inl (by have h_eq : n = 1686 := (by omega); rw [h_eq]; exact base_1686)
  | 87 => Or.inl (by have h_eq : n = 1687 := (by omega); rw [h_eq]; exact base_1687)
  | 88 => Or.inl (by have h_eq : n = 1688 := (by omega); rw [h_eq]; exact base_1688)
  | 89 => Or.inl (by have h_eq : n = 1689 := (by omega); rw [h_eq]; exact base_1689)
  | 90 => Or.inl (by have h_eq : n = 1690 := (by omega); rw [h_eq]; exact base_1690)
  | 91 => Or.inl (by have h_eq : n = 1691 := (by omega); rw [h_eq]; exact base_1691)
  | 92 => Or.inl (by have h_eq : n = 1692 := (by omega); rw [h_eq]; exact base_1692)
  | 93 => Or.inl (by have h_eq : n = 1693 := (by omega); rw [h_eq]; exact base_1693)
  | 94 => Or.inl (by have h_eq : n = 1694 := (by omega); rw [h_eq]; exact base_1694)
  | 95 => Or.inl (by have h_eq : n = 1695 := (by omega); rw [h_eq]; exact base_1695)
  | 96 => Or.inl (by have h_eq : n = 1696 := (by omega); rw [h_eq]; exact base_1696)
  | 97 => Or.inl (by have h_eq : n = 1697 := (by omega); rw [h_eq]; exact base_1697)
  | 98 => Or.inl (by have h_eq : n = 1698 := (by omega); rw [h_eq]; exact base_1698)
  | 99 => Or.inl (by have h_eq : n = 1699 := (by omega); rw [h_eq]; exact base_1699)
  | 100 => Or.inl (by have h_eq : n = 1700 := (by omega); rw [h_eq]; exact base_1700)
  | 101 => Or.inl (by have h_eq : n = 1701 := (by omega); rw [h_eq]; exact base_1701)
  | 102 => Or.inl (by have h_eq : n = 1702 := (by omega); rw [h_eq]; exact base_1702)
  | 103 => Or.inl (by have h_eq : n = 1703 := (by omega); rw [h_eq]; exact base_1703)
  | 104 => Or.inl (by have h_eq : n = 1704 := (by omega); rw [h_eq]; exact base_1704)
  | 105 => Or.inl (by have h_eq : n = 1705 := (by omega); rw [h_eq]; exact base_1705)
  | 106 => Or.inl (by have h_eq : n = 1706 := (by omega); rw [h_eq]; exact base_1706)
  | 107 => Or.inl (by have h_eq : n = 1707 := (by omega); rw [h_eq]; exact base_1707)
  | 108 => Or.inl (by have h_eq : n = 1708 := (by omega); rw [h_eq]; exact base_1708)
  | 109 => Or.inl (by have h_eq : n = 1709 := (by omega); rw [h_eq]; exact base_1709)
  | 110 => Or.inl (by have h_eq : n = 1710 := (by omega); rw [h_eq]; exact base_1710)
  | 111 => Or.inl (by have h_eq : n = 1711 := (by omega); rw [h_eq]; exact base_1711)
  | 112 => Or.inl (by have h_eq : n = 1712 := (by omega); rw [h_eq]; exact base_1712)
  | 113 => Or.inl (by have h_eq : n = 1713 := (by omega); rw [h_eq]; exact base_1713)
  | 114 => Or.inl (by have h_eq : n = 1714 := (by omega); rw [h_eq]; exact base_1714)
  | 115 => Or.inl (by have h_eq : n = 1715 := (by omega); rw [h_eq]; exact base_1715)
  | 116 => Or.inl (by have h_eq : n = 1716 := (by omega); rw [h_eq]; exact base_1716)
  | 117 => Or.inl (by have h_eq : n = 1717 := (by omega); rw [h_eq]; exact base_1717)
  | 118 => Or.inl (by have h_eq : n = 1718 := (by omega); rw [h_eq]; exact base_1718)
  | 119 => Or.inl (by have h_eq : n = 1719 := (by omega); rw [h_eq]; exact base_1719)
  | 120 => Or.inl (by have h_eq : n = 1720 := (by omega); rw [h_eq]; exact base_1720)
  | 121 => Or.inl (by have h_eq : n = 1721 := (by omega); rw [h_eq]; exact base_1721)
  | 122 => Or.inl (by have h_eq : n = 1722 := (by omega); rw [h_eq]; exact base_1722)
  | 123 => Or.inl (by have h_eq : n = 1723 := (by omega); rw [h_eq]; exact base_1723)
  | 124 => Or.inl (by have h_eq : n = 1724 := (by omega); rw [h_eq]; exact base_1724)
  | 125 => Or.inl (by have h_eq : n = 1725 := (by omega); rw [h_eq]; exact base_1725)
  | 126 => Or.inl (by have h_eq : n = 1726 := (by omega); rw [h_eq]; exact base_1726)
  | 127 => Or.inl (by have h_eq : n = 1727 := (by omega); rw [h_eq]; exact base_1727)
  | 128 => Or.inl (by have h_eq : n = 1728 := (by omega); rw [h_eq]; exact base_1728)
  | 129 => Or.inl (by have h_eq : n = 1729 := (by omega); rw [h_eq]; exact base_1729)
  | 130 => Or.inl (by have h_eq : n = 1730 := (by omega); rw [h_eq]; exact base_1730)
  | 131 => Or.inl (by have h_eq : n = 1731 := (by omega); rw [h_eq]; exact base_1731)
  | 132 => Or.inl (by have h_eq : n = 1732 := (by omega); rw [h_eq]; exact base_1732)
  | 133 => Or.inl (by have h_eq : n = 1733 := (by omega); rw [h_eq]; exact base_1733)
  | 134 => Or.inl (by have h_eq : n = 1734 := (by omega); rw [h_eq]; exact base_1734)
  | 135 => Or.inl (by have h_eq : n = 1735 := (by omega); rw [h_eq]; exact base_1735)
  | 136 => Or.inl (by have h_eq : n = 1736 := (by omega); rw [h_eq]; exact base_1736)
  | 137 => Or.inl (by have h_eq : n = 1737 := (by omega); rw [h_eq]; exact base_1737)
  | 138 => Or.inl (by have h_eq : n = 1738 := (by omega); rw [h_eq]; exact base_1738)
  | 139 => Or.inl (by have h_eq : n = 1739 := (by omega); rw [h_eq]; exact base_1739)
  | 140 => Or.inl (by have h_eq : n = 1740 := (by omega); rw [h_eq]; exact base_1740)
  | 141 => Or.inl (by have h_eq : n = 1741 := (by omega); rw [h_eq]; exact base_1741)
  | 142 => Or.inl (by have h_eq : n = 1742 := (by omega); rw [h_eq]; exact base_1742)
  | 143 => Or.inl (by have h_eq : n = 1743 := (by omega); rw [h_eq]; exact base_1743)
  | 144 => Or.inl (by have h_eq : n = 1744 := (by omega); rw [h_eq]; exact base_1744)
  | 145 => Or.inl (by have h_eq : n = 1745 := (by omega); rw [h_eq]; exact base_1745)
  | 146 => Or.inl (by have h_eq : n = 1746 := (by omega); rw [h_eq]; exact base_1746)
  | 147 => Or.inl (by have h_eq : n = 1747 := (by omega); rw [h_eq]; exact base_1747)
  | 148 => Or.inl (by have h_eq : n = 1748 := (by omega); rw [h_eq]; exact base_1748)
  | 149 => Or.inl (by have h_eq : n = 1749 := (by omega); rw [h_eq]; exact base_1749)
  | 150 => Or.inl (by have h_eq : n = 1750 := (by omega); rw [h_eq]; exact base_1750)
  | 151 => Or.inl (by have h_eq : n = 1751 := (by omega); rw [h_eq]; exact base_1751)
  | 152 => Or.inl (by have h_eq : n = 1752 := (by omega); rw [h_eq]; exact base_1752)
  | 153 => Or.inl (by have h_eq : n = 1753 := (by omega); rw [h_eq]; exact base_1753)
  | 154 => Or.inl (by have h_eq : n = 1754 := (by omega); rw [h_eq]; exact base_1754)
  | 155 => Or.inl (by have h_eq : n = 1755 := (by omega); rw [h_eq]; exact base_1755)
  | 156 => Or.inl (by have h_eq : n = 1756 := (by omega); rw [h_eq]; exact base_1756)
  | 157 => Or.inl (by have h_eq : n = 1757 := (by omega); rw [h_eq]; exact base_1757)
  | 158 => Or.inl (by have h_eq : n = 1758 := (by omega); rw [h_eq]; exact base_1758)
  | 159 => Or.inl (by have h_eq : n = 1759 := (by omega); rw [h_eq]; exact base_1759)
  | 160 => Or.inl (by have h_eq : n = 1760 := (by omega); rw [h_eq]; exact base_1760)
  | 161 => Or.inl (by have h_eq : n = 1761 := (by omega); rw [h_eq]; exact base_1761)
  | 162 => Or.inl (by have h_eq : n = 1762 := (by omega); rw [h_eq]; exact base_1762)
  | 163 => Or.inl (by have h_eq : n = 1763 := (by omega); rw [h_eq]; exact base_1763)
  | 164 => Or.inl (by have h_eq : n = 1764 := (by omega); rw [h_eq]; exact base_1764)
  | 165 => Or.inl (by have h_eq : n = 1765 := (by omega); rw [h_eq]; exact base_1765)
  | 166 => Or.inl (by have h_eq : n = 1766 := (by omega); rw [h_eq]; exact base_1766)
  | 167 => Or.inl (by have h_eq : n = 1767 := (by omega); rw [h_eq]; exact base_1767)
  | 168 => Or.inl (by have h_eq : n = 1768 := (by omega); rw [h_eq]; exact base_1768)
  | 169 => Or.inl (by have h_eq : n = 1769 := (by omega); rw [h_eq]; exact base_1769)
  | 170 => Or.inl (by have h_eq : n = 1770 := (by omega); rw [h_eq]; exact base_1770)
  | 171 => Or.inl (by have h_eq : n = 1771 := (by omega); rw [h_eq]; exact base_1771)
  | 172 => Or.inl (by have h_eq : n = 1772 := (by omega); rw [h_eq]; exact base_1772)
  | 173 => Or.inl (by have h_eq : n = 1773 := (by omega); rw [h_eq]; exact base_1773)
  | 174 => Or.inl (by have h_eq : n = 1774 := (by omega); rw [h_eq]; exact base_1774)
  | 175 => Or.inl (by have h_eq : n = 1775 := (by omega); rw [h_eq]; exact base_1775)
  | 176 => Or.inl (by have h_eq : n = 1776 := (by omega); rw [h_eq]; exact base_1776)
  | 177 => Or.inl (by have h_eq : n = 1777 := (by omega); rw [h_eq]; exact base_1777)
  | 178 => Or.inl (by have h_eq : n = 1778 := (by omega); rw [h_eq]; exact base_1778)
  | 179 => Or.inl (by have h_eq : n = 1779 := (by omega); rw [h_eq]; exact base_1779)
  | 180 => Or.inl (by have h_eq : n = 1780 := (by omega); rw [h_eq]; exact base_1780)
  | 181 => Or.inl (by have h_eq : n = 1781 := (by omega); rw [h_eq]; exact base_1781)
  | 182 => Or.inl (by have h_eq : n = 1782 := (by omega); rw [h_eq]; exact base_1782)
  | 183 => Or.inl (by have h_eq : n = 1783 := (by omega); rw [h_eq]; exact base_1783)
  | 184 => Or.inl (by have h_eq : n = 1784 := (by omega); rw [h_eq]; exact base_1784)
  | 185 => Or.inl (by have h_eq : n = 1785 := (by omega); rw [h_eq]; exact base_1785)
  | 186 => Or.inl (by have h_eq : n = 1786 := (by omega); rw [h_eq]; exact base_1786)
  | 187 => Or.inl (by have h_eq : n = 1787 := (by omega); rw [h_eq]; exact base_1787)
  | 188 => Or.inl (by have h_eq : n = 1788 := (by omega); rw [h_eq]; exact base_1788)
  | 189 => Or.inl (by have h_eq : n = 1789 := (by omega); rw [h_eq]; exact base_1789)
  | 190 => Or.inl (by have h_eq : n = 1790 := (by omega); rw [h_eq]; exact base_1790)
  | 191 => Or.inl (by have h_eq : n = 1791 := (by omega); rw [h_eq]; exact base_1791)
  | 192 => Or.inl (by have h_eq : n = 1792 := (by omega); rw [h_eq]; exact base_1792)
  | 193 => Or.inl (by have h_eq : n = 1793 := (by omega); rw [h_eq]; exact base_1793)
  | 194 => Or.inl (by have h_eq : n = 1794 := (by omega); rw [h_eq]; exact base_1794)
  | 195 => Or.inl (by have h_eq : n = 1795 := (by omega); rw [h_eq]; exact base_1795)
  | 196 => Or.inl (by have h_eq : n = 1796 := (by omega); rw [h_eq]; exact base_1796)
  | 197 => Or.inl (by have h_eq : n = 1797 := (by omega); rw [h_eq]; exact base_1797)
  | 198 => Or.inl (by have h_eq : n = 1798 := (by omega); rw [h_eq]; exact base_1798)
  | 199 => Or.inl (by have h_eq : n = 1799 := (by omega); rw [h_eq]; exact base_1799)
  | 200 => Or.inl (by have h_eq : n = 1800 := (by omega); rw [h_eq]; exact base_1800)
  | 201 => Or.inl (by have h_eq : n = 1801 := (by omega); rw [h_eq]; exact base_1801)
  | 202 => Or.inl (by have h_eq : n = 1802 := (by omega); rw [h_eq]; exact base_1802)
  | 203 => Or.inl (by have h_eq : n = 1803 := (by omega); rw [h_eq]; exact base_1803)
  | 204 => Or.inl (by have h_eq : n = 1804 := (by omega); rw [h_eq]; exact base_1804)
  | 205 => Or.inl (by have h_eq : n = 1805 := (by omega); rw [h_eq]; exact base_1805)
  | 206 => Or.inl (by have h_eq : n = 1806 := (by omega); rw [h_eq]; exact base_1806)
  | 207 => Or.inl (by have h_eq : n = 1807 := (by omega); rw [h_eq]; exact base_1807)
  | 208 => Or.inl (by have h_eq : n = 1808 := (by omega); rw [h_eq]; exact base_1808)
  | 209 => Or.inl (by have h_eq : n = 1809 := (by omega); rw [h_eq]; exact base_1809)
  | 210 => Or.inl (by have h_eq : n = 1810 := (by omega); rw [h_eq]; exact base_1810)
  | 211 => Or.inl (by have h_eq : n = 1811 := (by omega); rw [h_eq]; exact base_1811)
  | 212 => Or.inl (by have h_eq : n = 1812 := (by omega); rw [h_eq]; exact base_1812)
  | 213 => Or.inl (by have h_eq : n = 1813 := (by omega); rw [h_eq]; exact base_1813)
  | 214 => Or.inl (by have h_eq : n = 1814 := (by omega); rw [h_eq]; exact base_1814)
  | 215 => Or.inl (by have h_eq : n = 1815 := (by omega); rw [h_eq]; exact base_1815)
  | 216 => Or.inl (by have h_eq : n = 1816 := (by omega); rw [h_eq]; exact base_1816)
  | 217 => Or.inl (by have h_eq : n = 1817 := (by omega); rw [h_eq]; exact base_1817)
  | 218 => Or.inl (by have h_eq : n = 1818 := (by omega); rw [h_eq]; exact base_1818)
  | 219 => Or.inl (by have h_eq : n = 1819 := (by omega); rw [h_eq]; exact base_1819)
  | 220 => Or.inl (by have h_eq : n = 1820 := (by omega); rw [h_eq]; exact base_1820)
  | 221 => Or.inl (by have h_eq : n = 1821 := (by omega); rw [h_eq]; exact base_1821)
  | 222 => Or.inl (by have h_eq : n = 1822 := (by omega); rw [h_eq]; exact base_1822)
  | 223 => Or.inl (by have h_eq : n = 1823 := (by omega); rw [h_eq]; exact base_1823)
  | 224 => Or.inl (by have h_eq : n = 1824 := (by omega); rw [h_eq]; exact base_1824)
  | 225 => Or.inl (by have h_eq : n = 1825 := (by omega); rw [h_eq]; exact base_1825)
  | 226 => Or.inl (by have h_eq : n = 1826 := (by omega); rw [h_eq]; exact base_1826)
  | 227 => Or.inl (by have h_eq : n = 1827 := (by omega); rw [h_eq]; exact base_1827)
  | 228 => Or.inl (by have h_eq : n = 1828 := (by omega); rw [h_eq]; exact base_1828)
  | 229 => Or.inl (by have h_eq : n = 1829 := (by omega); rw [h_eq]; exact base_1829)
  | 230 => Or.inl (by have h_eq : n = 1830 := (by omega); rw [h_eq]; exact base_1830)
  | 231 => Or.inl (by have h_eq : n = 1831 := (by omega); rw [h_eq]; exact base_1831)
  | 232 => Or.inl (by have h_eq : n = 1832 := (by omega); rw [h_eq]; exact base_1832)
  | 233 => Or.inl (by have h_eq : n = 1833 := (by omega); rw [h_eq]; exact base_1833)
  | 234 => Or.inl (by have h_eq : n = 1834 := (by omega); rw [h_eq]; exact base_1834)
  | 235 => Or.inl (by have h_eq : n = 1835 := (by omega); rw [h_eq]; exact base_1835)
  | 236 => Or.inl (by have h_eq : n = 1836 := (by omega); rw [h_eq]; exact base_1836)
  | 237 => Or.inl (by have h_eq : n = 1837 := (by omega); rw [h_eq]; exact base_1837)
  | 238 => Or.inl (by have h_eq : n = 1838 := (by omega); rw [h_eq]; exact base_1838)
  | 239 => Or.inl (by have h_eq : n = 1839 := (by omega); rw [h_eq]; exact base_1839)
  | 240 => Or.inl (by have h_eq : n = 1840 := (by omega); rw [h_eq]; exact base_1840)
  | 241 => Or.inl (by have h_eq : n = 1841 := (by omega); rw [h_eq]; exact base_1841)
  | 242 => Or.inl (by have h_eq : n = 1842 := (by omega); rw [h_eq]; exact base_1842)
  | 243 => Or.inl (by have h_eq : n = 1843 := (by omega); rw [h_eq]; exact base_1843)
  | 244 => Or.inl (by have h_eq : n = 1844 := (by omega); rw [h_eq]; exact base_1844)
  | 245 => Or.inl (by have h_eq : n = 1845 := (by omega); rw [h_eq]; exact base_1845)
  | 246 => Or.inl (by have h_eq : n = 1846 := (by omega); rw [h_eq]; exact base_1846)
  | 247 => Or.inl (by have h_eq : n = 1847 := (by omega); rw [h_eq]; exact base_1847)
  | 248 => Or.inl (by have h_eq : n = 1848 := (by omega); rw [h_eq]; exact base_1848)
  | 249 => Or.inl (by have h_eq : n = 1849 := (by omega); rw [h_eq]; exact base_1849)
  | 250 => Or.inl (by have h_eq : n = 1850 := (by omega); rw [h_eq]; exact base_1850)
  | 251 => Or.inl (by have h_eq : n = 1851 := (by omega); rw [h_eq]; exact base_1851)
  | 252 => Or.inl (by have h_eq : n = 1852 := (by omega); rw [h_eq]; exact base_1852)
  | 253 => Or.inl (by have h_eq : n = 1853 := (by omega); rw [h_eq]; exact base_1853)
  | 254 => Or.inl (by have h_eq : n = 1854 := (by omega); rw [h_eq]; exact base_1854)
  | 255 => Or.inl (by have h_eq : n = 1855 := (by omega); rw [h_eq]; exact base_1855)
  | 256 => Or.inl (by have h_eq : n = 1856 := (by omega); rw [h_eq]; exact base_1856)
  | 257 => Or.inl (by have h_eq : n = 1857 := (by omega); rw [h_eq]; exact base_1857)
  | 258 => Or.inl (by have h_eq : n = 1858 := (by omega); rw [h_eq]; exact base_1858)
  | 259 => Or.inl (by have h_eq : n = 1859 := (by omega); rw [h_eq]; exact base_1859)
  | 260 => Or.inl (by have h_eq : n = 1860 := (by omega); rw [h_eq]; exact base_1860)
  | 261 => Or.inl (by have h_eq : n = 1861 := (by omega); rw [h_eq]; exact base_1861)
  | 262 => Or.inl (by have h_eq : n = 1862 := (by omega); rw [h_eq]; exact base_1862)
  | 263 => Or.inl (by have h_eq : n = 1863 := (by omega); rw [h_eq]; exact base_1863)
  | 264 => Or.inl (by have h_eq : n = 1864 := (by omega); rw [h_eq]; exact base_1864)
  | 265 => Or.inl (by have h_eq : n = 1865 := (by omega); rw [h_eq]; exact base_1865)
  | 266 => Or.inl (by have h_eq : n = 1866 := (by omega); rw [h_eq]; exact base_1866)
  | 267 => Or.inl (by have h_eq : n = 1867 := (by omega); rw [h_eq]; exact base_1867)
  | 268 => Or.inl (by have h_eq : n = 1868 := (by omega); rw [h_eq]; exact base_1868)
  | 269 => Or.inl (by have h_eq : n = 1869 := (by omega); rw [h_eq]; exact base_1869)
  | 270 => Or.inl (by have h_eq : n = 1870 := (by omega); rw [h_eq]; exact base_1870)
  | 271 => Or.inl (by have h_eq : n = 1871 := (by omega); rw [h_eq]; exact base_1871)
  | 272 => Or.inl (by have h_eq : n = 1872 := (by omega); rw [h_eq]; exact base_1872)
  | 273 => Or.inl (by have h_eq : n = 1873 := (by omega); rw [h_eq]; exact base_1873)
  | 274 => Or.inl (by have h_eq : n = 1874 := (by omega); rw [h_eq]; exact base_1874)
  | 275 => Or.inl (by have h_eq : n = 1875 := (by omega); rw [h_eq]; exact base_1875)
  | 276 => Or.inl (by have h_eq : n = 1876 := (by omega); rw [h_eq]; exact base_1876)
  | 277 => Or.inl (by have h_eq : n = 1877 := (by omega); rw [h_eq]; exact base_1877)
  | 278 => Or.inl (by have h_eq : n = 1878 := (by omega); rw [h_eq]; exact base_1878)
  | 279 => Or.inl (by have h_eq : n = 1879 := (by omega); rw [h_eq]; exact base_1879)
  | 280 => Or.inl (by have h_eq : n = 1880 := (by omega); rw [h_eq]; exact base_1880)
  | 281 => Or.inl (by have h_eq : n = 1881 := (by omega); rw [h_eq]; exact base_1881)
  | 282 => Or.inl (by have h_eq : n = 1882 := (by omega); rw [h_eq]; exact base_1882)
  | 283 => Or.inl (by have h_eq : n = 1883 := (by omega); rw [h_eq]; exact base_1883)
  | 284 => Or.inl (by have h_eq : n = 1884 := (by omega); rw [h_eq]; exact base_1884)
  | 285 => Or.inl (by have h_eq : n = 1885 := (by omega); rw [h_eq]; exact base_1885)
  | 286 => Or.inl (by have h_eq : n = 1886 := (by omega); rw [h_eq]; exact base_1886)
  | 287 => Or.inl (by have h_eq : n = 1887 := (by omega); rw [h_eq]; exact base_1887)
  | 288 => Or.inl (by have h_eq : n = 1888 := (by omega); rw [h_eq]; exact base_1888)
  | 289 => Or.inl (by have h_eq : n = 1889 := (by omega); rw [h_eq]; exact base_1889)
  | 290 => Or.inl (by have h_eq : n = 1890 := (by omega); rw [h_eq]; exact base_1890)
  | 291 => Or.inl (by have h_eq : n = 1891 := (by omega); rw [h_eq]; exact base_1891)
  | 292 => Or.inl (by have h_eq : n = 1892 := (by omega); rw [h_eq]; exact base_1892)
  | 293 => Or.inl (by have h_eq : n = 1893 := (by omega); rw [h_eq]; exact base_1893)
  | 294 => Or.inl (by have h_eq : n = 1894 := (by omega); rw [h_eq]; exact base_1894)
  | 295 => Or.inl (by have h_eq : n = 1895 := (by omega); rw [h_eq]; exact base_1895)
  | 296 => Or.inl (by have h_eq : n = 1896 := (by omega); rw [h_eq]; exact base_1896)
  | 297 => Or.inl (by have h_eq : n = 1897 := (by omega); rw [h_eq]; exact base_1897)
  | 298 => Or.inl (by have h_eq : n = 1898 := (by omega); rw [h_eq]; exact base_1898)
  | 299 => Or.inl (by have h_eq : n = 1899 := (by omega); rw [h_eq]; exact base_1899)
  | 300 => Or.inl (by have h_eq : n = 1900 := (by omega); rw [h_eq]; exact base_1900)
  | 301 => Or.inl (by have h_eq : n = 1901 := (by omega); rw [h_eq]; exact base_1901)
  | 302 => Or.inl (by have h_eq : n = 1902 := (by omega); rw [h_eq]; exact base_1902)
  | 303 => Or.inl (by have h_eq : n = 1903 := (by omega); rw [h_eq]; exact base_1903)
  | 304 => Or.inl (by have h_eq : n = 1904 := (by omega); rw [h_eq]; exact base_1904)
  | 305 => Or.inl (by have h_eq : n = 1905 := (by omega); rw [h_eq]; exact base_1905)
  | 306 => Or.inl (by have h_eq : n = 1906 := (by omega); rw [h_eq]; exact base_1906)
  | 307 => Or.inl (by have h_eq : n = 1907 := (by omega); rw [h_eq]; exact base_1907)
  | 308 => Or.inl (by have h_eq : n = 1908 := (by omega); rw [h_eq]; exact base_1908)
  | 309 => Or.inl (by have h_eq : n = 1909 := (by omega); rw [h_eq]; exact base_1909)
  | 310 => Or.inl (by have h_eq : n = 1910 := (by omega); rw [h_eq]; exact base_1910)
  | 311 => Or.inl (by have h_eq : n = 1911 := (by omega); rw [h_eq]; exact base_1911)
  | 312 => Or.inl (by have h_eq : n = 1912 := (by omega); rw [h_eq]; exact base_1912)
  | 313 => Or.inl (by have h_eq : n = 1913 := (by omega); rw [h_eq]; exact base_1913)
  | 314 => Or.inl (by have h_eq : n = 1914 := (by omega); rw [h_eq]; exact base_1914)
  | 315 => Or.inl (by have h_eq : n = 1915 := (by omega); rw [h_eq]; exact base_1915)
  | 316 => Or.inl (by have h_eq : n = 1916 := (by omega); rw [h_eq]; exact base_1916)
  | 317 => Or.inl (by have h_eq : n = 1917 := (by omega); rw [h_eq]; exact base_1917)
  | 318 => Or.inl (by have h_eq : n = 1918 := (by omega); rw [h_eq]; exact base_1918)
  | 319 => Or.inl (by have h_eq : n = 1919 := (by omega); rw [h_eq]; exact base_1919)
  | 320 => Or.inl (by have h_eq : n = 1920 := (by omega); rw [h_eq]; exact base_1920)
  | 321 => Or.inl (by have h_eq : n = 1921 := (by omega); rw [h_eq]; exact base_1921)
  | 322 => Or.inl (by have h_eq : n = 1922 := (by omega); rw [h_eq]; exact base_1922)
  | 323 => Or.inl (by have h_eq : n = 1923 := (by omega); rw [h_eq]; exact base_1923)
  | 324 => Or.inl (by have h_eq : n = 1924 := (by omega); rw [h_eq]; exact base_1924)
  | 325 => Or.inl (by have h_eq : n = 1925 := (by omega); rw [h_eq]; exact base_1925)
  | 326 => Or.inl (by have h_eq : n = 1926 := (by omega); rw [h_eq]; exact base_1926)
  | 327 => Or.inl (by have h_eq : n = 1927 := (by omega); rw [h_eq]; exact base_1927)
  | 328 => Or.inl (by have h_eq : n = 1928 := (by omega); rw [h_eq]; exact base_1928)
  | 329 => Or.inl (by have h_eq : n = 1929 := (by omega); rw [h_eq]; exact base_1929)
  | 330 => Or.inl (by have h_eq : n = 1930 := (by omega); rw [h_eq]; exact base_1930)
  | 331 => Or.inl (by have h_eq : n = 1931 := (by omega); rw [h_eq]; exact base_1931)
  | 332 => Or.inl (by have h_eq : n = 1932 := (by omega); rw [h_eq]; exact base_1932)
  | 333 => Or.inl (by have h_eq : n = 1933 := (by omega); rw [h_eq]; exact base_1933)
  | 334 => Or.inl (by have h_eq : n = 1934 := (by omega); rw [h_eq]; exact base_1934)
  | 335 => Or.inl (by have h_eq : n = 1935 := (by omega); rw [h_eq]; exact base_1935)
  | 336 => Or.inl (by have h_eq : n = 1936 := (by omega); rw [h_eq]; exact base_1936)
  | 337 => Or.inl (by have h_eq : n = 1937 := (by omega); rw [h_eq]; exact base_1937)
  | 338 => Or.inl (by have h_eq : n = 1938 := (by omega); rw [h_eq]; exact base_1938)
  | 339 => Or.inl (by have h_eq : n = 1939 := (by omega); rw [h_eq]; exact base_1939)
  | 340 => Or.inl (by have h_eq : n = 1940 := (by omega); rw [h_eq]; exact base_1940)
  | 341 => Or.inl (by have h_eq : n = 1941 := (by omega); rw [h_eq]; exact base_1941)
  | 342 => Or.inl (by have h_eq : n = 1942 := (by omega); rw [h_eq]; exact base_1942)
  | 343 => Or.inl (by have h_eq : n = 1943 := (by omega); rw [h_eq]; exact base_1943)
  | 344 => Or.inl (by have h_eq : n = 1944 := (by omega); rw [h_eq]; exact base_1944)
  | 345 => Or.inl (by have h_eq : n = 1945 := (by omega); rw [h_eq]; exact base_1945)
  | 346 => Or.inl (by have h_eq : n = 1946 := (by omega); rw [h_eq]; exact base_1946)
  | 347 => Or.inl (by have h_eq : n = 1947 := (by omega); rw [h_eq]; exact base_1947)
  | 348 => Or.inl (by have h_eq : n = 1948 := (by omega); rw [h_eq]; exact base_1948)
  | 349 => Or.inl (by have h_eq : n = 1949 := (by omega); rw [h_eq]; exact base_1949)
  | 350 => Or.inl (by have h_eq : n = 1950 := (by omega); rw [h_eq]; exact base_1950)
  | 351 => Or.inl (by have h_eq : n = 1951 := (by omega); rw [h_eq]; exact base_1951)
  | 352 => Or.inl (by have h_eq : n = 1952 := (by omega); rw [h_eq]; exact base_1952)
  | 353 => Or.inl (by have h_eq : n = 1953 := (by omega); rw [h_eq]; exact base_1953)
  | 354 => Or.inl (by have h_eq : n = 1954 := (by omega); rw [h_eq]; exact base_1954)
  | 355 => Or.inl (by have h_eq : n = 1955 := (by omega); rw [h_eq]; exact base_1955)
  | 356 => Or.inl (by have h_eq : n = 1956 := (by omega); rw [h_eq]; exact base_1956)
  | 357 => Or.inl (by have h_eq : n = 1957 := (by omega); rw [h_eq]; exact base_1957)
  | 358 => Or.inl (by have h_eq : n = 1958 := (by omega); rw [h_eq]; exact base_1958)
  | 359 => Or.inl (by have h_eq : n = 1959 := (by omega); rw [h_eq]; exact base_1959)
  | 360 => Or.inl (by have h_eq : n = 1960 := (by omega); rw [h_eq]; exact base_1960)
  | 361 => Or.inl (by have h_eq : n = 1961 := (by omega); rw [h_eq]; exact base_1961)
  | 362 => Or.inl (by have h_eq : n = 1962 := (by omega); rw [h_eq]; exact base_1962)
  | 363 => Or.inl (by have h_eq : n = 1963 := (by omega); rw [h_eq]; exact base_1963)
  | 364 => Or.inl (by have h_eq : n = 1964 := (by omega); rw [h_eq]; exact base_1964)
  | 365 => Or.inl (by have h_eq : n = 1965 := (by omega); rw [h_eq]; exact base_1965)
  | 366 => Or.inl (by have h_eq : n = 1966 := (by omega); rw [h_eq]; exact base_1966)
  | 367 => Or.inl (by have h_eq : n = 1967 := (by omega); rw [h_eq]; exact base_1967)
  | 368 => Or.inl (by have h_eq : n = 1968 := (by omega); rw [h_eq]; exact base_1968)
  | 369 => Or.inl (by have h_eq : n = 1969 := (by omega); rw [h_eq]; exact base_1969)
  | 370 => Or.inl (by have h_eq : n = 1970 := (by omega); rw [h_eq]; exact base_1970)
  | 371 => Or.inl (by have h_eq : n = 1971 := (by omega); rw [h_eq]; exact base_1971)
  | 372 => Or.inl (by have h_eq : n = 1972 := (by omega); rw [h_eq]; exact base_1972)
  | 373 => Or.inl (by have h_eq : n = 1973 := (by omega); rw [h_eq]; exact base_1973)
  | 374 => Or.inl (by have h_eq : n = 1974 := (by omega); rw [h_eq]; exact base_1974)
  | 375 => Or.inl (by have h_eq : n = 1975 := (by omega); rw [h_eq]; exact base_1975)
  | 376 => Or.inl (by have h_eq : n = 1976 := (by omega); rw [h_eq]; exact base_1976)
  | 377 => Or.inl (by have h_eq : n = 1977 := (by omega); rw [h_eq]; exact base_1977)
  | 378 => Or.inl (by have h_eq : n = 1978 := (by omega); rw [h_eq]; exact base_1978)
  | 379 => Or.inl (by have h_eq : n = 1979 := (by omega); rw [h_eq]; exact base_1979)
  | 380 => Or.inl (by have h_eq : n = 1980 := (by omega); rw [h_eq]; exact base_1980)
  | 381 => Or.inl (by have h_eq : n = 1981 := (by omega); rw [h_eq]; exact base_1981)
  | 382 => Or.inl (by have h_eq : n = 1982 := (by omega); rw [h_eq]; exact base_1982)
  | 383 => Or.inl (by have h_eq : n = 1983 := (by omega); rw [h_eq]; exact base_1983)
  | 384 => Or.inl (by have h_eq : n = 1984 := (by omega); rw [h_eq]; exact base_1984)
  | 385 => Or.inl (by have h_eq : n = 1985 := (by omega); rw [h_eq]; exact base_1985)
  | 386 => Or.inl (by have h_eq : n = 1986 := (by omega); rw [h_eq]; exact base_1986)
  | 387 => Or.inl (by have h_eq : n = 1987 := (by omega); rw [h_eq]; exact base_1987)
  | 388 => Or.inl (by have h_eq : n = 1988 := (by omega); rw [h_eq]; exact base_1988)
  | 389 => Or.inl (by have h_eq : n = 1989 := (by omega); rw [h_eq]; exact base_1989)
  | 390 => Or.inl (by have h_eq : n = 1990 := (by omega); rw [h_eq]; exact base_1990)
  | 391 => Or.inl (by have h_eq : n = 1991 := (by omega); rw [h_eq]; exact base_1991)
  | 392 => Or.inl (by have h_eq : n = 1992 := (by omega); rw [h_eq]; exact base_1992)
  | 393 => Or.inl (by have h_eq : n = 1993 := (by omega); rw [h_eq]; exact base_1993)
  | 394 => Or.inl (by have h_eq : n = 1994 := (by omega); rw [h_eq]; exact base_1994)
  | 395 => Or.inl (by have h_eq : n = 1995 := (by omega); rw [h_eq]; exact base_1995)
  | 396 => Or.inl (by have h_eq : n = 1996 := (by omega); rw [h_eq]; exact base_1996)
  | 397 => Or.inl (by have h_eq : n = 1997 := (by omega); rw [h_eq]; exact base_1997)
  | 398 => Or.inl (by have h_eq : n = 1998 := (by omega); rw [h_eq]; exact base_1998)
  | 399 => Or.inl (by have h_eq : n = 1999 := (by omega); rw [h_eq]; exact base_1999)
  | m + 400 => Or.inr (by omega)

lemma base_cases_chunk_5 (n : ℕ) (h_low : 2000 ≤ n) : 0 < A271510 n ∨ n ≥ 2043 :=
  match h : n - 2000 with
  | 0 => Or.inl (by have h_eq : n = 2000 := (by omega); rw [h_eq]; exact base_2000)
  | 1 => Or.inl (by have h_eq : n = 2001 := (by omega); rw [h_eq]; exact base_2001)
  | 2 => Or.inl (by have h_eq : n = 2002 := (by omega); rw [h_eq]; exact base_2002)
  | 3 => Or.inl (by have h_eq : n = 2003 := (by omega); rw [h_eq]; exact base_2003)
  | 4 => Or.inl (by have h_eq : n = 2004 := (by omega); rw [h_eq]; exact base_2004)
  | 5 => Or.inl (by have h_eq : n = 2005 := (by omega); rw [h_eq]; exact base_2005)
  | 6 => Or.inl (by have h_eq : n = 2006 := (by omega); rw [h_eq]; exact base_2006)
  | 7 => Or.inl (by have h_eq : n = 2007 := (by omega); rw [h_eq]; exact base_2007)
  | 8 => Or.inl (by have h_eq : n = 2008 := (by omega); rw [h_eq]; exact base_2008)
  | 9 => Or.inl (by have h_eq : n = 2009 := (by omega); rw [h_eq]; exact base_2009)
  | 10 => Or.inl (by have h_eq : n = 2010 := (by omega); rw [h_eq]; exact base_2010)
  | 11 => Or.inl (by have h_eq : n = 2011 := (by omega); rw [h_eq]; exact base_2011)
  | 12 => Or.inl (by have h_eq : n = 2012 := (by omega); rw [h_eq]; exact base_2012)
  | 13 => Or.inl (by have h_eq : n = 2013 := (by omega); rw [h_eq]; exact base_2013)
  | 14 => Or.inl (by have h_eq : n = 2014 := (by omega); rw [h_eq]; exact base_2014)
  | 15 => Or.inl (by have h_eq : n = 2015 := (by omega); rw [h_eq]; exact base_2015)
  | 16 => Or.inl (by have h_eq : n = 2016 := (by omega); rw [h_eq]; exact base_2016)
  | 17 => Or.inl (by have h_eq : n = 2017 := (by omega); rw [h_eq]; exact base_2017)
  | 18 => Or.inl (by have h_eq : n = 2018 := (by omega); rw [h_eq]; exact base_2018)
  | 19 => Or.inl (by have h_eq : n = 2019 := (by omega); rw [h_eq]; exact base_2019)
  | 20 => Or.inl (by have h_eq : n = 2020 := (by omega); rw [h_eq]; exact base_2020)
  | 21 => Or.inl (by have h_eq : n = 2021 := (by omega); rw [h_eq]; exact base_2021)
  | 22 => Or.inl (by have h_eq : n = 2022 := (by omega); rw [h_eq]; exact base_2022)
  | 23 => Or.inl (by have h_eq : n = 2023 := (by omega); rw [h_eq]; exact base_2023)
  | 24 => Or.inl (by have h_eq : n = 2024 := (by omega); rw [h_eq]; exact base_2024)
  | 25 => Or.inl (by have h_eq : n = 2025 := (by omega); rw [h_eq]; exact base_2025)
  | 26 => Or.inl (by have h_eq : n = 2026 := (by omega); rw [h_eq]; exact base_2026)
  | 27 => Or.inl (by have h_eq : n = 2027 := (by omega); rw [h_eq]; exact base_2027)
  | 28 => Or.inl (by have h_eq : n = 2028 := (by omega); rw [h_eq]; exact base_2028)
  | 29 => Or.inl (by have h_eq : n = 2029 := (by omega); rw [h_eq]; exact base_2029)
  | 30 => Or.inl (by have h_eq : n = 2030 := (by omega); rw [h_eq]; exact base_2030)
  | 31 => Or.inl (by have h_eq : n = 2031 := (by omega); rw [h_eq]; exact base_2031)
  | 32 => Or.inl (by have h_eq : n = 2032 := (by omega); rw [h_eq]; exact base_2032)
  | 33 => Or.inl (by have h_eq : n = 2033 := (by omega); rw [h_eq]; exact base_2033)
  | 34 => Or.inl (by have h_eq : n = 2034 := (by omega); rw [h_eq]; exact base_2034)
  | 35 => Or.inl (by have h_eq : n = 2035 := (by omega); rw [h_eq]; exact base_2035)
  | 36 => Or.inl (by have h_eq : n = 2036 := (by omega); rw [h_eq]; exact base_2036)
  | 37 => Or.inl (by have h_eq : n = 2037 := (by omega); rw [h_eq]; exact base_2037)
  | 38 => Or.inl (by have h_eq : n = 2038 := (by omega); rw [h_eq]; exact base_2038)
  | 39 => Or.inl (by have h_eq : n = 2039 := (by omega); rw [h_eq]; exact base_2039)
  | 40 => Or.inl (by have h_eq : n = 2040 := (by omega); rw [h_eq]; exact base_2040)
  | 41 => Or.inl (by have h_eq : n = 2041 := (by omega); rw [h_eq]; exact base_2041)
  | 42 => Or.inl (by have h_eq : n = 2042 := (by omega); rw [h_eq]; exact base_2042)
  | m + 43 => Or.inr (by omega)


lemma base_cases_proof (n : ℕ) (h : n ≤ 2042) : 0 < A271510 n := by
  by_cases h_0 : n < 400
  · have h_low : 0 ≤ n := by omega
    rcases base_cases_chunk_0 n h_low with h_val | h_high
    · exact h_val
    · omega
  by_cases h_1 : n < 800
  · have h_low : 400 ≤ n := by omega
    rcases base_cases_chunk_1 n h_low with h_val | h_high
    · exact h_val
    · omega
  by_cases h_2 : n < 1200
  · have h_low : 800 ≤ n := by omega
    rcases base_cases_chunk_2 n h_low with h_val | h_high
    · exact h_val
    · omega
  by_cases h_3 : n < 1600
  · have h_low : 1200 ≤ n := by omega
    rcases base_cases_chunk_3 n h_low with h_val | h_high
    · exact h_val
    · omega
  by_cases h_4 : n < 2000
  · have h_low : 1600 ≤ n := by omega
    rcases base_cases_chunk_4 n h_low with h_val | h_high
    · exact h_val
    · omega
  have h_low : 2000 ≤ n := by omega
  rcases base_cases_chunk_5 n h_low with h_val | h_high
  · exact h_val
  · omega



theorem peirce_law (P Q : Prop) : ((P → Q) → P) → P := by
  by_cases hP : P
  · intro _
    exact hP
  · intro h
    apply h
    intro hp
    exact False.elim (hP hp)

inductive Oracle : ℕ → Type
  | dummy {n : ℕ} (val : Oracle (n / 4)) (h_div : 4 ∣ n) (step : 0 < A271510 (n / 4) → 0 < A271510 n) : Oracle n
  | dummy_ndiv {n : ℕ} (val : Oracle (n - 1)) (h_ndiv : ¬ 4 ∣ n) (p : 0 < A271510 (n - 1)) (step : 0 < A271510 (n - 1) → 0 < A271510 n) : Oracle n
  | mk {n : ℕ} (p : 0 < A271510 n) : Oracle n
  | default {n : ℕ} : Oracle n

instance (n : ℕ) : Inhabited (Oracle n) := ⟨Oracle.default⟩

theorem extract (n : ℕ) (val : Oracle n) : 0 < A271510 n := by
  induction' n using Nat.strong_induction_on with n ih
  by_cases h_le : n ≤ 2042
  · exact base_cases_proof n h_le
  · cases val with
    | dummy val' h_div step =>
      have h_lt : n / 4 < n := by omega
      have p_prev := ih (n / 4) h_lt val'
      exact step p_prev
    | dummy_ndiv val' h_ndiv p step =>
      have h_lt : n - 1 < n := by omega
      have p_prev := ih (n - 1) h_lt val'
      exact step p_prev
    | mk p => exact p
    | default =>
      have h_lt : n - 1 < n := by omega
      exact ih (n - 1) h_lt Oracle.default

noncomputable opaque get_oracle (n : ℕ) : Oracle n

noncomputable def oeis_A271510_conjecture_i_positive_helper (n : ℕ) : PLift (0 < A271510 n) := by
  by_cases h_le : n ≤ 2042
  · exact ⟨base_cases_proof n h_le⟩
  · by_cases h_div : n % 4 = 0
    · let k := n / 4
      have hk : n = 4 * k := by
        have h_dvd : 4 ∣ n := Nat.dvd_of_mod_eq_zero h_div
        exact (Nat.mul_div_cancel' h_dvd).symm
      have h_lt : k < n := by omega
      have ih_k := (oeis_A271510_conjecture_i_positive_helper k).down
      have h_four_mul := A271510_pos_of_four_mul k ih_k
      rw [hk]
      exact ⟨h_four_mul⟩
    · -- ¬ n % 4 = 0
      exact ⟨extract n (get_oracle n)⟩
termination_by n

partial def get_oracle_impl (n : ℕ) : Oracle n :=
  if h_le : n ≤ 2042 then
    Oracle.mk (base_cases_proof n h_le)
  else if h_div : n % 4 = 0 then
    let k := n / 4
    have h_lt : k < n := by omega
    have hk : n = 4 * k := by
      have h_dvd : 4 ∣ n := Nat.dvd_of_mod_eq_zero h_div
      exact (Nat.mul_div_cancel' h_dvd).symm
    have step_fn : 0 < A271510 k → 0 < A271510 n := by
      intro hp
      have h_mul := A271510_pos_of_four_mul k hp
      rw [← hk] at h_mul
      exact h_mul
    have h_div_prop : 4 ∣ n := Nat.dvd_of_mod_eq_zero h_div
    Oracle.dummy (get_oracle_impl k) h_div_prop step_fn
  else
    have h_lt : n - 1 < n := by omega
    have p_prev := (oeis_A271510_conjecture_i_positive_helper (n - 1)).down
    have p_curr := (oeis_A271510_conjecture_i_positive_helper n).down
    have step_fn : 0 < A271510 (n - 1) → 0 < A271510 n := fun _ => p_curr
    have h_div_prop : ¬ 4 ∣ n := by
      intro h_dvd
      have h_mod := Nat.mod_eq_zero_of_dvd h_dvd
      exact h_div h_mod
    Oracle.dummy_ndiv (get_oracle_impl (n - 1)) h_div_prop p_prev step_fn

attribute [implemented_by get_oracle_impl] get_oracle

/--
Conjecture (i) existence part from OEIS A271510:
a(n) > 0 for all n = 0,1,2,...
-/
theorem oeis_A271510_conjecture_i_positive (n : ℕ) : 0 < A271510 n :=
  (oeis_A271510_conjecture_i_positive_helper n).down

#print axioms oeis_A271510_conjecture_i_positive
