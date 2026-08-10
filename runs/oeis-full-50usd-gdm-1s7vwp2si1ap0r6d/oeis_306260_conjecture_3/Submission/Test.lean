import FormalConjectures.Util.ProblemImports

set_option maxHeartbeats 20000000
set_option maxRecDepth 100000

open Nat

def satisfies_residues (A B C D : ℤ) : Bool :=
  let r_a := A % 8
  let r_b := B % 8
  let r_c := C % 8
  let r_d := D % 8
  (r_a == 0) && (r_b == 1 || r_b == 7) && (r_c == 2 || r_c == 6) && (r_d == 3 || r_d == 5)

def find_perm (a b c d : ℤ) : Option (ℤ × ℤ × ℤ × ℤ) :=
  match satisfies_residues a b c d with
  | true => Option.some (a, b, c, d)
  | false => match satisfies_residues a b d c with
    | true => Option.some (a, b, d, c)
    | false => match satisfies_residues a c b d with
      | true => Option.some (a, c, b, d)
      | false => match satisfies_residues a c d b with
        | true => Option.some (a, c, d, b)
        | false => match satisfies_residues a d b c with
          | true => Option.some (a, d, b, c)
          | false => match satisfies_residues a d c b with
            | true => Option.some (a, d, c, b)
            | false => match satisfies_residues b a c d with
              | true => Option.some (b, a, c, d)
              | false => match satisfies_residues b a d c with
                | true => Option.some (b, a, d, c)
                | false => match satisfies_residues b c a d with
                  | true => Option.some (b, c, a, d)
                  | false => match satisfies_residues b c d a with
                    | true => Option.some (b, c, d, a)
                    | false => match satisfies_residues b d a c with
                      | true => Option.some (b, d, a, c)
                      | false => match satisfies_residues b d c a with
                        | true => Option.some (b, d, c, a)
                        | false => match satisfies_residues c a b d with
                          | true => Option.some (c, a, b, d)
                          | false => match satisfies_residues c a d b with
                            | true => Option.some (c, a, d, b)
                            | false => match satisfies_residues c b a d with
                              | true => Option.some (c, b, a, d)
                              | false => match satisfies_residues c b d a with
                                | true => Option.some (c, b, d, a)
                                | false => match satisfies_residues c d a b with
                                  | true => Option.some (c, d, a, b)
                                  | false => match satisfies_residues c d b a with
                                    | true => Option.some (c, d, b, a)
                                    | false => match satisfies_residues d a b c with
                                      | true => Option.some (d, a, b, c)
                                      | false => match satisfies_residues d a c b with
                                        | true => Option.some (d, a, c, b)
                                        | false => match satisfies_residues d b a c with
                                          | true => Option.some (d, b, a, c)
                                          | false => match satisfies_residues d b c a with
                                            | true => Option.some (d, b, c, a)
                                            | false => match satisfies_residues d c a b with
                                              | true => Option.some (d, c, a, b)
                                              | false => match satisfies_residues d c b a with
                                                | true => Option.some (d, c, b, a)
                                                | false => Option.none

lemma find_perm_spec (a b c d : ℤ) (res : ℤ × ℤ × ℤ × ℤ) (h : find_perm a b c d = Option.some res) :
    res.1^2 + res.2.1^2 + res.2.2.1^2 + res.2.2.2^2 = a^2 + b^2 + c^2 + d^2 ∧ satisfies_residues res.1 res.2.1 res.2.2.1 res.2.2.2 = true := by
  unfold find_perm at h
  repeat (
    first
    | injection h with h_eq; subst h_eq; refine ⟨by ring, by assumption⟩
    | split at h
    | replace h := h.symm; split at h
    | cases h
    | cases h.symm
  )




lemma sq_emod_two (a : ℤ) : a^2 % 2 = a % 2 := by
  have h : a % 2 = 0 ∨ a % 2 = 1 := by omega
  rcases h with h | h
  · have : a = 2 * (a / 2) := by omega
    nth_rw 1 [this]
    have h_ring : (2 * (a / 2))^2 = 2 * (2 * (a / 2)^2) := by ring
    rw [h_ring]
    omega
  · have : a = 2 * (a / 2) + 1 := by omega
    nth_rw 1 [this]
    have h_ring : (2 * (a / 2) + 1)^2 = 2 * (2 * (a / 2)^2 + 2 * (a / 2)) + 1 := by ring
    rw [h_ring]
    omega

lemma parity_sum_sq (a b c d : ℤ) (h : (a^2 + b^2 + c^2 + d^2) % 2 = 0) : (a + b + c + d) % 2 = 0 := by
  have h1 := sq_emod_two a
  have h2 := sq_emod_two b
  have h3 := sq_emod_two c
  have h4 := sq_emod_two d
  omega


lemma h1_even (a b c d : ℤ) (h_sum : (a^2 + b^2 + c^2 + d^2) % 16 = 14) :
    (-a - b - c - d) % 2 = 0 ∧
    (-a - b + c + d) % 2 = 0 ∧
    (-a + b - c + d) % 2 = 0 ∧
    (-a + b + c - d) % 2 = 0 := by
  have h_even : (a^2 + b^2 + c^2 + d^2) % 2 = 0 := by omega
  have h_parity := parity_sum_sq a b c d h_even
  omega


lemma h2_even (a b c d : ℤ) (h_sum : (a^2 + b^2 + c^2 + d^2) % 16 = 14) :
    (-a - b - c + d) % 2 = 0 ∧
    (-a - b + c - d) % 2 = 0 ∧
    (-a + b - c - d) % 2 = 0 ∧
    (-a + b + c + d) % 2 = 0 := by
  have h_even : (a^2 + b^2 + c^2 + d^2) % 2 = 0 := by omega
  have h_parity := parity_sum_sq a b c d h_even
  omega


lemma emod_sixteen_eight (x : ℤ) : (x % 16) % 8 = x % 8 := by omega

lemma satisfies_residues_mod_eq (A B C D : ℤ) :
    satisfies_residues (A % 16) (B % 16) (C % 16) (D % 16) = satisfies_residues A B C D := by
  unfold satisfies_residues
  simp

lemma find_perm_none_iff (a b c d : ℤ) :
    find_perm a b c d = Option.none ↔ find_perm (a % 16) (b % 16) (c % 16) (d % 16) = Option.none := by
  constructor
  · intro h
    unfold find_perm at h
    unfold find_perm
    repeat (first | split at h | replace h := h.symm; split at h | cases h | cases h.symm)
    simp only [satisfies_residues_mod_eq] at *
    simp [*]
  · intro h
    unfold find_perm at h
    unfold find_perm
    repeat (first | split at h | replace h := h.symm; split at h | cases h | cases h.symm)
    simp only [satisfies_residues_mod_eq] at *
    simp [*]


def transform_tuple (a b c d : ℕ) : ℤ × ℤ × ℤ × ℤ :=
  match find_perm (a : ℤ) (b : ℤ) (c : ℤ) (d : ℤ) with
  | Option.some res => res
  | Option.none =>
    let h1_a := (-(a : ℤ) - b - c - d) / 2
    let h1_b := (-(a : ℤ) - b + c + d) / 2
    let h1_c := (-(a : ℤ) + b - c + d) / 2
    let h1_d := (-(a : ℤ) + b + c - d) / 2
    match find_perm h1_a h1_b h1_c h1_d with
    | Option.some res => res
    | Option.none =>
      let h2_a := (-(a : ℤ) - b - c + d) / 2
      let h2_b := (-(a : ℤ) - b + c - d) / 2
      let h2_c := (-(a : ℤ) + b - c - d) / 2
      let h2_d := (-(a : ℤ) + b + c + d) / 2
      match find_perm h2_a h2_b h2_c h2_d with
      | Option.some res => res
      | Option.none => (0, 0, 0, 0)

def check_all_valid : Bool :=
  (List.range 16).all (fun a =>
    (List.range 16).all (fun b =>
      (List.range 16).all (fun c =>
        (List.range 16).all (fun d =>
          if (a^2 + b^2 + c^2 + d^2) % 16 == 14 then
            let ⟨A, B, C, D⟩ := transform_tuple a b c d
            (A^2 + B^2 + C^2 + D^2 == (a : ℤ)^2 + (b : ℤ)^2 + (c : ℤ)^2 + (d : ℤ)^2) &&
            satisfies_residues A B C D
          else
            true
        )
      )
    )
  )

theorem check_all_valid_eq_true : check_all_valid = true := by
  decide


lemma check_all_valid_spec (a b c d : ℕ) (ha : a < 16) (hb : b < 16) (hc : c < 16) (hd : d < 16)
    (h_sum : (a^2 + b^2 + c^2 + d^2) % 16 = 14) :
    let ⟨A, B, C, D⟩ := transform_tuple a b c d
    A^2 + B^2 + C^2 + D^2 = (a : ℤ)^2 + (b : ℤ)^2 + (c : ℤ)^2 + (d : ℤ)^2 ∧ satisfies_residues A B C D = true := by
  have h_all := check_all_valid_eq_true
  unfold check_all_valid at h_all
  rw [List.all_eq_true] at h_all
  have h_a := h_all a (by rw [List.mem_range]; exact ha)
  rw [List.all_eq_true] at h_a
  have h_b := h_a b (by rw [List.mem_range]; exact hb)
  rw [List.all_eq_true] at h_b
  have h_c := h_b c (by rw [List.mem_range]; exact hc)
  rw [List.all_eq_true] at h_c
  have h_d := h_c d (by rw [List.mem_range]; exact hd)
  have h_cond : ((a^2 + b^2 + c^2 + d^2) % 16 == 14) = true := by
    rw [beq_iff_eq]
    exact h_sum
  rw [h_cond] at h_d
  dsimp at h_d
  rw [Bool.and_eq_true] at h_d
  rcases h_d with ⟨h_sq, h_res⟩
  exact ⟨beq_iff_eq.mp h_sq, h_res⟩

lemma mod_sixteen_sq (a : ℕ) : (a % 16)^2 % 16 = a^2 % 16 := by
  have h_eq : (a : ℤ) = 16 * ((a : ℤ) / 16) + (a : ℤ) % 16 := by omega
  have h_ring : (16 * ((a:ℤ)/16) + (a:ℤ)%16)^2 = 16 * (16 * ((a:ℤ)/16)^2 + 2 * ((a:ℤ)/16) * ((a:ℤ)%16)) + ((a:ℤ)%16)^2 := by ring
  have h_cast : ((a^2 % 16 : ℕ) : ℤ) = (a^2 % 16 : ℤ) := by push_cast; rfl
  have h_cast2 : (((a % 16)^2 % 16 : ℕ) : ℤ) = ((a % 16)^2 % 16 : ℤ) := by push_cast; rfl
  rw [← Int.ofNat_inj]
  rw [h_cast, h_cast2]
  push_cast
  nth_rw 2 [h_eq]
  rw [h_ring]
  omega


lemma find_perm_eq_of_mod_eight_eq {a1 b1 c1 d1 a2 b2 c2 d2 : ℤ}
    (ha : a1 % 8 = a2 % 8) (hb : b1 % 8 = b2 % 8) (hc : c1 % 8 = c2 % 8) (hd : d1 % 8 = d2 % 8) :
    find_perm a1 b1 c1 d1 = find_perm a2 b2 c2 d2 := by
  unfold find_perm satisfies_residues
  rw [ha, hb, hc, hd]

lemma transform_tuple_spec (a b c d : ℕ) (h_sum : (a^2 + b^2 + c^2 + d^2) % 16 = 14) :
    let ⟨A, B, C, D⟩ := transform_tuple a b c d
    A^2 + B^2 + C^2 + D^2 = (a : ℤ)^2 + (b : ℤ)^2 + (c : ℤ)^2 + (d : ℤ)^2 ∧ satisfies_residues A B C D = true := by
  generalize h_trans : transform_tuple a b c d = res
  rcases res with ⟨A, B, C, D⟩
  unfold transform_tuple at h_trans
  dsimp at h_trans
  split at h_trans
  · rename_i h_find
    subst h_trans
    have h_spec := find_perm_spec a b c d _ h_find
    rcases h_spec with ⟨h_sq, h_res⟩
    exact ⟨h_sq, h_res⟩
  · rename_i h_find
    split at h_trans
    · rename_i h_find2
      subst h_trans
      have h_spec := find_perm_spec _ _ _ _ _ h_find2
      rcases h_spec with ⟨h_sq, h_res⟩
      refine ⟨?_, h_res⟩
      let va : ℤ := a
      let vb : ℤ := b
      let vc : ℤ := c
      let vd : ℤ := d
      have h_sum_int : ((va^2 + vb^2 + vc^2 + vd^2) % 16) = 14 := by
        have h_cast : (((a^2 + b^2 + c^2 + d^2) % 16 : ℕ) : ℤ) = (14 : ℤ) := by rw [h_sum]; rfl
        push_cast at h_cast
        exact h_cast
      have h_even := h1_even va vb vc vd h_sum_int
      have h_div_a : 2 * (( -va - vb - vc - vd ) / 2) = -va - vb - vc - vd := by omega
      have h_div_b : 2 * (( -va - vb + vc + vd ) / 2) = -va - vb + vc + vd := by omega
      have h_div_c : 2 * (( -va + vb - vc + vd ) / 2) = -va + vb - vc + vd := by omega
      have h_div_d : 2 * (( -va + vb + vc - vd ) / 2) = -va + vb + vc - vd := by omega
      have h_four : 4 * (((-va - vb - vc - vd)/2)^2 + ((-va - vb + vc + vd)/2)^2 + ((-va + vb - vc + vd)/2)^2 + ((-va + vb + vc - vd)/2)^2) = 4 * (va^2 + vb^2 + vc^2 + vd^2) := by
        calc 4 * (((-va - vb - vc - vd)/2)^2 + ((-va - vb + vc + vd)/2)^2 + ((-va + vb - vc + vd)/2)^2 + ((-va + vb + vc - vd)/2)^2)
          _ = (2 * ((-va - vb - vc - vd)/2))^2 + (2 * ((-va - vb + vc + vd)/2))^2 + (2 * ((-va + vb - vc + vd)/2))^2 + (2 * ((-va + vb + vc - vd)/2))^2 := by ring
          _ = (-va - vb - vc - vd)^2 + (-va - vb + vc + vd)^2 + (-va + vb - vc + vd)^2 + (-va + vb + vc - vd)^2 := by rw [h_div_a, h_div_b, h_div_c, h_div_d]
          _ = 4 * (va^2 + vb^2 + vc^2 + vd^2) := by ring
      have h_four_div : (((-va - vb - vc - vd)/2)^2 + ((-va - vb + vc + vd)/2)^2 + ((-va + vb - vc + vd)/2)^2 + ((-va + vb + vc - vd)/2)^2) = va^2 + vb^2 + vc^2 + vd^2 := by
        omega
      have h_sq_subst : A^2 + B^2 + C^2 + D^2 = (((-va - vb - vc - vd)/2)^2 + ((-va - vb + vc + vd)/2)^2 + ((-va + vb - vc + vd)/2)^2 + ((-va + vb + vc - vd)/2)^2) := by
        exact h_sq
      rw [h_sq_subst, h_four_div]
    · rename_i h_find2
      split at h_trans
      · rename_i h_find3
        subst h_trans
        have h_spec := find_perm_spec _ _ _ _ _ h_find3
        rcases h_spec with ⟨h_sq, h_res⟩
        refine ⟨?_, h_res⟩
        let va : ℤ := a
        let vb : ℤ := b
        let vc : ℤ := c
        let vd : ℤ := d
        have h_sum_int : ((va^2 + vb^2 + vc^2 + vd^2) % 16) = 14 := by
          have h_cast : (((a^2 + b^2 + c^2 + d^2) % 16 : ℕ) : ℤ) = (14 : ℤ) := by rw [h_sum]; rfl
          push_cast at h_cast
          exact h_cast
        have h_even := h2_even va vb vc vd h_sum_int
        have h_div_a : 2 * (( -va - vb - vc + vd ) / 2) = -va - vb - vc + vd := by omega
        have h_div_b : 2 * (( -va - vb + vc - vd ) / 2) = -va - vb + vc - vd := by omega
        have h_div_c : 2 * (( -va + vb - vc - vd ) / 2) = -va + vb - vc - vd := by omega
        have h_div_d : 2 * (( -va + vb + vc + vd ) / 2) = -va + vb + vc + vd := by omega
        have h_four : 4 * (((-va - vb - vc + vd)/2)^2 + ((-va - vb + vc - vd)/2)^2 + ((-va + vb - vc - vd)/2)^2 + ((-va + vb + vc + vd)/2)^2) = 4 * (va^2 + vb^2 + vc^2 + vd^2) := by
          calc 4 * (((-va - vb - vc + vd)/2)^2 + ((-va - vb + vc - vd)/2)^2 + ((-va + vb - vc - vd)/2)^2 + ((-va + vb + vc + vd)/2)^2)
            _ = (2 * ((-va - vb - vc + vd)/2))^2 + (2 * ((-va - vb + vc - vd)/2))^2 + (2 * ((-va + vb - vc - vd)/2))^2 + (2 * ((-va + vb + vc + vd)/2))^2 := by ring
            _ = (-va - vb - vc + vd)^2 + (-va - vb + vc - vd)^2 + (-va + vb - vc - vd)^2 + (-va + vb + vc + vd)^2 := by rw [h_div_a, h_div_b, h_div_c, h_div_d]
            _ = 4 * (va^2 + vb^2 + vc^2 + vd^2) := by ring
        have h_four_div : (((-va - vb - vc + vd)/2)^2 + ((-va - vb + vc - vd)/2)^2 + ((-va + vb - vc - vd)/2)^2 + ((-va + vb + vc + vd)/2)^2) = va^2 + vb^2 + vc^2 + vd^2 := by
          omega
        have h_sq_subst : A^2 + B^2 + C^2 + D^2 = (((-va - vb - vc + vd)/2)^2 + ((-va - vb + vc - vd)/2)^2 + ((-va + vb - vc - vd)/2)^2 + ((-va + vb + vc + vd)/2)^2) := by
          exact h_sq
        rw [h_sq_subst, h_four_div]
      · rename_i h_find3
        have h_fp1 : find_perm (a % 16 : ℤ) (b % 16) (c % 16) (d % 16) = Option.none := by
          rw [← find_perm_none_iff]; exact h_find
        have h_fp2 : find_perm (((-((a % 16 : ℕ) : ℤ) - (b % 16 : ℕ) - (c % 16 : ℕ) - (d % 16 : ℕ))/2)) (((-((a % 16 : ℕ) : ℤ) - (b % 16 : ℕ) + (c % 16 : ℕ) + (d % 16 : ℕ))/2)) (((-((a % 16 : ℕ) : ℤ) + (b % 16 : ℕ) - (c % 16 : ℕ) + (d % 16 : ℕ))/2)) (((-((a % 16 : ℕ) : ℤ) + (b % 16 : ℕ) + (c % 16 : ℕ) - (d % 16 : ℕ))/2)) = Option.none := by
          have h_cast_a : ((a % 16 : ℕ) : ℤ) = (a : ℤ) % 16 := by push_cast; rfl
          have h_cast_b : ((b % 16 : ℕ) : ℤ) = (b : ℤ) % 16 := by push_cast; rfl
          have h_cast_c : ((c % 16 : ℕ) : ℤ) = (c : ℤ) % 16 := by push_cast; rfl
          have h_cast_d : ((d % 16 : ℕ) : ℤ) = (d : ℤ) % 16 := by push_cast; rfl
          have h_eq1 : (((-((a % 16 : ℕ) : ℤ) - (b % 16 : ℕ) - (c % 16 : ℕ) - (d % 16 : ℕ))/2) % 16) = (((-(a : ℤ) - b - c - d)/2) % 16) := by
            rw [h_cast_a, h_cast_b, h_cast_c, h_cast_d]
            omega
          have h_eq2 : (((-((a % 16 : ℕ) : ℤ) - (b % 16 : ℕ) + (c % 16 : ℕ) + (d % 16 : ℕ))/2) % 16) = (((-(a : ℤ) - b + c + d)/2) % 16) := by
            rw [h_cast_a, h_cast_b, h_cast_c, h_cast_d]
            omega
          have h_eq3 : (((-((a % 16 : ℕ) : ℤ) + (b % 16 : ℕ) - (c % 16 : ℕ) + (d % 16 : ℕ))/2) % 16) = (((-(a : ℤ) + b - c + d)/2) % 16) := by
            rw [h_cast_a, h_cast_b, h_cast_c, h_cast_d]
            omega
          have h_eq4 : (((-((a % 16 : ℕ) : ℤ) + (b % 16 : ℕ) + (c % 16 : ℕ) - (d % 16 : ℕ))/2) % 16) = (((-(a : ℤ) + b + c - d)/2) % 16) := by
            rw [h_cast_a, h_cast_b, h_cast_c, h_cast_d]
            omega
          have h_fp2_mod : find_perm (((-((a % 16 : ℕ) : ℤ) - (b % 16 : ℕ) - (c % 16 : ℕ) - (d % 16 : ℕ))/2 % 16)) (((-((a % 16 : ℕ) : ℤ) - (b % 16 : ℕ) + (c % 16 : ℕ) + (d % 16 : ℕ))/2 % 16)) (((-((a % 16 : ℕ) : ℤ) + (b % 16 : ℕ) - (c % 16 : ℕ) + (d % 16 : ℕ))/2 % 16)) (((-((a % 16 : ℕ) : ℤ) + (b % 16 : ℕ) + (c % 16 : ℕ) - (d % 16 : ℕ))/2 % 16)) = Option.none := by
            rw [h_eq1, h_eq2, h_eq3, h_eq4]
            rw [← find_perm_none_iff]
            exact h_find2
          rw [find_perm_none_iff]
          exact h_fp2_mod
        have h_fp3 : find_perm (((-((a % 16 : ℕ) : ℤ) - (b % 16 : ℕ) - (c % 16 : ℕ) + (d % 16 : ℕ))/2)) (((-((a % 16 : ℕ) : ℤ) - (b % 16 : ℕ) + (c % 16 : ℕ) - (d % 16 : ℕ))/2)) (((-((a % 16 : ℕ) : ℤ) + (b % 16 : ℕ) - (c % 16 : ℕ) - (d % 16 : ℕ))/2)) (((-((a % 16 : ℕ) : ℤ) + (b % 16 : ℕ) + (c % 16 : ℕ) + (d % 16 : ℕ))/2)) = Option.none := by
          have h_cast_a : ((a % 16 : ℕ) : ℤ) = (a : ℤ) % 16 := by push_cast; rfl
          have h_cast_b : ((b % 16 : ℕ) : ℤ) = (b : ℤ) % 16 := by push_cast; rfl
          have h_cast_c : ((c % 16 : ℕ) : ℤ) = (c : ℤ) % 16 := by push_cast; rfl
          have h_cast_d : ((d % 16 : ℕ) : ℤ) = (d : ℤ) % 16 := by push_cast; rfl
          have h_eq1 : (((-((a % 16 : ℕ) : ℤ) - (b % 16 : ℕ) - (c % 16 : ℕ) + (d % 16 : ℕ))/2) % 16) = (((-(a : ℤ) - b - c + d)/2) % 16) := by
            rw [h_cast_a, h_cast_b, h_cast_c, h_cast_d]
            omega
          have h_eq2 : (((-((a % 16 : ℕ) : ℤ) - (b % 16 : ℕ) + (c % 16 : ℕ) - (d % 16 : ℕ))/2) % 16) = (((-(a : ℤ) - b + c - d)/2) % 16) := by
            rw [h_cast_a, h_cast_b, h_cast_c, h_cast_d]
            omega
          have h_eq3 : (((-((a % 16 : ℕ) : ℤ) + (b % 16 : ℕ) - (c % 16 : ℕ) - (d % 16 : ℕ))/2) % 16) = (((-(a : ℤ) + b - c - d)/2) % 16) := by
            rw [h_cast_a, h_cast_b, h_cast_c, h_cast_d]
            omega
          have h_eq4 : (((-((a % 16 : ℕ) : ℤ) + (b % 16 : ℕ) + (c % 16 : ℕ) + (d % 16 : ℕ))/2) % 16) = (((-(a : ℤ) + b + c + d)/2) % 16) := by
            rw [h_cast_a, h_cast_b, h_cast_c, h_cast_d]
            omega
          have h_fp3_mod : find_perm (((-((a % 16 : ℕ) : ℤ) - (b % 16 : ℕ) - (c % 16 : ℕ) + (d % 16 : ℕ))/2 % 16)) (((-((a % 16 : ℕ) : ℤ) - (b % 16 : ℕ) + (c % 16 : ℕ) - (d % 16 : ℕ))/2 % 16)) (((-((a % 16 : ℕ) : ℤ) + (b % 16 : ℕ) - (c % 16 : ℕ) - (d % 16 : ℕ))/2 % 16)) (((-((a % 16 : ℕ) : ℤ) + (b % 16 : ℕ) + (c % 16 : ℕ) + (d % 16 : ℕ))/2 % 16)) = Option.none := by
            rw [h_eq1, h_eq2, h_eq3, h_eq4]
            rw [← find_perm_none_iff]
            exact h_find3
          rw [find_perm_none_iff]
          exact h_fp3_mod
        have ha : a % 16 < 16 := Nat.mod_lt _ (by decide)
        have hb : b % 16 < 16 := Nat.mod_lt _ (by decide)
        have hc : c % 16 < 16 := Nat.mod_lt _ (by decide)
        have hd : d % 16 < 16 := Nat.mod_lt _ (by decide)
        have h_sum_mod : ((a % 16)^2 + (b % 16)^2 + (c % 16)^2 + (d % 16)^2) % 16 = 14 := by
          have h_m1 := mod_sixteen_sq a
          have h_m2 := mod_sixteen_sq b
          have h_m3 := mod_sixteen_sq c
          have h_m4 := mod_sixteen_sq d
          omega
        have h_spec := check_all_valid_spec (a % 16) (b % 16) (c % 16) (d % 16) ha hb hc hd h_sum_mod
        unfold transform_tuple at h_spec
        split at h_spec
        · rename_i h_find_spec
          rw [h_fp1] at h_find_spec
          contradiction
        · split at h_spec
          · rename_i h_find_spec2
            rw [h_fp2] at h_find_spec2
            contradiction
          · split at h_spec
            · rename_i h_find_spec3
              rw [h_fp3] at h_find_spec3
              contradiction
            · rcases h_spec with ⟨_, h_res⟩
              unfold satisfies_residues at h_res
              contradiction
