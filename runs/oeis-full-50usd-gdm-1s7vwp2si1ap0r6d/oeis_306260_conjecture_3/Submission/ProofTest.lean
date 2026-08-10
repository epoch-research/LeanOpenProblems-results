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


lemma satisfies_residues_mod_eight_eq (A B C D : ℤ) :
    satisfies_residues (A % 8) (B % 8) (C % 8) (D % 8) = satisfies_residues A B C D := by
  unfold satisfies_residues
  have hA : (A % 8) % 8 = A % 8 := by omega
  have hB : (B % 8) % 8 = B % 8 := by omega
  have hC : (C % 8) % 8 = C % 8 := by omega
  have hD : (D % 8) % 8 = D % 8 := by omega
  rw [hA, hB, hC, hD]

lemma find_perm_none_iff_mod_eight (a b c d : ℤ) :
    find_perm a b c d = Option.none ↔ find_perm (a % 8) (b % 8) (c % 8) (d % 8) = Option.none := by
  constructor
  · intro h
    unfold find_perm at h
    unfold find_perm
    repeat (first | split at h | replace h := h.symm; split at h | cases h | cases h.symm)
    simp only [satisfies_residues_mod_eight_eq] at *
    simp [*]
  · intro h
    unfold find_perm at h
    unfold find_perm
    repeat (first | split at h | replace h := h.symm; split at h | cases h | cases h.symm)
    simp only [satisfies_residues_mod_eight_eq] at *
    simp [*]

lemma h1_a_mod_eight (a b c d : ℤ) :
    ((-a - b - c - d) / 2) % 8 = ((-(a % 16) - (b % 16) - (c % 16) - (d % 16)) / 2) % 8 := by omega

lemma h1_b_mod_eight (a b c d : ℤ) :
    ((-a - b + c + d) / 2) % 8 = ((-(a % 16) - (b % 16) + (c % 16) + (d % 16)) / 2) % 8 := by omega

lemma h1_c_mod_eight (a b c d : ℤ) :
    ((-a + b - c + d) / 2) % 8 = ((-(a % 16) + (b % 16) - (c % 16) + (d % 16)) / 2) % 8 := by omega


lemma mod_sixteen_sq_int (a : ℤ) : (a % 16)^2 % 16 = a^2 % 16 := by
  have h_eq : a = 16 * (a / 16) + a % 16 := by omega
  have h_ring : a^2 = 16 * (16 * (a / 16)^2 + 2 * (a / 16) * (a % 16)) + (a % 16)^2 := by
    nth_rw 1 [h_eq]
    ring
  rw [h_ring]
  omega

lemma h1_d_mod_eight (a b c d : ℤ) :
    ((-a + b + c - d) / 2) % 8 = ((-(a % 16) + (b % 16) + (c % 16) - (d % 16)) / 2) % 8 := by omega

lemma h2_a_mod_eight (a b c d : ℤ) :
    ((-a - b - c + d) / 2) % 8 = ((-(a % 16) - (b % 16) - (c % 16) + (d % 16)) / 2) % 8 := by omega

lemma h2_b_mod_eight (a b c d : ℤ) :
    ((-a - b + c - d) / 2) % 8 = ((-(a % 16) - (b % 16) + (c % 16) - (d % 16)) / 2) % 8 := by omega

lemma h2_c_mod_eight (a b c d : ℤ) :
    ((-a + b - c - d) / 2) % 8 = ((-(a % 16) + (b % 16) - (c % 16) - (d % 16)) / 2) % 8 := by omega

lemma h2_d_mod_eight (a b c d : ℤ) :
    ((-a + b + c + d) / 2) % 8 = ((-(a % 16) + (b % 16) + (c % 16) + (d % 16)) / 2) % 8 := by omega

def transform_tuple (a b c d : ℕ) : ℤ × ℤ × ℤ × ℤ :=
  let val_a : ℤ := a
  let val_b : ℤ := b
  let val_c : ℤ := c
  let val_d : ℤ := d

  match find_perm val_a val_b val_c val_d with
  | Option.some res => res
  | Option.none =>
    let x1_a := -val_a
    let x1_b := -val_b
    let x1_c := -val_c
    let x1_d := -val_d
    let h1_a := (x1_a + x1_b + x1_c + x1_d) / 2
    let h1_b := (x1_a + x1_b - x1_c - x1_d) / 2
    let h1_c := (x1_a - x1_b + x1_c - x1_d) / 2
    let h1_d := (x1_a - x1_b - x1_c + x1_d) / 2
    match find_perm h1_a h1_b h1_c h1_d with
    | Option.some res => res
    | Option.none =>
      let x2_a := -val_a
      let x2_b := -val_b
      let x2_c := -val_c
      let x2_d := val_d
      let h2_a := (x2_a + x2_b + x2_c + x2_d) / 2
      let h2_b := (x2_a + x2_b - x2_c - x2_d) / 2
      let h2_c := (x2_a - x2_b + x2_c - x2_d) / 2
      let h2_d := (x2_a - x2_b - x2_c + x2_d) / 2
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


lemma exists_residues_of_sum_squares_eq (a b c d : ℤ) (h_sum : (a^2 + b^2 + c^2 + d^2) % 16 = 14) :
    ∃ A B C D : ℤ, A^2 + B^2 + C^2 + D^2 = a^2 + b^2 + c^2 + d^2 ∧ satisfies_residues A B C D = true := by
  let ra_N := (a % 16).natAbs
  let rb_N := (b % 16).natAbs
  let rc_N := (c % 16).natAbs
  let rd_N := (d % 16).natAbs
  have ha : ra_N < 16 := by omega
  have hb : rb_N < 16 := by omega
  have hc : rc_N < 16 := by omega
  have hd : rd_N < 16 := by omega
  have h_ra_eq : (ra_N : ℤ) = a % 16 := by omega
  have h_rb_eq : (rb_N : ℤ) = b % 16 := by omega
  have h_rc_eq : (rc_N : ℤ) = c % 16 := by omega
  have h_rd_eq : (rd_N : ℤ) = d % 16 := by omega
  have h_sum_mod : (ra_N^2 + rb_N^2 + rc_N^2 + rd_N^2) % 16 = 14 := by
    have h1 := mod_sixteen_sq_int a
    have h2 := mod_sixteen_sq_int b
    have h3 := mod_sixteen_sq_int c
    have h4 := mod_sixteen_sq_int d
    have h_cast : ((ra_N^2 + rb_N^2 + rc_N^2 + rd_N^2 : ℕ) : ℤ) = (ra_N : ℤ)^2 + (rb_N : ℤ)^2 + (rc_N : ℤ)^2 + (rd_N : ℤ)^2 := by push_cast; rfl
    have h_eq : (ra_N : ℤ)^2 + (rb_N : ℤ)^2 + (rc_N : ℤ)^2 + (rd_N : ℤ)^2 = (a % 16)^2 + (b % 16)^2 + (c % 16)^2 + (d % 16)^2 := by
      rw [h_ra_eq, h_rb_eq, h_rc_eq, h_rd_eq]
    have h_goal : (((ra_N^2 + rb_N^2 + rc_N^2 + rd_N^2 : ℕ) : ℤ) % 16) = 14 := by
      rw [h_cast, h_eq]
      omega
    exact Int.ofNat_inj.mp h_goal

  have h_spec := check_all_valid_spec ra_N rb_N rc_N rd_N ha hb hc hd h_sum_mod
  generalize h_trans : transform_tuple ra_N rb_N rc_N rd_N = res at h_spec
  rcases res with ⟨A0, B0, C0, D0⟩
  rcases h_spec with ⟨h_sq0, h_res0⟩
  unfold transform_tuple at h_trans
  dsimp at h_trans
  split at h_trans
  · rename_i h_find0
    subst h_trans
    have h_not_none : find_perm ra_N rb_N rc_N rd_N ≠ Option.none := by
      rw [h_find0]; simp
    have h_ra_mod : (ra_N : ℤ) % 8 = a % 8 := by omega
    have h_rb_mod : (rb_N : ℤ) % 8 = b % 8 := by omega
    have h_rc_mod : (rc_N : ℤ) % 8 = c % 8 := by omega
    have h_rd_mod : (rd_N : ℤ) % 8 = d % 8 := by omega
    have h_find_not_none : find_perm a b c d ≠ Option.none := by
      intro h_none
      rw [find_perm_none_iff_mod_eight] at h_none
      have h_none_ra : find_perm (ra_N : ℤ) (rb_N : ℤ) (rc_N : ℤ) (rd_N : ℤ) = Option.none := by
        rw [find_perm_none_iff_mod_eight]
        rw [h_ra_mod, h_rb_mod, h_rc_mod, h_rd_mod]
        exact h_none
      contradiction
    have h_exists_res : ∃ res_Z, find_perm a b c d = some res_Z := by
      cases h_find_eq : find_perm a b c d
      · contradiction
      · exact ⟨_, rfl⟩
    rcases h_exists_res with ⟨res_Z, h_find_Z⟩
    have h_spec_Z := find_perm_spec a b c d res_Z h_find_Z
    exact ⟨res_Z.1, res_Z.2.1, res_Z.2.2.1, res_Z.2.2.2, h_spec_Z⟩
  · rename_i h_find0
    split at h_trans
    · rename_i h_find1
      subst h_trans
      let H1_a := (-a - b - c - d) / 2
      let H1_b := (-a - b + c + d) / 2
      let H1_c := (-a + b - c + d) / 2
      let H1_d := (-a + b + c - d) / 2
      have h_not_none : find_perm (((-ra_N - rb_N - rc_N - rd_N : ℤ) / 2)) (((-ra_N - rb_N + rc_N + rd_N : ℤ) / 2)) (((-ra_N + rb_N - rc_N + rd_N : ℤ) / 2)) (((-ra_N + rb_N + rc_N - rd_N : ℤ) / 2)) ≠ Option.none := by
        have h_eq_a : (-ra_N - rb_N - rc_N - rd_N : ℤ) = -ra_N + -rb_N + -rc_N + -rd_N := by ring
        have h_eq_b : (-ra_N - rb_N + rc_N + rd_N : ℤ) = -ra_N + -rb_N - -rc_N - -rd_N := by ring
        have h_eq_c : (-ra_N + rb_N - rc_N + rd_N : ℤ) = -ra_N - -rb_N + -rc_N - -rd_N := by ring
        have h_eq_d : (-ra_N + rb_N + rc_N - rd_N : ℤ) = -ra_N - -rb_N - -rc_N + -rd_N := by ring
        rw [h_eq_a, h_eq_b, h_eq_c, h_eq_d]
        rw [h_find1]
        simp
      have h_mod_a : ((-ra_N - rb_N - rc_N - rd_N : ℤ)/2) % 8 = H1_a % 8 := by
        have h_eq_a : ((-a - b - c - d)/2) % 8 = ((-(ra_N : ℤ) - rb_N - rc_N - rd_N)/2) % 8 := by
          rw [h_ra_eq, h_rb_eq, h_rc_eq, h_rd_eq]
          exact h1_a_mod_eight a b c d
        omega
      have h_mod_b : ((-ra_N - rb_N + rc_N + rd_N : ℤ)/2) % 8 = H1_b % 8 := by
        have h_eq_b : ((-a - b + c + d)/2) % 8 = ((-(ra_N : ℤ) - rb_N + rc_N + rd_N)/2) % 8 := by
          rw [h_ra_eq, h_rb_eq, h_rc_eq, h_rd_eq]
          exact h1_b_mod_eight a b c d
        omega
      have h_mod_c : ((-ra_N + rb_N - rc_N + rd_N : ℤ)/2) % 8 = H1_c % 8 := by
        have h_eq_c : ((-a + b - c + d)/2) % 8 = ((-(ra_N : ℤ) + rb_N - rc_N + rd_N)/2) % 8 := by
          rw [h_ra_eq, h_rb_eq, h_rc_eq, h_rd_eq]
          exact h1_c_mod_eight a b c d
        omega
      have h_mod_d : ((-ra_N + rb_N + rc_N - rd_N : ℤ)/2) % 8 = H1_d % 8 := by
        have h_eq_d : ((-a + b + c - d)/2) % 8 = ((-(ra_N : ℤ) + rb_N + rc_N - rd_N)/2) % 8 := by
          rw [h_ra_eq, h_rb_eq, h_rc_eq, h_rd_eq]
          exact h1_d_mod_eight a b c d
        omega
      have h_find_not_none : find_perm H1_a H1_b H1_c H1_d ≠ Option.none := by
        intro h_none
        rw [find_perm_none_iff_mod_eight] at h_none
        have h_none_ra : find_perm (((-ra_N - rb_N - rc_N - rd_N : ℤ)/2)) (((-ra_N - rb_N + rc_N + rd_N : ℤ)/2)) (((-ra_N + rb_N - rc_N + rd_N : ℤ)/2)) (((-ra_N + rb_N + rc_N - rd_N : ℤ)/2)) = Option.none := by
          rw [find_perm_none_iff_mod_eight]
          rw [h_mod_a, h_mod_b, h_mod_c, h_mod_d]
          exact h_none
        contradiction
      have h_exists_res : ∃ res_Z, find_perm H1_a H1_b H1_c H1_d = some res_Z := by
        cases h_find_eq : find_perm H1_a H1_b H1_c H1_d
        · contradiction
        · exact ⟨_, rfl⟩
      rcases h_exists_res with ⟨res_Z, h_find_Z⟩
      have h_spec_Z := find_perm_spec H1_a H1_b H1_c H1_d res_Z h_find_Z
      refine ⟨res_Z.1, res_Z.2.1, res_Z.2.2.1, res_Z.2.2.2, ?_⟩
      rcases h_spec_Z with ⟨h_sq_Z, h_res_Z⟩
      refine ⟨?_, h_res_Z⟩
      have h_even : (a^2 + b^2 + c^2 + d^2) % 2 = 0 := by omega
      have h_parity := parity_sum_sq a b c d h_even
      have h_div_a : 2 * H1_a = -a - b - c - d := by omega
      have h_div_b : 2 * H1_b = -a - b + c + d := by omega
      have h_div_c : 2 * H1_c = -a + b - c + d := by omega
      have h_div_d : 2 * H1_d = -a + b + c - d := by omega
      have h_four : 4 * (H1_a^2 + H1_b^2 + H1_c^2 + H1_d^2) = 4 * (a^2 + b^2 + c^2 + d^2) := by
        calc 4 * (H1_a^2 + H1_b^2 + H1_c^2 + H1_d^2)
          _ = (2 * H1_a)^2 + (2 * H1_b)^2 + (2 * H1_c)^2 + (2 * H1_d)^2 := by ring
          _ = (-a - b - c - d)^2 + (-a - b + c + d)^2 + (-a + b - c + d)^2 + (-a + b + c - d)^2 := by rw [h_div_a, h_div_b, h_div_c, h_div_d]
          _ = 4 * (a^2 + b^2 + c^2 + d^2) := by ring
      have h_four_div : H1_a^2 + H1_b^2 + H1_c^2 + H1_d^2 = a^2 + b^2 + c^2 + d^2 := by omega
      rw [h_sq_Z, h_four_div]
    · rename_i h_find1
      split at h_trans
      · rename_i h_find2
        subst h_trans
        let H2_a := (-a - b - c + d) / 2
        let H2_b := (-a - b + c - d) / 2
        let H2_c := (-a + b - c - d) / 2
        let H2_d := (-a + b + c + d) / 2
        have h_not_none : find_perm (((-ra_N - rb_N - rc_N + rd_N : ℤ) / 2)) (((-ra_N - rb_N + rc_N - rd_N : ℤ) / 2)) (((-ra_N + rb_N - rc_N - rd_N : ℤ) / 2)) (((-ra_N + rb_N + rc_N + rd_N : ℤ) / 2)) ≠ Option.none := by
          have h_eq_a : (-ra_N - rb_N - rc_N + rd_N : ℤ) = -ra_N + -rb_N + -rc_N + rd_N := by ring
          have h_eq_b : (-ra_N - rb_N + rc_N - rd_N : ℤ) = -ra_N + -rb_N - -rc_N - rd_N := by ring
          have h_eq_c : (-ra_N + rb_N - rc_N - rd_N : ℤ) = -ra_N - -rb_N + -rc_N - rd_N := by ring
          have h_eq_d : (-ra_N + rb_N + rc_N + rd_N : ℤ) = -ra_N - -rb_N - -rc_N + rd_N := by ring
          rw [h_eq_a, h_eq_b, h_eq_c, h_eq_d]
          rw [h_find2]
          simp
        have h_mod_a : ((-ra_N - rb_N - rc_N + rd_N : ℤ)/2) % 8 = H2_a % 8 := by
          have h_eq_a : ((-a - b - c + d)/2) % 8 = ((-(ra_N : ℤ) - rb_N - rc_N + rd_N)/2) % 8 := by
            rw [h_ra_eq, h_rb_eq, h_rc_eq, h_rd_eq]
            exact h2_a_mod_eight a b c d
          omega
        have h_mod_b : ((-ra_N - rb_N + rc_N - rd_N : ℤ)/2) % 8 = H2_b % 8 := by
          have h_eq_b : ((-a - b + c - d)/2) % 8 = ((-(ra_N : ℤ) - rb_N + rc_N - rd_N)/2) % 8 := by
            rw [h_ra_eq, h_rb_eq, h_rc_eq, h_rd_eq]
            exact h2_b_mod_eight a b c d
          omega
        have h_mod_c : ((-ra_N + rb_N - rc_N - rd_N : ℤ)/2) % 8 = H2_c % 8 := by
          have h_eq_c : ((-a + b - c - d)/2) % 8 = ((-(ra_N : ℤ) + rb_N - rc_N - rd_N)/2) % 8 := by
            rw [h_ra_eq, h_rb_eq, h_rc_eq, h_rd_eq]
            exact h2_c_mod_eight a b c d
          omega
        have h_mod_d : ((-ra_N + rb_N + rc_N + rd_N : ℤ)/2) % 8 = H2_d % 8 := by
          have h_eq_d : ((-a + b + c + d)/2) % 8 = ((-(ra_N : ℤ) + rb_N + rc_N + rd_N)/2) % 8 := by
            rw [h_ra_eq, h_rb_eq, h_rc_eq, h_rd_eq]
            exact h2_d_mod_eight a b c d
          omega
        have h_find_not_none : find_perm H2_a H2_b H2_c H2_d ≠ Option.none := by
          intro h_none
          rw [find_perm_none_iff_mod_eight] at h_none
          have h_none_ra : find_perm (((-ra_N - rb_N - rc_N + rd_N : ℤ)/2)) (((-ra_N - rb_N + rc_N - rd_N : ℤ)/2)) (((-ra_N + rb_N - rc_N - rd_N : ℤ)/2)) (((-ra_N + rb_N + rc_N + rd_N : ℤ)/2)) = Option.none := by
            rw [find_perm_none_iff_mod_eight]
            rw [h_mod_a, h_mod_b, h_mod_c, h_mod_d]
            exact h_none
          contradiction
        have h_exists_res : ∃ res_Z, find_perm H2_a H2_b H2_c H2_d = some res_Z := by
          cases h_find_eq : find_perm H2_a H2_b H2_c H2_d
          · contradiction
          · exact ⟨_, rfl⟩
        rcases h_exists_res with ⟨res_Z, h_find_Z⟩
        have h_spec_Z := find_perm_spec H2_a H2_b H2_c H2_d res_Z h_find_Z
        refine ⟨res_Z.1, res_Z.2.1, res_Z.2.2.1, res_Z.2.2.2, ?_⟩
        rcases h_spec_Z with ⟨h_sq_Z, h_res_Z⟩
        refine ⟨?_, h_res_Z⟩
        have h_even : (a^2 + b^2 + c^2 + d^2) % 2 = 0 := by omega
        have h_parity := parity_sum_sq a b c d h_even
        have h_div_a : 2 * H2_a = -a - b - c + d := by omega
        have h_div_b : 2 * H2_b = -a - b + c - d := by omega
        have h_div_c : 2 * H2_c = -a + b - c - d := by omega
        have h_div_d : 2 * H2_d = -a + b + c + d := by omega
        have h_four : 4 * (H2_a^2 + H2_b^2 + H2_c^2 + H2_d^2) = 4 * (a^2 + b^2 + c^2 + d^2) := by
          calc 4 * (H2_a^2 + H2_b^2 + H2_c^2 + H2_d^2)
            _ = (2 * H2_a)^2 + (2 * H2_b)^2 + (2 * H2_c)^2 + (2 * H2_d)^2 := by ring
            _ = (-a - b - c + d)^2 + (-a - b + c - d)^2 + (-a + b - c - d)^2 + (-a + b + c + d)^2 := by rw [h_div_a, h_div_b, h_div_c, h_div_d]
            _ = 4 * (a^2 + b^2 + c^2 + d^2) := by ring
        have h_four_div : H2_a^2 + H2_b^2 + H2_c^2 + H2_d^2 = a^2 + b^2 + c^2 + d^2 := by omega
        rw [h_sq_Z, h_four_div]
      · injection h_trans with hA h_rest
        injection h_rest with hB h_rest2
        injection h_rest2 with hC hD
        subst hA hB hC hD
        unfold satisfies_residues at h_res0
        contradiction

