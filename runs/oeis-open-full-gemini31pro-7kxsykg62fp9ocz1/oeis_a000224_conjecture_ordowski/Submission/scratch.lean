import FormalConjectures.Util.ProblemImports
open Finset

/--
A000224: Number of squares $\bmod n$.
This is the cardinality of the set $\{k^2 \bmod n \mid k \in \{0, 1, \dots, n-1\}\}$.
-/
noncomputable def A000224 (n : ℕ) : ℕ :=
  if n = 0 then 1
  else
    Finset.card ((Finset.range n).image (fun k : ℕ => k ^ 2 % n))

lemma card_image_sq {F : Type*} [Field F] [Fintype F] [DecidableEq F] (hF : ringChar F ≠ 2) :
  (Finset.univ.image (fun x : F => x ^ 2)).card = (Fintype.card F + 1) / 2 := by
  let S := Finset.univ.image (fun x : F => x ^ 2)
  have eq1 : ∑ a : F, ({x : F | x ^ 2 = a}.toFinset.card : ℤ) = Fintype.card F := by
    have H (a : F) : ({x : F | x ^ 2 = a}.toFinset.card : ℤ) = (quadraticChar F) a + 1 := by
      exact_mod_cast quadraticChar_card_sqrts hF a
    have : ∑ a : F, ({x : F | x ^ 2 = a}.toFinset.card : ℤ) = ∑ a : F, ((quadraticChar F) a + 1) := by
      apply sum_congr rfl
      intro x _
      exact H x
    rw [this, sum_add_distrib]
    have H2 : ∑ a : F, (quadraticChar F) a = 0 := quadraticChar_sum_zero hF
    rw [H2, zero_add, sum_const, card_univ]
    simp
  have eq2 : ∑ a : F, ({x : F | x ^ 2 = a}.toFinset.card : ℤ) = ∑ a ∈ S, ({x : F | x ^ 2 = a}.toFinset.card : ℤ) := by
    symm
    apply sum_subset
    · intro a _
      exact mem_univ a
    · intro a _ ha
      have h_empty : {x : F | x ^ 2 = a}.toFinset = ∅ := by
        ext x
        simp only [Set.mem_toFinset, Set.mem_setOf_eq]
        constructor
        · intro hx
          apply False.elim
          apply ha
          simp only [S, mem_image, mem_univ, true_and]
          exact ⟨x, hx⟩
        · intro hx
          revert hx
          simp
      rw [h_empty, card_empty, Nat.cast_zero]
  have h_zero_in_S : (0 : F) ∈ S := by
    simp only [S, mem_image, mem_univ, true_and]
    exact ⟨0, zero_pow (by decide)⟩
  have eq3 : ∑ a ∈ S, ({x : F | x ^ 2 = a}.toFinset.card : ℤ) = 1 + 2 * ((S.card : ℤ) - 1) := by
    have h_split : S = insert 0 (S \ {0}) := by
      ext x
      simp only [mem_insert, mem_sdiff, mem_singleton]
      constructor
      · intro h
        by_cases h0 : x = 0
        · exact Or.inl h0
        · exact Or.inr ⟨h, h0⟩
      · rintro (rfl | ⟨h1, h2⟩)
        · exact h_zero_in_S
        · exact h1
    have h_insert_sum : ∑ a ∈ S, ({x : F | x ^ 2 = a}.toFinset.card : ℤ) = ({x : F | x ^ 2 = 0}.toFinset.card : ℤ) + ∑ a ∈ S \ {0}, ({x : F | x ^ 2 = a}.toFinset.card : ℤ) := by
      calc ∑ a ∈ S, ({x : F | x ^ 2 = a}.toFinset.card : ℤ) = ∑ a ∈ insert 0 (S \ {0}), ({x : F | x ^ 2 = a}.toFinset.card : ℤ) := by congr
        _ = ({x : F | x ^ 2 = 0}.toFinset.card : ℤ) + ∑ a ∈ S \ {0}, ({x : F | x ^ 2 = a}.toFinset.card : ℤ) := by
          have h_not_mem : (0 : F) ∉ S \ {0} := by simp only [mem_sdiff, mem_singleton, not_true, and_false, not_false_iff]
          exact Finset.sum_insert h_not_mem
    rw [h_insert_sum]
    have h_zero : ({x : F | x ^ 2 = 0}.toFinset.card : ℤ) = 1 := by
      have : {x : F | x ^ 2 = 0}.toFinset = {0} := by
        ext x
        simp only [Set.mem_toFinset, Set.mem_setOf_eq, mem_singleton]
        exact sq_eq_zero_iff
      rw [this, card_singleton]
      rfl
    rw [h_zero]
    have h_other : ∀ a ∈ S \ {0}, ({x : F | x ^ 2 = a}.toFinset.card : ℤ) = 2 := by
      intro a ha
      simp only [mem_sdiff, mem_singleton] at ha
      obtain ⟨h_in, h_neq⟩ := ha
      simp only [S, mem_image, mem_univ, true_and] at h_in
      obtain ⟨x, rfl⟩ := h_in
      have hx0 : x ≠ 0 := by
        intro hx0
        rw [hx0, zero_pow (by decide)] at h_neq
        exact h_neq rfl
      have H_sol : {y : F | y ^ 2 = x ^ 2}.toFinset = {x, -x} := by
        ext y
        simp only [Set.mem_toFinset, Set.mem_setOf_eq, mem_insert, mem_singleton]
        exact sq_eq_sq_iff_eq_or_eq_neg
      rw [H_sol]
      have h_neq_neg : x ≠ -x := by
        intro h_eq
        have H : x + x = 0 := by
          calc x + x = x + -x := by nth_rw 2 [h_eq]
            _ = 0 := add_neg_cancel x
        have h_char_2 : (2 : F) * x = 0 := by
          calc (2 : F) * x = (1 : F) * x + (1 : F) * x := by ring
            _ = x + x := by ring
            _ = 0 := H
        have H2 : (2 : F) = 0 := by
          cases mul_eq_zero.mp h_char_2 with
          | inl h2 => exact h2
          | inr hx => exact (hx0 hx).elim
        have hdvd : ringChar F ∣ 2 := ringChar.dvd H2
        have h_div := (Nat.dvd_prime Nat.prime_two).mp hdvd
        cases h_div with
        | inl h1 =>
          have := CharP.char_ne_one F (ringChar F)
          contradiction
        | inr h2 =>
          exact hF h2
      have h_card_insert : ({x, -x} : Finset F).card = 2 := by
        rw [card_pair h_neq_neg]
      rw [h_card_insert]
      rfl
    have h_sum_other : ∑ a ∈ S \ {0}, ({x : F | x ^ 2 = a}.toFinset.card : ℤ) = 2 * ((S.card : ℤ) - 1) := by
      rw [sum_congr rfl h_other, sum_const, nsmul_eq_mul]
      have h_card_sdiff : (S \ {0}).card = S.card - 1 := by
        have H1 : ({0} : Finset F) ⊆ S := by
          intro x hx
          simp only [mem_singleton] at hx
          rw [hx]
          exact h_zero_in_S
        rw [card_sdiff_of_subset H1, card_singleton]
      have H_card_sdiff2 : ((S \ {0}).card : ℤ) = (S.card : ℤ) - 1 := by
        rw [h_card_sdiff]
        have hS_pos : 1 ≤ S.card := by
          apply card_pos.mpr
          exact ⟨0, h_zero_in_S⟩
        exact Int.ofNat_sub hS_pos
      rw [H_card_sdiff2]
      ring
    rw [h_sum_other]
  rw [eq2, eq3] at eq1
  have eq4 : 2 * (S.card : ℤ) = (Fintype.card F : ℤ) + 1 := by
    calc 2 * (S.card : ℤ) = 1 + 2 * ((S.card : ℤ) - 1) + 1 := by ring
      _ = (Fintype.card F : ℤ) + 1 := by rw [eq1]
  have eq5 : (S.card : ℤ) = ((Fintype.card F + 1) / 2 : ℤ) := by
    calc (S.card : ℤ) = 2 * (S.card : ℤ) / 2 := by rw [mul_comm, Int.mul_ediv_cancel _ (by decide)]
      _ = ((Fintype.card F : ℤ) + 1) / 2 := by rw [eq4]
      _ = ((Fintype.card F + 1) / 2 : ℤ) := by rfl
  exact_mod_cast eq5

lemma card_image_ZMod (n : ℕ) [NeZero n] :
  ((Finset.range n).image (fun k : ℕ => k ^ 2 % n)).card =
  (Finset.univ.image (fun x : ZMod n => x ^ 2)).card := by
  let f : ℕ → ℕ := fun k => k ^ 2 % n
  let g : ZMod n → ZMod n := fun x => x ^ 2
  have h_univ : (Finset.univ.image g).card = ((Finset.range n).image (fun k : ℕ => g (k : ZMod n))).card := by
    have H : Finset.univ = (Finset.range n).image (fun k : ℕ => (k : ZMod n)) := by
      ext x
      simp only [mem_univ, mem_image, mem_range, true_iff]
      exact ⟨x.val, ZMod.val_lt x, ZMod.natCast_zmod_val x⟩
    rw [H, image_image]
    congr
  rw [h_univ]
  have h_map : ∀ k, (f k : ZMod n) = g (k : ZMod n) := by
    intro k
    change ((k ^ 2 % n : ℕ) : ZMod n) = (k : ZMod n) ^ 2
    rw [ZMod.natCast_mod]
    push_cast
    rfl
  have H : ((Finset.range n).image f).card = (((Finset.range n).image f).image (fun x : ℕ => (x : ZMod n))).card := by
    symm
    apply card_image_of_injOn
    intro x hx y hy
    simp only [coe_image, Set.mem_image, mem_coe, mem_range] at hx hy
    obtain ⟨kx, _, rfl⟩ := hx
    obtain ⟨ky, _, rfl⟩ := hy
    intro heq
    change (f kx : ZMod n) = (f ky : ZMod n) at heq
    have hfx : f kx < n := Nat.mod_lt _ (NeZero.pos n)
    have hfy : f ky < n := Nat.mod_lt _ (NeZero.pos n)
    have heqx : (f kx : ZMod n).val = f kx := ZMod.val_cast_of_lt hfx
    have heqy : (f ky : ZMod n).val = f ky := ZMod.val_cast_of_lt hfy
    rw [← heqx, ← heqy, heq]
  rw [H, image_image]
  have heq_fun : (fun x : ℕ => ((f x : ℕ) : ZMod n)) = (fun k : ℕ => g (k : ZMod n)) := by
    ext k
    exact h_map k
  have h_comp : (fun x : ℕ => (x : ZMod n)) ∘ f = (fun k : ℕ => g (k : ZMod n)) := by
    ext k
    exact h_map k
  rw [h_comp]

lemma p_prime_A000224 (p : ℕ) (hp : p.Prime) (hodd : p ≠ 2) :
  A000224 p = (p + 1) / 2 := by
  haveI : NeZero p := ⟨hp.ne_zero⟩
  haveI : Fact p.Prime := ⟨hp⟩
  unfold A000224
  rw [if_neg hp.ne_zero, card_image_ZMod]
  have h_char : ringChar (ZMod p) ≠ 2 := by
    rw [ringChar.eq (ZMod p) p]
    exact hodd
  have H := card_image_sq h_char
  have h_card : Fintype.card (ZMod p) = p := ZMod.card p
  rw [h_card] at H
  exact H

lemma A000224_prime_A000224 (p : ℕ) (hp : p.Prime) (hodd : p ≠ 2) :
  A000224 p * (A000224 p - 1) = (p + 1) / 2 * ((p - 1) / 2) := by
  rw [p_prime_A000224 p hp hodd]
  have h1 : (p + 1) / 2 - 1 = (p - 1) / 2 := by
    obtain ⟨k, rfl⟩ := hp.odd_of_ne_two hodd
    have h1 : (2 * k + 1 + 1) / 2 = k + 1 := by omega
    have h2 : (2 * k + 1 - 1) / 2 = k := by omega
    rw [h1, h2]
    omega
  rw [h1]

/--
Conjecture: n^2 == 1 (mod a(n)*(a(n)-1)) if and only if n is an odd prime.
-/
theorem oeis_a000224_conjecture_ordowski {n : ℕ} (h_n : 1 < n) :
    (n.Prime ∧ n ≠ 2) ↔ (n * n) ≡ 1 [MOD A000224 n * (A000224 n - 1)] := by
  sorry

theorem oeis_a000224_conjecture_ordowski.disproof : ¬ (type_of% @oeis_a000224_conjecture_ordowski) := sorry
