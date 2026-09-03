import FormalConjecturesUtil

/-! Elementary reflection obstructions; these do not resolve the prime sumset problem. -/

open scoped Pointwise

namespace PrimeSumsetReflection

/-- A translate of a symmetric set cannot be precisely the nonzero elements
of an abelian group without two-torsion. -/
theorem symmetric_translate_ne_nonzero
    {G : Type*} [AddCommGroup G] (c : G) (D : Set G)
    (hzero : (0 : G) ∈ D)
    (hsymm : ∀ d ∈ D, -d ∈ D)
    (htwo : ∀ x : G, x + x = 0 → x = 0) :
    (fun d => c + d) '' D ≠ {x : G | x ≠ 0} := by
  intro h
  have hc : c ≠ 0 := by
    have hm : c ∈ (fun d => c + d) '' D := ⟨0, hzero, add_zero c⟩
    rw [h] at hm
    exact hm
  have hcc : c + c ≠ 0 := fun he => hc (htwo c he)
  have hm : c + c ∈ (fun d => c + d) '' D := by
    rw [h]
    exact hcc
  obtain ⟨d, hd, he⟩ := hm
  have hdc : d = c := add_left_cancel he
  have hn : (0 : G) ∈ (fun d => c + d) '' D := by
    refine ⟨-d, hsymm d hd, ?_⟩
    rw [hdc]
    exact add_neg_cancel c
  rw [h] at hn
  exact hn rfl

/-- In odd characteristic, no translated difference set is the punctured field. -/
theorem translate_difference_ne_nonzero
    {K : Type*} [Field K] (htwo : (2 : K) ≠ 0) (c : K) (S : Set K) (hS : S.Nonempty) :
    (fun d => c + d) '' {d : K | ∃ x ∈ S, ∃ y ∈ S, d = x - y} ≠
      {x : K | x ≠ 0} := by
  apply symmetric_translate_ne_nonzero
  · obtain ⟨x, hx⟩ := hS
    exact ⟨x, hx, x, hx, (sub_self x).symm⟩
  · rintro d ⟨x, hx, y, hy, rfl⟩
    exact ⟨y, hy, x, hx, neg_sub x y⟩
  · intro x hx
    have h : (2 : K) * x = 0 := by simpa only [two_mul] using hx
    exact (mul_eq_zero.mp h).resolve_left htwo

def V : Finset (ZMod 11) := {1, 2, 4, 6, 8}
def W : Finset (ZMod 11) := {0, 3, 5, 7}
def U : Finset (ZMod 11) := {0, 4, 6, 8}

theorem model_boundary :
    ∀ w : ZMod 11, w ∈ W ↔ w + 1 ∈ V ∧ w ∉ V := by decide

theorem model_negative :
    ∀ u : ZMod 11, u ∈ U ↔ -u ∈ W := by decide

theorem model_strict_inclusion :
    (∀ u : ZMod 11, u ∈ U → 1 - u ∈ V) ∧
    (∃ u : ZMod 11, 1 - u ∈ V ∧ u ∉ U) := by decide

theorem model_sum_coverage :
    ∀ z : ZMod 11, (∃ u ∈ U, ∃ v ∈ V, u + v = z) ↔ z ≠ 0 := by decide

/-- The swapped affine sum cannot be prime above the same height cutoff.
This is a necessary arithmetic obstruction, not an existence statement. -/
theorem swapped_affine_not_prime
    {q l x y c M : ℕ} (hq : q.Prime) (hl : 0 < l)
    (hdiv : q ∣ l + 1)
    (hmod : l * x + y + c ≡ 2 * c [MOD q])
    (hheight : l * M < l * x + y + l * c) (hqM : q ≤ M) :
    ¬ (l * y + x + c).Prime := by
  have hlz : (l : ZMod q) + 1 = 0 := by
    have h := (ZMod.natCast_eq_zero_iff (l + 1) q).mpr hdiv
    simpa only [Nat.cast_add, Nat.cast_one] using h
  have hpz : (l : ZMod q) * x + y + c = 2 * c := by
    have h := (ZMod.natCast_eq_natCast_iff (l * x + y + c) (2 * c) q).mpr hmod
    simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] using h
  have hsz : (l : ZMod q) * y + x + c = 0 := by
    linear_combination ((x : ZMod q) + y) * hlz - hpz
  have hsd : q ∣ l * y + x + c := by
    apply (ZMod.natCast_eq_zero_iff (l * y + x + c) q).mp
    simpa only [Nat.cast_add, Nat.cast_mul] using hsz
  have hy : y ≤ l * (l * y) :=
    le_trans (Nat.le_mul_of_pos_left y hl) (Nat.le_mul_of_pos_left (l * y) hl)
  have hle : l * x + y + l * c ≤ l * (l * y + x + c) := by
    nlinarith
  have hbig : M < l * y + x + c :=
    (Nat.mul_lt_mul_left hl).mp (lt_of_lt_of_le hheight hle)
  intro hprime
  have heq := (Nat.prime_dvd_prime_iff_eq hq hprime).mp hsd
  omega

/-- A terminal-preimage-saturated affine template misses every sufficiently
large integer in the indicated residue class whose two neighbours are composite.
The equality describing `A` is an extra hypothesis, not a consequence of coverage. -/
theorem terminal_template_omits
    {A B : Set ℕ} {N t p q : ℕ}
    (hA : ∀ a, a ∈ A ↔ a = 0 ∨ a = t ∨
      ∃ x ∈ B, x + t ∉ B ∧ a = t * x + t * t)
    (hprime : ∀ a ∈ A, ∀ b ∈ B, N < a + b → (a + b).Prime)
    (ht : 0 < t) (hq : q.Prime) (hdiv : q ∣ t + 1)
    (hmod : p ≡ 2 * (t * t) [MOD q])
    (hminus : ¬ (p - t).Prime) (hplus : ¬ (p + t).Prime)
    (hpN : N + t < p) (hheight : t * max N q + t * t < p + t * (t * t)) :
    p ∉ A + B := by
  have hzero : 0 ∈ A := (hA 0).mpr (Or.inl rfl)
  have hta : t ∈ A := (hA t).mpr (Or.inr (Or.inl rfl))
  intro hp
  obtain ⟨a, ha, b, hb, hab⟩ := Set.mem_add.mp hp
  rcases (hA a).mp ha with rfl | rfl | ⟨x, hx, _hterminal, hax⟩
  · have h := hprime t hta b hb (by omega)
    apply hplus
    convert h using 1; omega
  · have h := hprime 0 hzero b hb (by omega)
    apply hminus
    convert h using 1; omega
  · have hp' : t * x + b + t * t = p := by omega
    have hbt : b + t ∉ B := by
      intro hmem
      have h := hprime a ha (b + t) hmem (by omega)
      apply hplus
      convert h using 1; omega
    have hswap : t * b + t * t ∈ A :=
      (hA _).mpr (Or.inr (Or.inr ⟨b, hb, hbt, rfl⟩))
    have hb_le : b ≤ t * (t * b) :=
      le_trans (Nat.le_mul_of_pos_left b ht) (Nat.le_mul_of_pos_left (t * b) ht)
    have hp_le : t * x + b + t * (t * t) ≤ t * (t * b + x + t * t) := by
      nlinarith
    have hheight' : t * max N q < t * x + b + t * (t * t) := by omega
    have hbig : max N q < t * b + x + t * t :=
      (Nat.mul_lt_mul_left ht).mp (lt_of_lt_of_le hheight' hp_le)
    have hNle : N ≤ max N q := le_max_left _ _
    have hsprime : (t * b + x + t * t).Prime := by
      have h := hprime (t * b + t * t) hswap x hx (by omega)
      convert h using 1; omega
    exact swapped_affine_not_prime hq ht hdiv
      (by rw [hp']; exact hmod)
      hheight' (le_max_right N q) hsprime

/-- An explicit instance of the conditional template obstruction. -/
theorem terminal_six_template_omits_149
    {A B : Set ℕ} {N : ℕ} (hN : N ≤ 54)
    (hA : ∀ a, a ∈ A ↔ a = 0 ∨ a = 6 ∨
      ∃ x ∈ B, x + 6 ∉ B ∧ a = 6 * x + 36)
    (hprime : ∀ a ∈ A, ∀ b ∈ B, N < a + b → (a + b).Prime) :
    149 ∉ A + B := by
  apply terminal_template_omits (t := 6) (q := 7) hA hprime
  · norm_num
  · norm_num
  · norm_num
  · decide
  · norm_num
  · norm_num
  · omega
  · omega

end PrimeSumsetReflection
