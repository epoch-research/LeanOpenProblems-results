import FormalConjectures.Util.ProblemImports
open Finset

theorem prod_erase_zero (p : ℕ) [hp : Fact p.Prime] :
    ∏ x ∈ (univ : Finset (ZMod p)).erase 0, x = -1 := by
  have hp0 : 0 < p := hp.1.pos
  rw [← ZMod.prod_Ico_one_prime (p := p)]
  apply Finset.prod_nbij' (fun (x : ZMod p) => x.val) (fun (i : ℕ) => (i : ZMod p))
  · intro x hx
    rw [Finset.mem_erase] at hx
    rw [Finset.mem_Ico]
    refine ⟨?_, ZMod.val_lt x⟩
    rw [Nat.one_le_iff_ne_zero]
    intro h; exact hx.1 ((ZMod.val_eq_zero x).mp h)
  · intro i hi
    rw [Finset.mem_Ico] at hi
    rw [Finset.mem_erase]
    refine ⟨?_, Finset.mem_univ _⟩
    rw [Ne, ZMod.natCast_eq_zero_iff]
    intro h; have := Nat.le_of_dvd (by omega) h; omega
  · intro x hx; simp
  · intro i hi
    rw [Finset.mem_Ico] at hi
    rw [ZMod.val_natCast, Nat.mod_eq_of_lt hi.2]
  · intro x hx; rw [ZMod.natCast_val, ZMod.cast_id]

theorem resid_prod (p : ℕ) [hp : Fact p.Prime] (a : ZMod p) :
    ∏ x ∈ (univ : Finset (ZMod p)).erase a, (a - x) = -1 := by
  have hinj : ∀ x ∈ (univ : Finset (ZMod p)).erase a, ∀ y ∈ (univ : Finset (ZMod p)).erase a,
      (Equiv.subLeft a) x = (Equiv.subLeft a) y → x = y :=
    fun x _ y _ h => (Equiv.subLeft a).injective h
  have himg : ((univ : Finset (ZMod p)).erase a).image (Equiv.subLeft a) =
      (univ : Finset (ZMod p)).erase 0 := by
    ext y
    simp only [Finset.mem_image, Finset.mem_erase, Finset.mem_univ, and_true]
    constructor
    · rintro ⟨x, hx, rfl⟩
      simp only [Equiv.subLeft_apply]
      rw [sub_ne_zero]; exact fun h => hx h.symm
    · intro hy
      exact ⟨a - y, by rw [Ne, sub_eq_self]; exact hy, by simp⟩
  have key : ∏ y ∈ (univ : Finset (ZMod p)).erase 0, y
      = ∏ x ∈ (univ : Finset (ZMod p)).erase a, (a - x) := by
    rw [← himg, Finset.prod_image hinj]
    apply Finset.prod_congr rfl; intro x _; rw [Equiv.subLeft_apply]
  rw [← key, prod_erase_zero]
