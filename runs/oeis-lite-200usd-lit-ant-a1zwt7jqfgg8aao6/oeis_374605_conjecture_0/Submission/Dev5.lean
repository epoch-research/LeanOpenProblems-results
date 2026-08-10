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

-- window product: ∏_{i ∈ range(p-1), i ≠ i₀} (↑(M - i)) = -(a+1)⁻¹ where a = ↑M
theorem window_prod (p M i₀ : ℕ) [hp : Fact p.Prime] (hp5 : 5 ≤ p)
    (hM : p - 2 ≤ M) (hi₀ : i₀ < p - 1) (hzero : (M : ZMod p) = (i₀ : ZMod p))
    (hane : (M : ZMod p) + 1 ≠ 0) :
    ∏ i ∈ (Finset.range (p-1)).erase i₀, ((M - i : ℕ) : ZMod p) = -((M : ZMod p) + 1)⁻¹ := by
  set a : ZMod p := (M : ZMod p) with ha
  -- rewrite terms as a - ↑i
  have hterm : ∀ i ∈ (Finset.range (p-1)).erase i₀, ((M - i : ℕ) : ZMod p) = a - (i : ZMod p) := by
    intro i hi
    rw [Finset.mem_erase, Finset.mem_range] at hi
    rw [Nat.cast_sub (by omega)]
  rw [Finset.prod_congr rfl hterm]
  -- φ injective
  have hinj : Set.InjOn (fun (i:ℕ) => a - (i:ZMod p)) (↑((Finset.range (p-1)).erase i₀) : Set ℕ) := by
    intro i hi j hj h
    rw [Finset.mem_coe, Finset.mem_erase, Finset.mem_range] at hi hj
    simp only at h
    have : (i : ZMod p) = (j : ZMod p) := by linear_combination -h
    have := (ZMod.natCast_eq_natCast_iff' i j p).mp this
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at this
    exact this
  rw [← Finset.prod_image (f := fun (x:ZMod p) => x) (g := fun (i:ℕ) => a - (i:ZMod p)) hinj]
  -- image = (univ.erase (a+1)).erase 0
  have e1 : ((p-1:ℕ):ZMod p) = -1 := by
    have h : ((p-1:ℕ):ZMod p) = (p:ZMod p) - 1 := by
      rw [Nat.cast_sub (by omega)]; simp
    rw [h, ZMod.natCast_self]; ring
  have himg : ((Finset.range (p-1)).erase i₀).image (fun (i:ℕ) => a - (i:ZMod p))
      = ((univ : Finset (ZMod p)).erase (a+1)).erase 0 := by
    ext y
    simp only [Finset.mem_image, Finset.mem_erase, Finset.mem_range, Finset.mem_univ, and_true]
    constructor
    · rintro ⟨i, ⟨hii₀, hilt⟩, rfl⟩

      refine ⟨?_, ?_⟩
      · -- a - ↑i ≠ 0
        intro h
        apply hii₀
        have hc : (i : ZMod p) = (i₀ : ZMod p) := by rw [← hzero]; linear_combination -h
        have := (ZMod.natCast_eq_natCast_iff' i i₀ p).mp hc
        rwa [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at this
      · -- a - ↑i ≠ a + 1
        intro h
        have hc : (i : ZMod p) = ((p-1:ℕ):ZMod p) := by rw [e1]; linear_combination -h
        have := (ZMod.natCast_eq_natCast_iff' i (p-1) p).mp hc
        rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at this
        omega
    · rintro ⟨hy0, hya1⟩
      have hv : ((a-y).val : ZMod p) = a - y := by rw [ZMod.natCast_val, ZMod.cast_id]
      refine ⟨(a - y).val, ⟨?_, ?_⟩, ?_⟩
      · -- (a-y).val ≠ i₀
        intro h
        apply hy0
        have h2 : (a - y) = a := by rw [← hv, h, ← hzero]
        linear_combination -h2
      · -- (a-y).val < p-1
        have hlt : (a-y).val < p := ZMod.val_lt _
        rcases Nat.lt_or_ge ((a-y).val) (p-1) with h | h
        · exact h
        · exfalso; apply hya1
          have hval : (a-y).val = p-1 := by omega
          rw [hval, e1] at hv
          linear_combination hv
      · -- a - ↑(a-y).val = y
        rw [hv]; ring
    
  rw [himg]
  -- ∏ over (erase (a+1)).erase 0 = -(a+1)⁻¹
  have hmem : (a+1) ∈ (univ : Finset (ZMod p)).erase 0 := by
    rw [Finset.mem_erase]; exact ⟨by rw [add_comm]; exact fun h => hane (by linear_combination h), Finset.mem_univ _⟩
  have := Finset.prod_erase_mul ((univ : Finset (ZMod p)).erase 0) (fun x => x) hmem
  rw [prod_erase_zero] at this
  -- this : (∏ x ∈ (erase 0).erase (a+1), x) * (a+1) = -1
  have hid : (∏ x ∈ ((univ : Finset (ZMod p)).erase 0).erase (a+1), x) = -((a+1)⁻¹) := by
    have hne : (a+1) ≠ 0 := hane
    field_simp at this ⊢
    linear_combination this
  rw [Finset.erase_right_comm] at hid
  rw [hid]
