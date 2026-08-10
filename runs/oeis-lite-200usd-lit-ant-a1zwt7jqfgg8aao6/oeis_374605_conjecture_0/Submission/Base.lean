import FormalConjectures.Util.ProblemImports
open Finset

noncomputable def T (n k : ℕ) : ℕ :=
  (Nat.choose n k) ^ 2 * (Nat.choose (n + k) k) * (Nat.choose (3 * n + 2 * k) n)

section ZModHelpers
open Finset
open Finset

-- ascFactorial first-factor split: n.ascFactorial (k+1) = n * (n+1).ascFactorial k
theorem asc_split (n k : ℕ) : n.ascFactorial (k+1) = n * (n+1).ascFactorial k := by
  induction k with
  | zero => simp [Nat.ascFactorial_succ, Nat.ascFactorial_zero]
  | succ k ih =>
    rw [Nat.ascFactorial_succ, ih, Nat.ascFactorial_succ]
    ring

theorem choose_mul_fact (p k : ℕ) (hk : 1 ≤ k) (hkp : k ≤ p) :
    (Nat.choose (p - 1 + k) k) * (Nat.factorial k) = p.ascFactorial k := by
  have hpk : k ≤ p - 1 + k := by omega
  have h1 := Nat.choose_mul_factorial_mul_factorial hpk
  have hsub : (p - 1 + k) - k = p - 1 := by omega
  rw [hsub] at h1
  have h2 : (Nat.factorial (p-1)) * p.ascFactorial k = (Nat.factorial (p-1+k)) := by
    have := Nat.factorial_mul_ascFactorial (p-1) k
    have hp1 : p - 1 + 1 = p := by omega
    rw [hp1] at this; exact this
  rw [← h2] at h1
  have hpos : 0 < (Nat.factorial (p-1)) := Nat.factorial_pos _
  have key : (Nat.factorial (p-1)) * ((p - 1 + k).choose k * k.factorial) = (Nat.factorial (p-1)) * p.ascFactorial k := by
    rw [← Nat.mul_assoc, Nat.mul_comm (Nat.factorial (p-1))] at *
    linarith [h1]
  exact Nat.eq_of_mul_eq_mul_left hpos key

-- p divides C(p-1+k,k) for 1 ≤ k ≤ p-1
theorem p_dvd_choose1 (p k : ℕ) [hp : Fact p.Prime] (hk : 1 ≤ k) (hkp : k ≤ p - 1) :
    p ∣ Nat.choose (p - 1 + k) k := by
  apply hp.1.dvd_choose (a := k) (b := p - 1 + k) <;> omega

-- (A_k : ZMod p) where A_k = C(p-1+k,k)/p satisfies A_k * k = 1
-- (p+1).ascFactorial m ≡ m! mod p
theorem asc_mod (p m : ℕ) : (((p+1).ascFactorial m : ℕ) : ZMod p) = (m.factorial : ZMod p) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Nat.ascFactorial_succ, Nat.factorial_succ]
    push_cast [ih]
    have hpz : (p : ZMod p) = 0 := ZMod.natCast_self p
    have hh : ((p : ZMod p) + 1 + (m:ZMod p)) = (m:ZMod p) + 1 := by rw [hpz]; ring
    rw [hh]

theorem Ak_mod (p k : ℕ) [hp : Fact p.Prime] (hk : 1 ≤ k) (hkp : k ≤ p - 1) :
    ((Nat.choose (p-1+k) k / p : ℕ) : ZMod p) * (k : ZMod p) = 1 := by
  have hcf := choose_mul_fact p k hk (by omega)
  have hsplit := asc_split p (k-1)
  have hk1 : k - 1 + 1 = k := by omega
  rw [hk1] at hsplit
  -- hcf: C*k! = p.asc k ; hsplit: p.asc k = p * (p+1).asc (k-1)
  rw [hsplit] at hcf
  -- hcf : C * k! = p * (p+1).asc (k-1)
  have hdvd := p_dvd_choose1 p k hk hkp
  obtain ⟨A, hA⟩ := hdvd   -- C = p * A
  rw [hA] at hcf
  -- p*A*k! = p*(p+1).asc(k-1)
  have hp0 : 0 < p := hp.1.pos
  have hAk : A * k.factorial = (p+1).ascFactorial (k-1) := by
    have : p * (A * k.factorial) = p * (p+1).ascFactorial (k-1) := by ring_nf; ring_nf at hcf; linarith [hcf]
    exact Nat.eq_of_mul_eq_mul_left hp0 this
  -- divide: A_k = C/p = A
  have hquot : Nat.choose (p-1+k) k / p = A := by rw [hA]; exact Nat.mul_div_cancel_left A hp0
  rw [hquot]
  -- (A:ZMod p) * k = 1
  -- from hAk cast: A * k! = (k-1)! mod p, and k! = k*(k-1)!
  have hcast : (A : ZMod p) * (k.factorial : ZMod p) = ((k-1).factorial : ZMod p) := by
    have hc : ((A * k.factorial : ℕ) : ZMod p) = (((p+1).ascFactorial (k-1) : ℕ) : ZMod p) := by
      rw [hAk]
    push_cast at hc
    rw [hc, asc_mod]
  have hfact : (k.factorial : ZMod p) = (k : ZMod p) * ((k-1).factorial : ZMod p) := by
    have : k.factorial = k * (k-1).factorial := by
      conv_lhs => rw [← hk1, Nat.factorial_succ, hk1]
    rw [this]; push_cast; ring
  have hunit : ((k-1).factorial : ZMod p) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]
    intro hd
    have := Nat.Prime.dvd_factorial hp.1 |>.mp hd
    omega
  rw [hfact] at hcast
  -- (A) * (k * (k-1)!) = (k-1)!  => (A*k)*(k-1)! = 1*(k-1)!
  have : ((A : ZMod p) * (k:ZMod p)) * ((k-1).factorial : ZMod p) = 1 * ((k-1).factorial : ZMod p) := by
    rw [one_mul]; linear_combination hcast
  exact mul_right_cancel₀ hunit this


-- General product expansion modulo e^3 = 0.
-- ∏ (1 + e * b i) = 1 + e * (∑ b) + e² * ((∑b)² - ∑ b²) * half,  where 2*half=1.
theorem prod_one_add_e {R : Type*} [CommRing R] (e : R) (he : e^3 = 0)
    (half : R) (hhalf : 2 * half = 1)
    (s : Finset ℕ) (b : ℕ → R) :
    ∏ i ∈ s, (1 + e * b i)
      = 1 + e * (∑ i ∈ s, b i)
          + e^2 * ((∑ i ∈ s, b i)^2 - (∑ i ∈ s, (b i)^2)) * half := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha, Finset.sum_insert ha, ih]
    linear_combination (-(e^2 * b a * (∑ i ∈ s, b i))) * hhalf
      + (b a * ((∑ i ∈ s, b i)^2 - (∑ i ∈ s, (b i)^2)) * half) * he

-- Sum of all elements of ZMod p is 0 (p odd prime)
theorem sum_zmod_eq_zero (p : ℕ) [hp : Fact p.Prime] (hp2 : 2 < p) :
    ∑ x : ZMod p, x = 0 := by
  have h2 : (2 : ZMod p) ≠ 0 := by
    have : ((2:ℕ) : ZMod p) ≠ 0 := by
      rw [Ne, ZMod.natCast_eq_zero_iff]; intro h
      have := Nat.le_of_dvd (by norm_num) h; omega
    simpa using this
  have hneg : ∑ x : ZMod p, x = ∑ x : ZMod p, (-x) :=
    (Equiv.sum_comp (Equiv.neg (ZMod p)) (fun x => x)).symm
  rw [Finset.sum_neg_distrib] at hneg
  have h2eq : (2 : ZMod p) * ∑ x : ZMod p, x = 0 := by linear_combination hneg
  exact (mul_eq_zero.mp h2eq).resolve_left h2

-- Sum of inverses of all elements is 0
theorem sum_inv_zmod_eq_zero (p : ℕ) [hp : Fact p.Prime] (hp2 : 2 < p) :
    ∑ x : ZMod p, x⁻¹ = 0 := by
  have : ∑ x : ZMod p, x⁻¹ = ∑ x : ZMod p, x :=
    Equiv.sum_comp (Equiv.mk (·⁻¹) (·⁻¹) inv_inv inv_inv) (fun x => x)
  rw [this]; exact sum_zmod_eq_zero p hp2


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
end ZModHelpers
