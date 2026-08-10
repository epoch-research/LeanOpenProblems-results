import FormalConjectures.Util.ProblemImports
open Finset

noncomputable def T (n k : ℕ) : ℕ :=
  (Nat.choose n k) ^ 2 * (Nat.choose (n + k) k) * (Nat.choose (3 * n + 2 * k) n)

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
theorem zmod_sum_range (p:ℕ)[NeZero p](f : ZMod p → ZMod p) :
    ∑ m ∈ Finset.range p, f (m:ZMod p) = ∑ x : ZMod p, f x := by
  apply Finset.sum_nbij' (i := fun (m:ℕ) => (m : ZMod p)) (j := fun (x:ZMod p) => x.val)
  · intro a ha; exact Finset.mem_univ _
  · intro a ha; rw [Finset.mem_range]; exact ZMod.val_lt a
  · intro a ha; rw [Finset.mem_range] at ha; exact ZMod.val_cast_of_lt ha
  · intro a ha; rw [ZMod.natCast_val, ZMod.cast_id]
  · intro a ha; rfl

lemma reduce_p2' (p : ℕ) (hp : 1 ≤ p) (x y : ZMod (p^3))
    (h : (ZMod.castHom (show p ∣ p^3 by exact ⟨p^2, by ring⟩) (ZMod p)) x
       = (ZMod.castHom (show p ∣ p^3 by exact ⟨p^2, by ring⟩) (ZMod p)) y) :
    (p:ZMod (p^3))^2 * x = (p:ZMod (p^3))^2 * y := by
  haveI : NeZero (p^3) := ⟨by positivity⟩
  -- reduce h to val congruence
  have hx : (ZMod.castHom (show p ∣ p^3 by exact ⟨p^2, by ring⟩) (ZMod p)) x = (x.val : ZMod p) := by
    conv_lhs => rw [← ZMod.natCast_zmod_val x]
    rw [map_natCast]
  have hy : (ZMod.castHom (show p ∣ p^3 by exact ⟨p^2, by ring⟩) (ZMod p)) y = (y.val : ZMod p) := by
    conv_lhs => rw [← ZMod.natCast_zmod_val y]
    rw [map_natCast]
  rw [hx, hy] at h
  -- now (x.val:ZMod p) = (y.val:ZMod p), so p | x.val - y.val (in ℤ)
  have hpd : (p:ℤ) ∣ ((x.val:ℤ) - (y.val:ℤ)) := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]; push_cast; rw [h]; ring
  obtain ⟨d, hd⟩ := hpd
  have e1 : x - y = (((p:ℤ) * d : ℤ) : ZMod (p^3)) := by
    rw [← hd, Int.cast_sub, Int.cast_natCast, Int.cast_natCast,
        ZMod.natCast_zmod_val, ZMod.natCast_zmod_val]
  have e2 : (p:ZMod (p^3))^2 * (x - y) = 0 := by
    rw [e1]
    have : (p:ZMod (p^3))^2 * (((p:ℤ) * d : ℤ) : ZMod (p^3))
         = (((p:ℕ)^3 : ℕ):ZMod (p^3)) * (d : ZMod (p^3)) := by push_cast; ring
    rw [this, ZMod.natCast_self, zero_mul]
  linear_combination e2

theorem choose_mul_fact_asc (a b : ℕ) :
    (Nat.choose (a+b) b) * b.factorial = (a+1).ascFactorial b := by
  have h1 := Nat.choose_mul_factorial_mul_factorial (Nat.le_add_left b a)
  rw [Nat.add_sub_cancel] at h1
  have h2 := Nat.factorial_mul_ascFactorial a b
  have hpos : 0 < a.factorial := Nat.factorial_pos _
  apply Nat.eq_of_mul_eq_mul_right hpos
  rw [h1, mul_comm ((a+1).ascFactorial b) a.factorial, h2]

-- C(p-1,k) ≡ (-1)^k mod p
theorem C_pm1_mod (p k:ℕ)[hp:Fact p.Prime](hk:k ≤ p-1) :
    ((Nat.choose (p-1) k : ℕ):ZMod p) = (-1)^k := by
  have hp0 := hp.1.pos
  have hkfu : IsUnit ((k.factorial:ℕ):ZMod p) := by
    rw [ZMod.isUnit_iff_coprime]
    refine (hp.1.coprime_iff_not_dvd.mpr ?_).symm
    intro hd; have := (Nat.Prime.dvd_factorial hp.1).mp hd; omega
  have hd : (p-1).descFactorial k = k.factorial * (p-1).choose k :=
    Nat.descFactorial_eq_factorial_mul_choose _ _
  have hprodneg : (∏ i ∈ Finset.range k, ((p-1-i:ℕ):ZMod p)) = (-1)^k * ((k.factorial:ℕ):ZMod p) := by
    rw [show (∏ i ∈ Finset.range k, ((p-1-i:ℕ):ZMod p)) = ∏ i ∈ Finset.range k, ((-1)*(↑(i+1):ZMod p)) from ?_]
    · rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range,
          show (∏ i ∈ Finset.range k, ((i+1:ℕ):ZMod p)) = ((k.factorial:ℕ):ZMod p) from by
            rw [← Finset.prod_range_add_one_eq_factorial, Nat.cast_prod]]
    · apply Finset.prod_congr rfl
      intro i hi
      rw [Finset.mem_range] at hi
      have hsum : (p-1-i) + (i+1) = p := by omega
      have h2 : ((p-1-i:ℕ):ZMod p) + ((i+1:ℕ):ZMod p) = 0 := by
        rw [← Nat.cast_add, hsum, ZMod.natCast_self]
      linear_combination h2
  have hfin : ((k.factorial:ℕ):ZMod p) * ((Nat.choose (p-1) k:ℕ):ZMod p)
            = ((k.factorial:ℕ):ZMod p) * ((-1)^k) := by
    have h1 : (((p-1).descFactorial k : ℕ):ZMod p) = ((k.factorial:ℕ):ZMod p) * ((Nat.choose (p-1) k:ℕ):ZMod p) := by
      rw [hd]; push_cast; ring
    rw [← h1, Nat.descFactorial_eq_prod_range, Nat.cast_prod, hprodneg]; ring
  exact hkfu.mul_right_injective hfin

set_option maxHeartbeats 1000000 in
theorem Bk_mod (p k:ℕ)[hp:Fact p.Prime](hp5:5≤p)(hk2:2≤k)(hkp:k≤p-1) :
    ((Nat.choose (3*p-3+2*k) (p-1) / p : ℕ):ZMod p) * (2*((k:ZMod p)-1))
      = (((3*p-3+2*k)/p : ℕ):ZMod p) := by
  set M := 3*p-3+2*k with hM
  set i₀ := M % p with hi₀def
  set c := M / p with hcdef
  have hp0 := hp.1.pos
  -- basic facts about i₀, c
  have hMval : ((M:ℕ):ZMod p) = 2*(k:ZMod p)-3 := by
    have hpz : ((p:ℕ):ZMod p) = 0 := ZMod.natCast_self p
    have h1 : M + 3 = 3*p + 2*k := by rw [hM]; omega
    have h2 : ((M:ℕ):ZMod p) + 3 = ((3*p+2*k:ℕ):ZMod p) := by
      rw [show (3:ZMod p) = ((3:ℕ):ZMod p) by push_cast; ring, ← Nat.cast_add, h1]
    have h3 : ((3*p+2*k:ℕ):ZMod p) = 2*(k:ZMod p) := by push_cast [hpz]; ring
    linear_combination h2 + h3
  -- i₀ ≠ p-1 : else 2k ≡ 2
  have hi₀ne : i₀ ≠ p - 1 := by
    intro hcontra
    have : ((i₀:ℕ):ZMod p) = ((p-1:ℕ):ZMod p) := by rw [hcontra]
    rw [hi₀def, ZMod.natCast_mod] at this
    have hp1c : ((p-1:ℕ):ZMod p) = -1 := by
      have : ((p-1:ℕ):ZMod p) + 1 = 0 := by
        rw [show ((p-1:ℕ):ZMod p) + 1 = (((p-1)+1:ℕ):ZMod p) by push_cast; ring, show (p-1)+1 = p by omega, ZMod.natCast_self]
      linear_combination this
    rw [hMval, hp1c] at this
    have h2u : (2:ZMod p) ≠ 0 := by
      have : ((2:ℕ):ZMod p) ≠ 0 := by rw [Ne, ZMod.natCast_eq_zero_iff]; intro h; have := Nat.le_of_dvd (by norm_num) h; omega
      simpa using this
    have hk1 : (k:ZMod p) = 1 := by
      have h0 : (2:ZMod p)*((k:ZMod p)-1) = 0 := by linear_combination this
      rcases mul_eq_zero.mp h0 with h|h
      · exact absurd h h2u
      · linear_combination h
    have : ((k:ℕ):ZMod p) = ((1:ℕ):ZMod p) := by push_cast; exact hk1
    have := (ZMod.natCast_eq_natCast_iff' k 1 p).mp this
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at this
    omega
  have hi₀lt : i₀ < p - 1 := by
    have : i₀ < p := Nat.mod_lt _ hp0
    omega
  have hci : M - i₀ = c * p := by
    have hdm : p * c + i₀ = M := by rw [hcdef, hi₀def]; exact Nat.div_add_mod M p
    rw [Nat.mul_comm]; omega
  have hMi : ((M:ℕ):ZMod p) = ((i₀:ℕ):ZMod p) := by rw [hi₀def, ZMod.natCast_mod]
  -- C * (p-1)! = descFactorial = prod
  have hCfact : (Nat.choose M (p-1)) * (p-1).factorial = ∏ i ∈ Finset.range (p-1), (M - i) := by
    rw [← Nat.descFactorial_eq_prod_range, Nat.descFactorial_eq_factorial_mul_choose, Nat.mul_comm]
  have hi₀mem : i₀ ∈ Finset.range (p-1) := Finset.mem_range.mpr hi₀lt
  have hpull : ∏ i ∈ Finset.range (p-1), (M - i) = (M - i₀) * ∏ i ∈ (Finset.range (p-1)).erase i₀, (M - i) := by
    rw [← Finset.mul_prod_erase _ _ hi₀mem]
  rw [hpull, hci] at hCfact
  have hdvdC : p ∣ Nat.choose M (p-1) := by
    have hpdvd : p ∣ (Nat.choose M (p-1)) * (p-1).factorial := by
      rw [hCfact]; exact ⟨c * ∏ i ∈ (Finset.range (p-1)).erase i₀, (M - i), by ring⟩
    rcases (Nat.Prime.dvd_mul hp.1).mp hpdvd with h | h
    · exact h
    · exfalso; have := (Nat.Prime.dvd_factorial hp.1).mp h; omega
  obtain ⟨B, hB⟩ := hdvdC
  rw [hB] at hCfact
  have hBfact : B * (p-1).factorial = c * ∏ i ∈ (Finset.range (p-1)).erase i₀, (M - i) := by
    have hh : p * (B * (p-1).factorial) = p * (c * ∏ i ∈ (Finset.range (p-1)).erase i₀, (M - i)) := by
      rw [← Nat.mul_assoc, hCfact]; ring
    exact Nat.eq_of_mul_eq_mul_left hp0 hh
  have hBeq : Nat.choose M (p-1) / p = B := by rw [hB]; exact Nat.mul_div_cancel_left B hp0
  rw [hBeq]
  have hcast : (B:ZMod p) * (((p-1).factorial:ℕ):ZMod p)
             = (c:ZMod p) * (∏ i ∈ (Finset.range (p-1)).erase i₀, ((M - i:ℕ):ZMod p)) := by
    have h := congrArg (Nat.cast (R := ZMod p)) hBfact
    rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_prod] at h
    exact h
  rw [ZMod.wilsons_lemma p] at hcast
  have hM2 : p - 2 ≤ M := by rw [hM]; omega
  have hane : ((M:ℕ):ZMod p) + 1 ≠ 0 := by
    rw [hMval]
    intro hcontra
    have h2u : (2:ZMod p) ≠ 0 := by
      have : ((2:ℕ):ZMod p) ≠ 0 := by rw [Ne, ZMod.natCast_eq_zero_iff]; intro h; have := Nat.le_of_dvd (by norm_num) h; omega
      simpa using this
    have hk1 : (k:ZMod p) = 1 := by
      have h0 : (2:ZMod p)*((k:ZMod p)-1) = 0 := by linear_combination hcontra
      rcases mul_eq_zero.mp h0 with h|h
      · exact absurd h h2u
      · linear_combination h
    have : ((k:ℕ):ZMod p) = ((1:ℕ):ZMod p) := by push_cast; exact hk1
    have := (ZMod.natCast_eq_natCast_iff' k 1 p).mp this
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at this
    omega
  have hwin := window_prod p M i₀ hp5 hM2 hi₀lt hMi hane
  rw [hwin] at hcast
  have hMp1 : ((M:ℕ):ZMod p) + 1 = 2*((k:ZMod p)-1) := by rw [hMval]; ring
  rw [hMp1] at hcast
  have hu : (2*((k:ZMod p)-1)) * (2*((k:ZMod p)-1))⁻¹ = 1 := by
    apply mul_inv_cancel₀; rw [← hMp1]; exact hane
  have hBval : (B:ZMod p) = (c:ZMod p)*(2*((k:ZMod p)-1))⁻¹ := by linear_combination -hcast
  rw [hBval]
  linear_combination (c:ZMod p)*hu

theorem M_cast (p k:ℕ)[hp:Fact p.Prime](hp5:5≤p) :
    ((3*p-3+2*k:ℕ):ZMod p) = 2*(k:ZMod p)-3 := by
  have hpz : ((p:ℕ):ZMod p) = 0 := ZMod.natCast_self p
  have h1 : (3*p-3+2*k) + 3 = 3*p + 2*k := by omega
  have h2 : ((3*p-3+2*k:ℕ):ZMod p) + 3 = ((3*p+2*k:ℕ):ZMod p) := by
    rw [show (3:ZMod p) = ((3:ℕ):ZMod p) by push_cast; ring, ← Nat.cast_add, h1]
  have h3 : ((3*p+2*k:ℕ):ZMod p) = 2*(k:ZMod p) := by push_cast [hpz]; ring
  linear_combination h2 + h3

theorem M_mod_lt (p k:ℕ)[hp:Fact p.Prime](hp5:5≤p)(hk2:2≤k)(hkp:k≤p-1) :
    (3*p-3+2*k) % p < p - 1 := by
  have hp0 := hp.1.pos
  have hlt : (3*p-3+2*k) % p < p := Nat.mod_lt _ hp0
  rcases Nat.lt_or_ge ((3*p-3+2*k) % p) (p-1) with h|h
  · exact h
  · exfalso
    have hval : (3*p-3+2*k) % p = p - 1 := by omega
    have hc : (((3*p-3+2*k) % p : ℕ):ZMod p) = ((p-1:ℕ):ZMod p) := by rw [hval]
    rw [ZMod.natCast_mod, M_cast p k hp5] at hc
    have hp1c : ((p-1:ℕ):ZMod p) = -1 := by
      have : ((p-1:ℕ):ZMod p) + 1 = 0 := by
        rw [show ((p-1:ℕ):ZMod p) + 1 = (((p-1)+1:ℕ):ZMod p) by push_cast; ring, show (p-1)+1 = p by omega, ZMod.natCast_self]
      linear_combination this
    rw [hp1c] at hc
    have h2u : (2:ZMod p) ≠ 0 := by
      have : ((2:ℕ):ZMod p) ≠ 0 := by rw [Ne, ZMod.natCast_eq_zero_iff]; intro h; have := Nat.le_of_dvd (by norm_num) h; omega
      simpa using this
    have hk1 : (k:ZMod p) = 1 := by
      have h0 : (2:ZMod p)*((k:ZMod p)-1) = 0 := by linear_combination hc
      rcases mul_eq_zero.mp h0 with h|h
      · exact absurd h h2u
      · linear_combination h
    have : ((k:ℕ):ZMod p) = ((1:ℕ):ZMod p) := by push_cast; exact hk1
    have := (ZMod.natCast_eq_natCast_iff' k 1 p).mp this
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at this
    omega

theorem p_dvd_choose2 (p k:ℕ)[hp:Fact p.Prime](hp5:5≤p)(hk2:2≤k)(hkp:k≤p-1) :
    p ∣ Nat.choose (3*p-3+2*k) (p-1) := by
  set M := 3*p-3+2*k with hM
  have hp0 := hp.1.pos
  have hi₀lt : M % p < p - 1 := M_mod_lt p k hp5 hk2 hkp
  have hCfact : (Nat.choose M (p-1)) * (p-1).factorial = ∏ i ∈ Finset.range (p-1), (M - i) := by
    rw [← Nat.descFactorial_eq_prod_range, Nat.descFactorial_eq_factorial_mul_choose, Nat.mul_comm]
  have hi₀mem : M % p ∈ Finset.range (p-1) := Finset.mem_range.mpr hi₀lt
  have hfac : p ∣ (M - M % p) := ⟨M / p, by have := Nat.div_add_mod M p; omega⟩
  have hdvd : p ∣ ∏ i ∈ Finset.range (p-1), (M - i) :=
    dvd_trans hfac (Finset.dvd_prod_of_mem _ hi₀mem)
  rw [← hCfact] at hdvd
  rcases (Nat.Prime.dvd_mul hp.1).mp hdvd with h | h
  · exact h
  · exfalso; have := (Nat.Prime.dvd_factorial hp.1).mp h; omega

set_option maxHeartbeats 1000000 in
theorem Mk_val (p k:ℕ)[hp:Fact p.Prime](hp5:5≤p)(hk2:2≤k)(hkp:k≤p-1) :
    (((Nat.choose (p-1) k)^2 * (Nat.choose ((p-1)+k) k / p) * (Nat.choose (3*p-3+2*k) (p-1) / p) : ℕ):ZMod p)
      = (((3*p-3+2*k)/p : ℕ):ZMod p) * (2:ZMod p)⁻¹ * (((k-1:ℕ):ZMod p)⁻¹ - ((k:ℕ):ZMod p)⁻¹) := by
  have hkne : ((k:ℕ):ZMod p) ≠ 0 := by rw [Ne, ZMod.natCast_eq_zero_iff]; intro h; have := Nat.le_of_dvd (by omega) h; omega
  have hk1ne : ((k-1:ℕ):ZMod p) ≠ 0 := by rw [Ne, ZMod.natCast_eq_zero_iff]; intro h; have := Nat.le_of_dvd (by omega) h; omega
  have h2ne : (2:ZMod p) ≠ 0 := by
    have : ((2:ℕ):ZMod p) ≠ 0 := by rw [Ne, ZMod.natCast_eq_zero_iff]; intro h; have := Nat.le_of_dvd (by norm_num) h; omega
    simpa using this
  have hk1cast : ((k-1:ℕ):ZMod p) = (k:ZMod p) - 1 := by
    rw [Nat.cast_sub (by omega)]; push_cast; ring
  have hcp := C_pm1_mod p k hkp
  have hak := Ak_mod p k (by omega) hkp
  have hbk := Bk_mod p k hp5 hk2 hkp
  -- expand casts
  rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_pow, hcp]
  -- ((-1)^k)^2 = 1
  have hcc2 : ((-1:ZMod p)^k)^2 = 1 := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
  rw [hcc2, one_mul]
  -- now: A_k * B_k = ...
  -- A_k = k⁻¹, B_k = c*(2(k-1))⁻¹
  have hAA : ((Nat.choose ((p-1)+k) k / p:ℕ):ZMod p) = (k:ZMod p)⁻¹ := eq_inv_of_mul_eq_one_left hak
  have hk1ne2 : ((k:ZMod p)-1) ≠ 0 := by rw [← hk1cast]; exact hk1ne
  have hXne : (2*((k:ZMod p)-1)) ≠ 0 := mul_ne_zero h2ne hk1ne2
  have hBB : ((Nat.choose (3*p-3+2*k) (p-1) / p:ℕ):ZMod p) = (((3*p-3+2*k)/p:ℕ):ZMod p) * (2*((k:ZMod p)-1))⁻¹ := by
    field_simp [h2ne, hk1ne2]
    linear_combination hbk
  rw [hAA, hBB, hk1cast]
  field_simp [hkne, hk1ne2, h2ne]
  ring

theorem T_factor (p k:ℕ)[hp:Fact p.Prime](hp5:5≤p)(hk2:2≤k)(hkp:k≤p-1) :
    T (p-1) k = p^2 * ((Nat.choose (p-1) k)^2 * (Nat.choose (p-1+k) k / p)
        * (Nat.choose (3*p-3+2*k) (p-1) / p)) := by
  unfold T
  have e2 : 3*(p-1)+2*k = 3*p-3+2*k := by omega
  have hd1 := p_dvd_choose1 p k (by omega) hkp
  have hd2 := p_dvd_choose2 p k hp5 hk2 hkp
  have hA : Nat.choose (p-1+k) k = p * (Nat.choose (p-1+k) k / p) := (Nat.mul_div_cancel' hd1).symm
  have hB : Nat.choose (3*p-3+2*k) (p-1) = p * (Nat.choose (3*p-3+2*k) (p-1) / p) := (Nat.mul_div_cancel' hd2).symm
  rw [e2]
  rw [show (p-1)+k = p-1+k from rfl]
  conv_lhs => rw [hA, hB]
  ring

lemma tele {A:Type*}[AddCommGroup A](a:ℕ)(ha:1≤a)(G:ℕ→A) :
    ∀ b, a-1 ≤ b → ∑ k ∈ Finset.Icc a b, (G (k-1) - G k) = G (a-1) - G b := by
  intro b hb
  induction b, hb using Nat.le_induction with
  | base =>
      rw [Finset.Icc_eq_empty (by omega)]; simp
  | succ b hb ih =>
      rw [Finset.sum_Icc_succ_top (by omega), ih]
      rw [show b+1-1 = b by omega]; abel

set_option maxHeartbeats 1000000 in
theorem sum_Mk (p:ℕ)[hp:Fact p.Prime](hp5:5≤p) :
    2 * ∑ k ∈ Finset.Icc 2 (p-1),
      (((Nat.choose (p-1) k)^2 * (Nat.choose (p-1+k) k / p)
        * (Nat.choose (3*p-3+2*k) (p-1) / p) : ℕ) : ZMod p) = 9 := by
  have hodd : p % 2 = 1 := hp.1.eq_two_or_odd.resolve_left (by omega)
  set m := (p+1)/2 with hm
  have h2m : 2*m = p+1 := by rw [hm]; omega
  set G : ℕ → ZMod p := fun j => ((j:ℕ):ZMod p)⁻¹ with hG
  -- rewrite summand
  have hsumrw : ∑ k ∈ Finset.Icc 2 (p-1),
      (((Nat.choose (p-1) k)^2 * (Nat.choose (p-1+k) k / p)
        * (Nat.choose (3*p-3+2*k) (p-1) / p) : ℕ) : ZMod p)
      = ∑ k ∈ Finset.Icc 2 (p-1),
          (((3*p-3+2*k)/p : ℕ):ZMod p) * (2:ZMod p)⁻¹ * (G (k-1) - G k) := by
    apply Finset.sum_congr rfl
    intro k hk
    rw [Finset.mem_Icc] at hk
    have := Mk_val p k hp5 hk.1 hk.2
    rw [this, hG]
  rw [hsumrw]
  -- split Icc 2 (p-1) = Icc 2 m ∪ Icc (m+1) (p-1)  via Ioc
  have hIcc1 : Finset.Icc 2 (p-1) = Finset.Ioc 1 (p-1) := by
    rw [show (2:ℕ) = 1+1 from rfl, Icc_add_one_left_eq_Ioc]
  have hIcc2 : Finset.Icc 2 m = Finset.Ioc 1 m := by
    rw [show (2:ℕ) = 1+1 from rfl, Icc_add_one_left_eq_Ioc]
  have hIcc3 : Finset.Icc (m+1) (p-1) = Finset.Ioc m (p-1) := by
    rw [Icc_add_one_left_eq_Ioc]
  have hsplit : ∑ k ∈ Finset.Icc 2 (p-1), (((3*p-3+2*k)/p : ℕ):ZMod p) * (2:ZMod p)⁻¹ * (G (k-1) - G k)
      = (∑ k ∈ Finset.Icc 2 m, (((3*p-3+2*k)/p : ℕ):ZMod p) * (2:ZMod p)⁻¹ * (G (k-1) - G k))
      + (∑ k ∈ Finset.Icc (m+1) (p-1), (((3*p-3+2*k)/p : ℕ):ZMod p) * (2:ZMod p)⁻¹ * (G (k-1) - G k)) := by
    rw [hIcc1, hIcc2, hIcc3]
    rw [← Finset.sum_Ioc_consecutive _ (show 1 ≤ m by omega) (show m ≤ p-1 by omega)]
  rw [hsplit]
  -- region 1: ck = 3
  have hr1 : ∑ k ∈ Finset.Icc 2 m, (((3*p-3+2*k)/p : ℕ):ZMod p) * (2:ZMod p)⁻¹ * (G (k-1) - G k)
      = (3:ZMod p) * (2:ZMod p)⁻¹ * (G 1 - G m) := by
    rw [show ∑ k ∈ Finset.Icc 2 m, (((3*p-3+2*k)/p : ℕ):ZMod p) * (2:ZMod p)⁻¹ * (G (k-1) - G k)
          = ∑ k ∈ Finset.Icc 2 m, (3:ZMod p) * (2:ZMod p)⁻¹ * (G (k-1) - G k) from ?_]
    · rw [← Finset.mul_sum, tele 2 (by omega) G m (by omega)]
    · apply Finset.sum_congr rfl
      intro k hk
      rw [Finset.mem_Icc] at hk
      have hck : (3*p-3+2*k)/p = 3 :=
        Nat.div_eq_of_lt_le (by omega) (by omega)
      rw [hck]; norm_num
  -- region 2: ck = 4
  have hr2 : ∑ k ∈ Finset.Icc (m+1) (p-1), (((3*p-3+2*k)/p : ℕ):ZMod p) * (2:ZMod p)⁻¹ * (G (k-1) - G k)
      = (4:ZMod p) * (2:ZMod p)⁻¹ * (G m - G (p-1)) := by
    rw [show ∑ k ∈ Finset.Icc (m+1) (p-1), (((3*p-3+2*k)/p : ℕ):ZMod p) * (2:ZMod p)⁻¹ * (G (k-1) - G k)
          = ∑ k ∈ Finset.Icc (m+1) (p-1), (4:ZMod p) * (2:ZMod p)⁻¹ * (G (k-1) - G k) from ?_]
    · rw [← Finset.mul_sum, tele (m+1) (by omega) G (p-1) (by omega)]
      rw [show (m+1)-1 = m by omega]
    · apply Finset.sum_congr rfl
      intro k hk
      rw [Finset.mem_Icc] at hk
      have hck : (3*p-3+2*k)/p = 4 :=
        Nat.div_eq_of_lt_le (by omega) (by omega)
      rw [hck]; norm_num
  rw [hr1, hr2]
  -- G values
  have hG1 : G 1 = 1 := by rw [hG]; simp
  have h2ne : (2:ZMod p) ≠ 0 := by
    have : ((2:ℕ):ZMod p) ≠ 0 := by rw [Ne, ZMod.natCast_eq_zero_iff]; intro h; have := Nat.le_of_dvd (by norm_num) h; omega
    simpa using this
  have hGm : G m = 2 := by
    simp only [hG]
    have hmc : (m:ZMod p) = (2:ZMod p)⁻¹ := by
      have : (2:ZMod p) * (m:ZMod p) = 1 := by
        have : ((2*m:ℕ):ZMod p) = ((p+1:ℕ):ZMod p) := by rw [h2m]
        push_cast at this
        rw [ZMod.natCast_self] at this
        linear_combination this
      field_simp at this ⊢
      linear_combination this
    rw [hmc, inv_inv]
  have hGp1 : G (p-1) = -1 := by
    simp only [hG]
    have hpm1 : ((p-1:ℕ):ZMod p) = -1 := by
      rw [Nat.cast_sub (by omega)]; rw [ZMod.natCast_self]; simp
    rw [hpm1]; simp
  rw [hG1, hGm, hGp1]
  field_simp
  ring

set_option maxHeartbeats 1000000 in
theorem bulk_mod (p:ℕ)[hp:Fact p.Prime](hp5:5≤p) :
    ((2 * ∑ k ∈ Finset.Icc 2 (p-1), T (p-1) k : ℕ) : ZMod (p^3))
      = 9 * (p:ZMod (p^3))^2 := by
  set Mk : ℕ → ℕ := fun k => (Nat.choose (p-1) k)^2 * (Nat.choose (p-1+k) k / p)
        * (Nat.choose (3*p-3+2*k) (p-1) / p) with hMk
  have hTf : ∑ k ∈ Finset.Icc 2 (p-1), T (p-1) k = p^2 * ∑ k ∈ Finset.Icc 2 (p-1), Mk k := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    rw [Finset.mem_Icc] at hk
    rw [hMk]; exact T_factor p k hp5 hk.1 hk.2
  set S := ∑ k ∈ Finset.Icc 2 (p-1), Mk k with hS
  rw [hTf]
  have hpc : ((2 * (p^2 * S) : ℕ) : ZMod (p^3)) = (p:ZMod (p^3))^2 * ((2*S:ℕ):ZMod (p^3)) := by
    push_cast; ring
  rw [hpc]
  have hred := reduce_p2' p (by omega) (((2*S:ℕ)):ZMod (p^3)) (((9:ℕ)):ZMod (p^3)) ?_
  · rw [hred]; push_cast; ring
  · rw [map_natCast, map_natCast]
    rw [Nat.cast_mul, hS, Nat.cast_sum]
    simp only [hMk, Nat.cast_ofNat]
    exact sum_Mk p hp5
lemma peel2 {F:Type*}[AddCommMonoid F](g:ℕ→F)(N:ℕ)(hN:2≤N) :
    ∑ k ∈ Finset.range N, g k = (∑ k ∈ Finset.range (N-2), g k) + g (N-2) + g (N-1) := by
  obtain ⟨M,rfl⟩ : ∃ M, N=M+2 := ⟨N-2, by omega⟩
  rw [Finset.sum_range_succ, Finset.sum_range_succ]
  congr 2

-- harmonic sum over [1,p-3] = 3/2  (range form)

lemma pprod2 {R:Type*}[CommMonoid R](f:ℕ→R)(N:ℕ)(hN:2≤N) :
    ∏ i ∈ Finset.range N, f i = (∏ i ∈ Finset.range (N-2), f (i+2)) * f 1 * f 0 := by
  obtain ⟨M,rfl⟩ : ∃ M, N=M+2 := ⟨N-2, by omega⟩
  rw [Finset.prod_range_succ', Finset.prod_range_succ']
  simp only [Nat.add_sub_cancel]



theorem harmonic_range (p:ℕ)[hp:Fact p.Prime](hp5:5≤p) :
    ∑ i ∈ Finset.range (p-3), ((i+1:ℕ):ZMod p)⁻¹ = 3 * (2:ZMod p)⁻¹ := by
  haveI : NeZero p := ⟨by have := hp.1.pos; omega⟩
  have hp2 : 2 < p := by omega
  have hfull : ∑ m ∈ Finset.range p, ((m:ZMod p))⁻¹ = 0 := by
    rw [zmod_sum_range]; exact sum_inv_zmod_eq_zero p hp2
  obtain ⟨n, rfl⟩ : ∃ n, p = n+1 := ⟨p-1, by omega⟩
  rw [Finset.sum_range_succ'] at hfull
  simp only [Nat.cast_zero, inv_zero, add_zero] at hfull
  rw [peel2 (fun k => ((k+1:ℕ):ZMod (n+1))⁻¹) n (by omega)] at hfull
  have c1 : ((n-2+1 : ℕ):ZMod (n+1)) = -2 := by
    have h0 : ((n-2+1:ℕ):ZMod (n+1)) + 2 = 0 := by
      have : ((n-2+1:ℕ):ZMod (n+1)) + 2 = (((n-2+1)+2 : ℕ):ZMod (n+1)) := by push_cast; ring
      rw [this, show (n-2+1)+2 = n+1 by omega, ZMod.natCast_self]
    linear_combination h0
  have c2 : ((n-1+1 : ℕ):ZMod (n+1)) = -1 := by
    have h0 : ((n-1+1:ℕ):ZMod (n+1)) + 1 = 0 := by
      have : ((n-1+1:ℕ):ZMod (n+1)) + 1 = (((n-1+1)+1 : ℕ):ZMod (n+1)) := by push_cast; ring
      rw [this, show (n-1+1)+1 = n+1 by omega, ZMod.natCast_self]
    linear_combination h0
  rw [c1, c2] at hfull
  have h2 : (2:ZMod (n+1)) ≠ 0 := by
    have : ((2:ℕ):ZMod (n+1)) ≠ 0 := by rw [Ne, ZMod.natCast_eq_zero_iff]; intro h; have := Nat.le_of_dvd (by norm_num) h; omega
    simpa using this
  rw [show n+1-3 = n-2 by omega]
  simp only [inv_neg, inv_one] at hfull
  linear_combination hfull - inv_mul_cancel₀ h2


lemma castHom_inv (p a:ℕ)[Fact p.Prime](hcop: a.Coprime p) :
    (ZMod.castHom (show p∣p^3 from ⟨p^2,by ring⟩) (ZMod p)) ((a:ZMod (p^3))⁻¹) = ((a:ZMod p))⁻¹ := by
  have hu : IsUnit ((a:ZMod (p^3))) := by rw[ZMod.isUnit_iff_coprime]; exact hcop.pow_right 3
  have h1 : (ZMod.castHom (show p∣p^3 from ⟨p^2,by ring⟩) (ZMod p)) ((a:ZMod (p^3))) = (a:ZMod p) := map_natCast _ a
  have h2 : (a:ZMod p) * (ZMod.castHom (show p∣p^3 from ⟨p^2,by ring⟩) (ZMod p)) ((a:ZMod (p^3))⁻¹) = 1 := by
    rw [← h1, ← map_mul, ZMod.mul_inv_of_unit _ hu, map_one]
  exact (inv_eq_of_mul_eq_one_right h2).symm


set_option maxHeartbeats 1000000 in
theorem T0_mod (p:ℕ)[hp:Fact p.Prime](hp5:5≤p) :
    (2 * (Nat.choose (3*p-3) (p-1)) : ZMod (p^3))
      = -2*(p:ZMod (p^3)) - 5*(p:ZMod (p^3))^2 := by
  obtain ⟨n, rfl⟩ : ∃ n, p = n+1 := ⟨p-1, by omega⟩
  have hn4 : 4 ≤ n := by omega
  -- integer identity
  have hC : (Nat.choose (3*n) n) * n.factorial = (2*n+1).ascFactorial n := by
    have h := choose_mul_fact_asc (2*n) n
    rwa [show 2*n+n = 3*n by ring] at h
  rw [show 3*(n+1)-3 = 3*n by omega, show (n+1)-1 = n by omega]
  -- key abbreviation
  set P : ZMod ((n+1)^3) := ((n+1:ℕ):ZMod ((n+1)^3)) with hP
  have hP3 : P^3 = 0 := by rw [hP, ← Nat.cast_pow, ZMod.natCast_self]
  -- 2 is a unit
  have h2cop : (2:ℕ).Coprime (n+1) := (Nat.coprime_primes Nat.prime_two hp.1).mpr (by omega)
  have h2u : IsUnit ((2:ℕ):ZMod ((n+1)^3)) := by rw [ZMod.isUnit_iff_coprime]; exact h2cop.pow_right 3
  set half : ZMod ((n+1)^3) := ((2:ℕ):ZMod ((n+1)^3))⁻¹ with hhalf0
  have hhalf : 2 * half = 1 := by
    rw [hhalf0]
    have : (2:ZMod ((n+1)^3)) = ((2:ℕ):ZMod ((n+1)^3)) := by push_cast; ring
    rw [this]; exact ZMod.mul_inv_of_unit _ h2u
  -- cast the integer identity, expand product
  have hCz : ((Nat.choose (3*n) n : ℕ):ZMod ((n+1)^3)) * ((n.factorial:ℕ):ZMod ((n+1)^3))
            = (((2*n+1).ascFactorial n : ℕ):ZMod ((n+1)^3)) := by
    rw [← Nat.cast_mul, hC]
  rw [Nat.ascFactorial_eq_prod_range, Nat.cast_prod] at hCz
  rw [pprod2 (fun i => ((2*n+1+i:ℕ):ZMod ((n+1)^3))) n (by omega)] at hCz
  -- rewrite the middle product into factorial * (prod of 1+e*b)
  have hbig : ∏ i ∈ Finset.range (n-2), ((2*n+1+(i+2):ℕ):ZMod ((n+1)^3))
            = (((n-2).factorial : ℕ):ZMod ((n+1)^3))
              * ∏ i ∈ Finset.range (n-2), (1 + (2*P) * ((i+1:ℕ):ZMod ((n+1)^3))⁻¹) := by
    rw [← Finset.prod_range_add_one_eq_factorial (n-2), Nat.cast_prod, ← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro i hi
    rw [Finset.mem_range] at hi
    have hcop : (i+1).Coprime (n+1) :=
      (hp.1.coprime_iff_not_dvd.mpr (by intro hd; have := Nat.le_of_dvd (by omega) hd; omega)).symm
    have huu : ((i+1:ℕ):ZMod ((n+1)^3)) * (((i+1:ℕ):ZMod ((n+1)^3)))⁻¹ = 1 :=
      ZMod.mul_inv_of_unit _ (by rw [ZMod.isUnit_iff_coprime]; exact hcop.pow_right 3)
    rw [show ((2*n+1+(i+2):ℕ):ZMod ((n+1)^3)) = ((i+1:ℕ):ZMod ((n+1)^3)) + 2*P from by rw [hP]; push_cast; ring]
    linear_combination -(2*P)*huu
  rw [hbig] at hCz
  -- apply prod_one_add_e
  rw [prod_one_add_e (2*P) (by rw [mul_pow]; rw [hP3]; ring) half hhalf
        (Finset.range (n-2)) (fun i => ((i+1:ℕ):ZMod ((n+1)^3))⁻¹)] at hCz
  -- now hCz: C * (n! cast) = ((n-2)! * (1 + 2P*Σ + (2P)^2*G*half)) * f1 * f0
  -- simplify f0, f1
  have hf0 : ((2*n+1+0:ℕ):ZMod ((n+1)^3)) = 2*P - 1 := by rw [hP]; push_cast; ring
  have hf1 : ((2*n+1+1:ℕ):ZMod ((n+1)^3)) = 2*P := by rw [hP]; push_cast; ring
  rw [hf0, hf1] at hCz
  -- relate (n!) and (n-2)!
  have hfact : (n.factorial : ℕ) = n * (n-1) * (n-2).factorial := by
    have e1 : n = (n-1)+1 := by omega
    have e2 : n-1 = (n-2)+1 := by omega
    rw [e1, Nat.factorial_succ, e2, Nat.factorial_succ]
    rw [← e2, ← e1]; ring
  rw [hfact, Nat.cast_mul, Nat.cast_mul] at hCz
  -- cast n and n-1
  have hcn : ((n:ℕ):ZMod ((n+1)^3)) = P - 1 := by rw [hP]; push_cast; ring
  have hcn1 : ((n-1:ℕ):ZMod ((n+1)^3)) = P - 2 := by
    rw [hP, show (n-1:ℕ) = n-1 from rfl, Nat.cast_sub (by omega)]; push_cast; ring
  rw [hcn, hcn1] at hCz
  -- Now harmonic reduction:  P^2 * (-4 * Σ) = P^2 * (-6)
  set Sb : ZMod ((n+1)^3) := ∑ i ∈ Finset.range (n-2), ((i+1:ℕ):ZMod ((n+1)^3))⁻¹ with hSb
  have hred : P^2 * (-4 * Sb) = P^2 * (-6 : ZMod ((n+1)^3)) := by
    rw [hP]
    apply reduce_p2' (n+1) (by omega)
    -- castHom of Sb = harmonic value
    have hcast : (ZMod.castHom (show (n+1) ∣ (n+1)^3 by exact ⟨(n+1)^2, by ring⟩) (ZMod (n+1))) Sb
               = 3 * (2:ZMod (n+1))⁻¹ := by
      rw [hSb, map_sum]
      rw [show (∑ i ∈ Finset.range (n-2), (ZMod.castHom (show (n+1) ∣ (n+1)^3 by exact ⟨(n+1)^2, by ring⟩) (ZMod (n+1))) (((i+1:ℕ):ZMod ((n+1)^3))⁻¹))
            = ∑ i ∈ Finset.range (n+1-3), ((i+1:ℕ):ZMod (n+1))⁻¹ from ?_]
      · exact harmonic_range (n+1) hp5
      · rw [show n+1-3 = n-2 by omega]
        apply Finset.sum_congr rfl
        intro i hi
        rw [Finset.mem_range] at hi
        have hcop : (i+1).Coprime (n+1) :=
          (hp.1.coprime_iff_not_dvd.mpr (by intro hd; have := Nat.le_of_dvd (by omega) hd; omega)).symm
        exact castHom_inv (n+1) (i+1) hcop
    have h2u' : (2:ZMod (n+1)) ≠ 0 := by
      have : ((2:ℕ):ZMod (n+1)) ≠ 0 := by rw [Ne, ZMod.natCast_eq_zero_iff]; intro h; have := Nat.le_of_dvd (by norm_num) h; omega
      simpa using this
    rw [show (-4 * Sb : ZMod ((n+1)^3)) = ((-4:ℤ):ZMod ((n+1)^3))*Sb from by push_cast; ring,
        show ((-6:ZMod ((n+1)^3))) = ((-6:ℤ):ZMod ((n+1)^3)) from by push_cast; ring,
        map_mul, map_intCast, map_intCast, hcast]
    push_cast
    field_simp
    ring
  set C := ((3*n).choose n : ZMod ((n+1)^3)) with hCdef
  set S2 := ∑ i ∈ Finset.range (n-2), (((i+1:ℕ):ZMod ((n+1)^3))⁻¹)^2 with hS2def
  set F2 := (((n-2).factorial:ℕ):ZMod ((n+1)^3)) with hF2def
  have hF2u : IsUnit F2 := by
    rw [hF2def, ZMod.isUnit_iff_coprime]
    exact (Nat.Coprime.pow_right 3 ((hp.1.coprime_iff_not_dvd.mpr (fun hd => by have := (Nat.Prime.dvd_factorial hp.1).mp hd; omega)).symm))
  have hPu : IsUnit ((P-1)*(P-2)) := by
    have hu1 : IsUnit (P-1) := by
      rw [← hcn, ZMod.isUnit_iff_coprime]
      exact (Nat.Coprime.pow_right 3 ((hp.1.coprime_iff_not_dvd.mpr (fun hd => by have := Nat.le_of_dvd (by omega) hd; omega)).symm))
    have hu2 : IsUnit (P-2) := by
      rw [← hcn1, ZMod.isUnit_iff_coprime]
      exact (Nat.Coprime.pow_right 3 ((hp.1.coprime_iff_not_dvd.mpr (fun hd => by have := Nat.le_of_dvd (by omega) hd; omega)).symm))
    exact hu1.mul hu2
  have hkey : F2 * (C*(P-1)*(P-2))
            = F2 * ((1 + 2*P*Sb + (2*P)^2*(Sb^2-S2)*half)*(2*P)*(2*P-1)) := by
    linear_combination hCz
  have hEq1 := hF2u.mul_right_injective hkey
  have hEq2 : C*(P-1)*(P-2) = -2*P-2*P^2 := by
    rw [hEq1]
    linear_combination hred + (8*Sb - 8*(Sb^2-S2)*half + 16*P*(Sb^2-S2)*half)*hP3
  have hC2 : (2*C)*((P-1)*(P-2)) = (-2*P-5*P^2)*((P-1)*(P-2)) := by
    have h0 : (2*C)*((P-1)*(P-2)) = 2*(C*(P-1)*(P-2)) := by ring
    rw [h0, hEq2]
    linear_combination (5*P-13)*hP3
  have hfin := hPu.mul_left_injective hC2
  linear_combination hfin



theorem harmonic_full (p:ℕ)[hp:Fact p.Prime](hp5:5≤p) :
    ∑ i ∈ Finset.range (p-1), ((i+1:ℕ):ZMod p)⁻¹ = 0 := by
  haveI : NeZero p := ⟨by have := hp.1.pos; omega⟩
  have hp2 : 2 < p := by omega
  have hfull : ∑ m ∈ Finset.range p, ((m:ZMod p))⁻¹ = 0 := by
    rw [zmod_sum_range]; exact sum_inv_zmod_eq_zero p hp2
  obtain ⟨n, rfl⟩ : ∃ n, p = n+1 := ⟨p-1, by omega⟩
  rw [Finset.sum_range_succ'] at hfull
  simp only [Nat.cast_zero, inv_zero, add_zero] at hfull
  rw [show n+1-1 = n by omega]
  exact hfull

-- reduce: p * x = p * y  in ZMod (p^3) from equality mod p^2

lemma reduce_p1_3 (p : ℕ) (hp : 1 ≤ p) (x y : ZMod (p^3))
    (h : (ZMod.castHom (show p^2 ∣ p^3 by exact ⟨p, by ring⟩) (ZMod (p^2))) x
       = (ZMod.castHom (show p^2 ∣ p^3 by exact ⟨p, by ring⟩) (ZMod (p^2))) y) :
    (p:ZMod (p^3)) * x = (p:ZMod (p^3)) * y := by
  haveI : NeZero (p^3) := ⟨by positivity⟩
  haveI : NeZero (p^2) := ⟨by positivity⟩
  have hx : (ZMod.castHom (show p^2 ∣ p^3 by exact ⟨p, by ring⟩) (ZMod (p^2))) x = (x.val : ZMod (p^2)) := by
    conv_lhs => rw [← ZMod.natCast_zmod_val x]
    rw [map_natCast]
  have hy : (ZMod.castHom (show p^2 ∣ p^3 by exact ⟨p, by ring⟩) (ZMod (p^2))) y = (y.val : ZMod (p^2)) := by
    conv_lhs => rw [← ZMod.natCast_zmod_val y]
    rw [map_natCast]
  rw [hx, hy] at h
  have hpd : ((p:ℤ)^2) ∣ ((x.val:ℤ) - (y.val:ℤ)) := by
    have hd0 : (((p^2:ℕ)):ℤ) ∣ ((x.val:ℤ) - (y.val:ℤ)) := by
      rw [← ZMod.intCast_zmod_eq_zero_iff_dvd, Int.cast_sub, Int.cast_natCast, Int.cast_natCast, h, sub_self]
    rwa [Nat.cast_pow] at hd0
  obtain ⟨d, hd⟩ := hpd
  have e1 : x - y = ((((p:ℤ)^2) * d : ℤ) : ZMod (p^3)) := by
    rw [← hd, Int.cast_sub, Int.cast_natCast, Int.cast_natCast,
        ZMod.natCast_zmod_val, ZMod.natCast_zmod_val]
  have e2 : (p:ZMod (p^3)) * (x - y) = 0 := by
    rw [e1]
    have : (p:ZMod (p^3)) * ((((p:ℤ)^2) * d : ℤ) : ZMod (p^3))
         = (((p:ℕ)^3 : ℕ):ZMod (p^3)) * (d : ZMod (p^3)) := by push_cast; ring
    rw [this, ZMod.natCast_self, zero_mul]
  linear_combination e2


lemma reduce_gen (p a b:ℕ)(hp:1≤p)(hba:b≤a)(x y:ZMod (p^a))
    (h : (ZMod.castHom (pow_dvd_pow p hba) (ZMod (p^b))) x
       = (ZMod.castHom (pow_dvd_pow p hba) (ZMod (p^b))) y) :
    (p:ZMod (p^a))^(a-b) * x = (p:ZMod (p^a))^(a-b) * y := by
  haveI : NeZero (p^a) := ⟨by positivity⟩
  haveI : NeZero (p^b) := ⟨by positivity⟩
  have hx : (ZMod.castHom (pow_dvd_pow p hba) (ZMod (p^b))) x = (x.val : ZMod (p^b)) := by
    conv_lhs => rw [← ZMod.natCast_zmod_val x]; rw [map_natCast]
  have hy : (ZMod.castHom (pow_dvd_pow p hba) (ZMod (p^b))) y = (y.val : ZMod (p^b)) := by
    conv_lhs => rw [← ZMod.natCast_zmod_val y]; rw [map_natCast]
  rw [hx, hy] at h
  have hpd : ((p:ℤ)^b) ∣ ((x.val:ℤ) - (y.val:ℤ)) := by
    have hd0 : (((p^b:ℕ)):ℤ) ∣ ((x.val:ℤ) - (y.val:ℤ)) := by
      rw [← ZMod.intCast_zmod_eq_zero_iff_dvd, Int.cast_sub, Int.cast_natCast, Int.cast_natCast, h, sub_self]
    rwa [Nat.cast_pow] at hd0
  obtain ⟨d, hd⟩ := hpd
  have e1 : x - y = ((((p:ℤ)^b) * d : ℤ) : ZMod (p^a)) := by
    rw [← hd, Int.cast_sub, Int.cast_natCast, Int.cast_natCast,
        ZMod.natCast_zmod_val, ZMod.natCast_zmod_val]
  have e2 : (p:ZMod (p^a))^(a-b) * (x - y) = 0 := by
    rw [e1]
    have hcast : (p:ZMod (p^a))^(a-b) * ((((p:ℤ)^b) * d : ℤ) : ZMod (p^a))
         = (((p:ℕ)^a : ℕ):ZMod (p^a)) * (d : ZMod (p^a)) := by
      push_cast
      rw [← mul_assoc, ← pow_add, show a-b+b = a by omega]
    rw [hcast, ZMod.natCast_self, zero_mul]
  linear_combination e2


lemma castHom_inv_to_p (p e a:ℕ)[Fact p.Prime](he:1≤e)(hcop: a.Coprime p) :
    (ZMod.castHom (dvd_pow_self p (show e ≠ 0 by omega)) (ZMod p)) ((a:ZMod (p^e))⁻¹) = ((a:ZMod p))⁻¹ := by
  have hu : IsUnit ((a:ZMod (p^e))) := by rw [ZMod.isUnit_iff_coprime]; exact hcop.pow_right e
  have h1 : (ZMod.castHom (dvd_pow_self p (show e ≠ 0 by omega)) (ZMod p)) ((a:ZMod (p^e))) = (a:ZMod p) := map_natCast _ a
  have h2 : (a:ZMod p) * (ZMod.castHom (dvd_pow_self p (show e ≠ 0 by omega)) (ZMod p)) ((a:ZMod (p^e))⁻¹) = 1 := by
    rw [← h1, ← map_mul, ZMod.mul_inv_of_unit _ hu, map_one]
  exact (inv_eq_of_mul_eq_one_right h2).symm


lemma reduce_p0_2 (p : ℕ) (hp : 1 ≤ p) (x y : ZMod (p^2))
    (h : (ZMod.castHom (dvd_pow_self p (show (2:ℕ) ≠ 0 by omega)) (ZMod p)) x
       = (ZMod.castHom (dvd_pow_self p (show (2:ℕ) ≠ 0 by omega)) (ZMod p)) y) :
    (p:ZMod (p^2)) * x = (p:ZMod (p^2)) * y := by
  haveI : NeZero (p^2) := ⟨by positivity⟩
  have hx : (ZMod.castHom (dvd_pow_self p (show (2:ℕ) ≠ 0 by omega)) (ZMod p)) x = (x.val : ZMod p) := by
    conv_lhs => rw [← ZMod.natCast_zmod_val x]; rw [map_natCast]
  have hy : (ZMod.castHom (dvd_pow_self p (show (2:ℕ) ≠ 0 by omega)) (ZMod p)) y = (y.val : ZMod p) := by
    conv_lhs => rw [← ZMod.natCast_zmod_val y]; rw [map_natCast]
  rw [hx, hy] at h
  have hpd : (p:ℤ) ∣ ((x.val:ℤ) - (y.val:ℤ)) := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd, Int.cast_sub, Int.cast_natCast, Int.cast_natCast, h, sub_self]
  obtain ⟨d, hd⟩ := hpd
  have e1 : x - y = (((p:ℤ) * d : ℤ) : ZMod (p^2)) := by
    rw [← hd, Int.cast_sub, Int.cast_natCast, Int.cast_natCast,
        ZMod.natCast_zmod_val, ZMod.natCast_zmod_val]
  have e2 : (p:ZMod (p^2)) * (x - y) = 0 := by
    rw [e1]
    have hcast : (p:ZMod (p^2)) * (((p:ℤ) * d : ℤ) : ZMod (p^2))
         = (((p:ℕ)^2 : ℕ):ZMod (p^2)) * (d : ZMod (p^2)) := by push_cast; ring
    rw [hcast, ZMod.natCast_self, zero_mul]
  linear_combination e2


set_option maxHeartbeats 1000000 in
theorem C3p1_mod (p:ℕ)[hp:Fact p.Prime](hp5:5≤p) :
    ((Nat.choose (3*p-1) (p-1) : ℕ):ZMod (p^2)) = 1 := by
  obtain ⟨n, rfl⟩ : ∃ n, p = n+1 := ⟨p-1, by omega⟩
  have hn4 : 4 ≤ n := by omega
  have hC : (Nat.choose (3*n+2) n) * n.factorial = (2*n+3).ascFactorial n := by
    have h := choose_mul_fact_asc (2*n+2) n
    rwa [show 2*n+2+n = 3*n+2 by ring, show 2*n+2+1 = 2*n+3 by ring] at h
  rw [show 3*(n+1)-1 = 3*n+2 by omega, show (n+1)-1 = n by omega]
  set P : ZMod ((n+1)^2) := ((n+1:ℕ):ZMod ((n+1)^2)) with hP
  have hP2 : P^2 = 0 := by rw [hP, ← Nat.cast_pow, ZMod.natCast_self]
  have hP3 : P^3 = 0 := by rw [show (3:ℕ) = 2+1 by rfl, pow_add, hP2, zero_mul]
  have h2cop : (2:ℕ).Coprime (n+1) := (Nat.coprime_primes Nat.prime_two hp.1).mpr (by omega)
  have h2u : IsUnit ((2:ℕ):ZMod ((n+1)^2)) := by rw [ZMod.isUnit_iff_coprime]; exact h2cop.pow_right 2
  set half : ZMod ((n+1)^2) := ((2:ℕ):ZMod ((n+1)^2))⁻¹ with hhalf0
  have hhalf : 2 * half = 1 := by
    rw [hhalf0]; rw [show (2:ZMod ((n+1)^2)) = ((2:ℕ):ZMod ((n+1)^2)) by push_cast; ring]
    exact ZMod.mul_inv_of_unit _ h2u
  -- cast and expand product
  have hCz : ((Nat.choose (3*n+2) n : ℕ):ZMod ((n+1)^2)) * ((n.factorial:ℕ):ZMod ((n+1)^2))
            = (((2*n+3).ascFactorial n : ℕ):ZMod ((n+1)^2)) := by rw [← Nat.cast_mul, hC]
  rw [Nat.ascFactorial_eq_prod_range, Nat.cast_prod] at hCz
  -- product into factorial * prod(1+e b)
  have hbig : ∏ i ∈ Finset.range n, ((2*n+3+i:ℕ):ZMod ((n+1)^2))
            = ((n.factorial : ℕ):ZMod ((n+1)^2))
              * ∏ i ∈ Finset.range n, (1 + (2*P) * ((i+1:ℕ):ZMod ((n+1)^2))⁻¹) := by
    rw [← Finset.prod_range_add_one_eq_factorial n, Nat.cast_prod, ← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro i hi
    rw [Finset.mem_range] at hi
    have hcop : (i+1).Coprime (n+1) :=
      (hp.1.coprime_iff_not_dvd.mpr (by intro hd; have := Nat.le_of_dvd (by omega) hd; omega)).symm
    have huu : ((i+1:ℕ):ZMod ((n+1)^2)) * (((i+1:ℕ):ZMod ((n+1)^2)))⁻¹ = 1 :=
      ZMod.mul_inv_of_unit _ (by rw [ZMod.isUnit_iff_coprime]; exact hcop.pow_right 2)
    rw [show ((2*n+3+i:ℕ):ZMod ((n+1)^2)) = ((i+1:ℕ):ZMod ((n+1)^2)) + 2*P from by rw [hP]; push_cast; ring]
    linear_combination -(2*P)*huu
  rw [hbig] at hCz
  rw [prod_one_add_e (2*P) (by rw [mul_pow]; rw [hP3]; ring) half hhalf
        (Finset.range n) (fun i => ((i+1:ℕ):ZMod ((n+1)^2))⁻¹)] at hCz
  -- the e^2 term vanishes since (2P)^2 = 0
  set Sb : ZMod ((n+1)^2) := ∑ i ∈ Finset.range n, ((i+1:ℕ):ZMod ((n+1)^2))⁻¹ with hSb
  set S2 : ZMod ((n+1)^2) := ∑ i ∈ Finset.range n, (((i+1:ℕ):ZMod ((n+1)^2))⁻¹)^2 with hS2
  -- 2P * Sb = 0
  have hred : (2*P) * Sb = 0 := by
    have hstep : (2*P)*Sb = (↑(n+1):ZMod ((n+1)^2)) * (2*Sb) := by rw [hP]; ring
    rw [hstep]
    have h0 : (↑(n+1):ZMod ((n+1)^2)) * (2*Sb) = (↑(n+1):ZMod ((n+1)^2)) * (0:ZMod ((n+1)^2)) := by
      apply reduce_p0_2 (n+1) (by omega)
      rw [map_mul, map_sum, map_zero]
      have hsum0 : (∑ i ∈ Finset.range n, (ZMod.castHom (dvd_pow_self (n+1) (show (2:ℕ) ≠ 0 by omega)) (ZMod (n+1))) (((i+1:ℕ):ZMod ((n+1)^2))⁻¹)) = (0:ZMod (n+1)) := by
        rw [← harmonic_full (n+1) hp5]
        apply Finset.sum_congr rfl
        intro i hi
        rw [Finset.mem_range] at hi
        have hcop : (i+1).Coprime (n+1) :=
          (hp.1.coprime_iff_not_dvd.mpr (by intro hd; have := Nat.le_of_dvd (by omega) hd; omega)).symm
        exact castHom_inv_to_p (n+1) 2 (i+1) (by omega) hcop
      rw [hsum0]; ring
    rw [h0]; ring
  -- now hCz: C * n! = n! * (1 + 2P*Sb + (2P)^2*(Sb^2-S2)*half)
  set C := ((3*n+2).choose n : ZMod ((n+1)^2)) with hCdef
  set F := ((n.factorial:ℕ):ZMod ((n+1)^2)) with hFdef
  have hFu : IsUnit F := by
    rw [hFdef, ZMod.isUnit_iff_coprime]
    exact (Nat.Coprime.pow_right 2 ((hp.1.coprime_iff_not_dvd.mpr (fun hd => by have := (Nat.Prime.dvd_factorial hp.1).mp hd; omega)).symm))
  have hkey : F * C = F * 1 := by
    rw [mul_one]
    have hsq : (2*P)^2 = 0 := by rw [mul_pow, hP2]; ring
    linear_combination hCz + (F * (Sb^2 - S2) * half) * hsq + F * hred
  exact hFu.mul_right_injective hkey


set_option maxHeartbeats 1000000 in
theorem T1_mod (p:ℕ)[hp:Fact p.Prime](hp5:5≤p) :
    (2 * ((Nat.choose (p-1) 1)^2 * (Nat.choose ((p-1)+1) 1) * (Nat.choose (3*(p-1)+2*1) (p-1))) : ZMod (p^3))
      = 2*(p:ZMod (p^3)) - 4*(p:ZMod (p^3))^2 := by
  have hC3 := C3p1_mod p hp5
  obtain ⟨n, rfl⟩ : ∃ n, p = n+1 := ⟨p-1, by omega⟩
  have hn4 : 4 ≤ n := by omega
  rw [show (n+1)-1 = n by omega, Nat.choose_one_right, Nat.choose_one_right,
      show 3*n+2*1 = 3*n+2 by ring, show 3*(n+1)-1 = 3*n+2 by omega] at *
  have hQ2 : ((n+1:ℕ):ZMod ((n+1)^2))^2 = 0 := by rw [← Nat.cast_pow, ZMod.natCast_self]
  have key : (↑(n+1):ZMod ((n+1)^3)) * (2*((↑(n+1):ZMod ((n+1)^3))-1)^2*(↑((3*n+2).choose n):ZMod ((n+1)^3)))
           = (↑(n+1):ZMod ((n+1)^3)) * (2 - 4*(↑(n+1):ZMod ((n+1)^3))) := by
    apply reduce_p1_3 (n+1) (by omega)
    simp only [map_mul, map_pow, map_sub, map_ofNat, map_one, map_natCast]
    rw [hC3]
    linear_combination (2:ZMod ((n+1)^2)) * hQ2
  rw [show (2 * ((n:ZMod ((n+1)^3))^2 * (↑(n+1)) * ↑((3*n+2).choose n)) : ZMod ((n+1)^3))
        = (↑(n+1):ZMod ((n+1)^3)) * (2*((↑(n+1):ZMod ((n+1)^3))-1)^2*(↑((3*n+2).choose n))) from by push_cast; ring,
      show (2*(↑(n+1):ZMod ((n+1)^3)) - 4*(↑(n+1):ZMod ((n+1)^3))^2 : ZMod ((n+1)^3))
        = (↑(n+1):ZMod ((n+1)^3))*(2-4*(↑(n+1):ZMod ((n+1)^3))) from by ring]
  exact key



theorem apm1 (p:ℕ)[hp:Fact p.Prime](hp5:5≤p) :
    (p^3 : ℕ) ∣ ∑ k ∈ Finset.range p, T (p-1) k := by
  haveI : NeZero (p^3) := ⟨by positivity⟩
  have hT0eq : T (p-1) 0 = Nat.choose (3*p-3) (p-1) := by
    unfold T
    rw [show 3*(p-1)+2*0 = 3*p-3 by omega]
    simp
  have hT1eq : T (p-1) 1 = (Nat.choose (p-1) 1)^2 * (Nat.choose ((p-1)+1) 1) * (Nat.choose (3*(p-1)+2*1) (p-1)) := rfl
  have e : (∑ k ∈ Finset.range p, T (p-1) k)
      = T (p-1) 0 + T (p-1) 1 + ∑ k ∈ Finset.Icc 2 (p-1), T (p-1) k := by
    rw [Finset.range_eq_Ico, ← Finset.sum_Ico_consecutive _ (Nat.zero_le 2) (show 2 ≤ p by omega),
        Nat.Ico_zero_eq_range, Finset.sum_range_succ, Finset.sum_range_one,
        show Finset.Ico 2 p = Finset.Icc 2 (p-1) by ext x; simp only [Finset.mem_Ico, Finset.mem_Icc]; omega]
  have h2u : IsUnit ((2:ℕ):ZMod (p^3)) := by
    rw [ZMod.isUnit_iff_coprime]
    exact ((Nat.coprime_primes Nat.prime_two hp.1).mpr (by omega)).pow_right 3
  have key : ((2:ℕ):ZMod (p^3)) * ((∑ k ∈ Finset.range p, T (p-1) k :ℕ):ZMod (p^3)) = 0 := by
    rw [e, Nat.cast_add, Nat.cast_add, hT0eq]
    have a0 := T0_mod p hp5
    have a1 := T1_mod p hp5
    have a2 := bulk_mod p hp5
    rw [Nat.cast_mul, Nat.cast_ofNat] at a2
    have hT1cast : ((T (p-1) 1 :ℕ):ZMod (p^3))
        = ((Nat.choose (p-1) 1):ZMod (p^3))^2 * ((Nat.choose ((p-1)+1) 1):ZMod (p^3))
            * ((Nat.choose (3*(p-1)+2*1) (p-1)):ZMod (p^3)) := by
      rw [hT1eq]; push_cast; ring
    rw [hT1cast, Nat.cast_ofNat]
    linear_combination a0 + a1 + a2
  have hN0 : ((∑ k ∈ Finset.range p, T (p-1) k :ℕ):ZMod (p^3)) = 0 :=
    (h2u.mul_right_eq_zero).mp key
  exact (ZMod.natCast_eq_zero_iff _ (p^3)).mp hN0
