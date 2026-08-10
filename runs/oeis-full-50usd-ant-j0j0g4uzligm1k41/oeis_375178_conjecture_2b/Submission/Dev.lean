import FormalConjectures.Util.ProblemImports
open Finset
variable {p : ℕ}

/-- Additive split over `range (p*M)` into the `p`-multiples part and the rest. -/
lemma sum_split_range {M₀ : Type*} [AddCommMonoid M₀] (p M : ℕ) (hp : 0 < p) (f : ℕ → M₀) :
    ∑ i ∈ range (p*M), f i
      = (∑ t ∈ range M, f (p*t)) + ∑ i ∈ (range (p*M)).filter (fun i => ¬ p ∣ i), f i := by
  rw [← Finset.sum_filter_add_sum_filter_not (range (p*M)) (fun i => p ∣ i) f]
  congr 1
  have hset : (range (p*M)).filter (fun i => p ∣ i) = (range M).image (fun t => p*t) := by
    ext i
    simp only [mem_filter, mem_range, mem_image]
    constructor
    · rintro ⟨hi, t, rfl⟩
      exact ⟨t, lt_of_mul_lt_mul_left hi (Nat.zero_le p), rfl⟩
    · rintro ⟨t, ht, rfl⟩
      exact ⟨Nat.mul_lt_mul_of_pos_left ht hp, ⟨t, rfl⟩⟩
  rw [hset, Finset.sum_image]
  intro a _ b _ h; exact Nat.eq_of_mul_eq_mul_left hp h

/-- The decomposition `D = S2 + S1` over ℤ. -/
lemma D_decomp (m r : ℕ) (hp : 0 < p) (hr : 1 ≤ r) :
    (∑ k ∈ range (p^r), (Nat.multichoose (p^r) k ^ (2*m+1) : ℤ))
      - ∑ j ∈ range (p^(r-1)), (Nat.multichoose (p^(r-1)) j ^ (2*m+1) : ℤ)
    = (∑ t ∈ range (p^(r-1)),
        ((Nat.multichoose (p^r) (p*t) ^ (2*m+1) : ℤ) - (Nat.multichoose (p^(r-1)) t ^ (2*m+1) : ℤ)))
      + ∑ k ∈ (range (p^r)).filter (fun k => ¬ p ∣ k),
          (Nat.multichoose (p^r) k ^ (2*m+1) : ℤ) := by
  have heq : p^r = p * p^(r-1) := by
    conv_lhs => rw [show r = (r-1)+1 by omega]
    rw [pow_succ']
  rw [heq, sum_split_range p (p^(r-1)) hp (fun k => (Nat.multichoose (p * p^(r-1)) k ^ (2*m+1) : ℤ))]
  rw [Finset.sum_sub_distrib]
  ring_nf

/-- Outer bridge: `p^K ∣ S1` and `p^K ∣ S2` (as ℤ) give the target `ModEq`. -/
lemma modeq_of_S (m r K : ℕ) (hp : 0 < p) (hr : 1 ≤ r)
    (hS2 : (p^K : ℤ) ∣ ∑ t ∈ range (p^(r-1)),
        ((Nat.multichoose (p^r) (p*t) ^ (2*m+1) : ℤ) - (Nat.multichoose (p^(r-1)) t ^ (2*m+1) : ℤ)))
    (hS1 : (p^K : ℤ) ∣ ∑ k ∈ (range (p^r)).filter (fun k => ¬ p ∣ k),
          (Nat.multichoose (p^r) k ^ (2*m+1) : ℤ)) :
    (∑ k ∈ range (p^r), Nat.multichoose (p^r) k ^ (2*m+1))
      ≡ (∑ j ∈ range (p^(r-1)), Nat.multichoose (p^(r-1)) j ^ (2*m+1)) [MOD p^K] := by
  rw [Nat.modEq_iff_dvd]
  have hD : (p^K : ℤ) ∣
      (∑ k ∈ range (p^r), (Nat.multichoose (p^r) k ^ (2*m+1) : ℤ))
      - ∑ j ∈ range (p^(r-1)), (Nat.multichoose (p^(r-1)) j ^ (2*m+1) : ℤ) := by
    rw [D_decomp m r hp hr]; exact dvd_add hS2 hS1
  have hcast : ((∑ j ∈ range (p^(r-1)), Nat.multichoose (p^(r-1)) j ^ (2*m+1) : ℕ) : ℤ)
      - ((∑ k ∈ range (p^r), Nat.multichoose (p^r) k ^ (2*m+1) : ℕ) : ℤ)
      = -((∑ k ∈ range (p^r), (Nat.multichoose (p^r) k ^ (2*m+1) : ℤ))
          - ∑ j ∈ range (p^(r-1)), (Nat.multichoose (p^(r-1)) j ^ (2*m+1) : ℤ)) := by
    push_cast; ring
  rw [hcast]
  exact (dvd_neg).mpr hD

/-- Split a product over `range (p*M)` into the `p`-multiples part and the rest. -/
lemma prod_split_range (p M : ℕ) (hp : 0 < p) (f : ℕ → ℕ) :
    ∏ i ∈ range (p*M), f i
      = (∏ t ∈ range M, f (p*t)) * ∏ i ∈ (range (p*M)).filter (fun i => ¬ p ∣ i), f i := by
  rw [← Finset.prod_filter_mul_prod_filter_not (range (p*M)) (fun i => p ∣ i) f]
  congr 1
  have hset : (range (p*M)).filter (fun i => p ∣ i) = (range M).image (fun t => p*t) := by
    ext i
    simp only [mem_filter, mem_range, mem_image]
    constructor
    · rintro ⟨hi, t, rfl⟩
      exact ⟨t, lt_of_mul_lt_mul_left hi (Nat.zero_le p), rfl⟩
    · rintro ⟨t, ht, rfl⟩
      exact ⟨Nat.mul_lt_mul_of_pos_left ht hp, ⟨t, rfl⟩⟩
  rw [hset, Finset.prod_image]
  intro a _ b _ h; exact Nat.eq_of_mul_eq_mul_left hp h

/-- Split a product over `Ico 1 (p*N+1)` by divisibility of the value by `p`. -/
lemma prod_split_Ico (p N : ℕ) (hp : 0 < p) (f : ℕ → ℕ) :
    ∏ v ∈ Ico 1 (p*N+1), f v
      = (∏ t ∈ Ico 1 (N+1), f (p*t)) * ∏ v ∈ (Ico 1 (p*N+1)).filter (fun v => ¬ p ∣ v), f v := by
  rw [← Finset.prod_filter_mul_prod_filter_not (Ico 1 (p*N+1)) (fun v => p ∣ v) f]
  congr 1
  have hset : (Ico 1 (p*N+1)).filter (fun v => p ∣ v) = (Ico 1 (N+1)).image (fun t => p*t) := by
    ext v
    simp only [mem_filter, mem_Ico, mem_image]
    constructor
    · rintro ⟨⟨h1, h2⟩, t, rfl⟩
      refine ⟨t, ⟨?_, ?_⟩, rfl⟩
      · rcases Nat.eq_zero_or_pos t with h|h
        · simp [h] at h1
        · exact h
      · have hle : p*t ≤ p*N := by omega
        exact Nat.lt_succ_of_le (Nat.le_of_mul_le_mul_left hle hp)
    · rintro ⟨t, ⟨ht1, ht2⟩, rfl⟩
      have hpt : 0 < p*t := Nat.mul_pos hp (by omega)
      have hle : p*t ≤ p*N := Nat.mul_le_mul_left p (by omega)
      exact ⟨⟨by omega, by omega⟩, ⟨t, rfl⟩⟩
  rw [hset, Finset.prod_image]
  intro a _ b _ h; exact Nat.eq_of_mul_eq_mul_left hp h

lemma ratio_identity (r j : ℕ) (hp : 0 < p) (hr : 1 ≤ r) :
    (Nat.multichoose (p^r) (p*j)) * (∏ s ∈ (range (p*j)).filter (fun s => ¬ p ∣ s), s)
      = (Nat.multichoose (p^(r-1)) j)
          * (∏ s ∈ (range (p*j)).filter (fun s => ¬ p ∣ s), (p^r + s)) := by
  set R := (range (p*j)).filter (fun s => ¬ p ∣ s) with hR
  have heq : p^r = p * p^(r-1) := by
    conv_lhs => rw [show r = (r-1)+1 by omega]
    rw [pow_succ']
  -- set equality between Ico-filter and range-filter
  have hFG_set : (Ico 1 (p*j+1)).filter (fun v => ¬ p ∣ v) = R := by
    rw [hR]; ext x
    simp only [mem_filter, mem_range, mem_Ico]
    constructor
    · rintro ⟨⟨h1,h2⟩, hnd⟩
      refine ⟨?_, hnd⟩
      rcases lt_or_eq_of_le (Nat.lt_succ_iff.mp h2) with h|h
      · exact h
      · subst h; exact absurd (dvd_mul_right p j) hnd
    · rintro ⟨h1, hnd⟩
      have hx0 : x ≠ 0 := by rintro rfl; exact hnd (dvd_zero p)
      exact ⟨⟨by omega, by omega⟩, hnd⟩
  -- (F)
  have hcard : (Ico 1 (j+1)).card = j := by rw [Nat.card_Ico]; omega
  have hF : (Nat.factorial (p*j)) = p^j * (Nat.factorial j) * ∏ s ∈ R, s := by
    have h := prod_split_Ico p j hp (fun v => v)
    simp only at h
    rw [Finset.prod_Ico_id_eq_factorial, hFG_set] at h
    have h2 : ∏ t ∈ Ico 1 (j+1), (p*t) = p^j * (Nat.factorial j) := by
      rw [Finset.prod_mul_distrib, Finset.prod_const, hcard, Finset.prod_Ico_id_eq_factorial]
    rw [h2] at h
    rw [h]
  -- (G)
  have hG : (p^r).ascFactorial (p*j) = p^j * (p^(r-1)).ascFactorial j * ∏ s ∈ R, (p^r + s) := by
    rw [Nat.ascFactorial_eq_prod_range, prod_split_range p j hp (fun i => p^r + i)]
    have hcongr : ∀ t ∈ range j, p^r + p*t = p * (p^(r-1)+t) := fun t _ => by rw [heq]; ring
    have h3 : ∏ t ∈ range j, (p^r + p*t) = p^j * (p^(r-1)).ascFactorial j := by
      rw [Finset.prod_congr rfl hcongr, Finset.prod_mul_distrib, Finset.prod_const,
          Finset.card_range, Nat.ascFactorial_eq_prod_range]
    rw [h3]
  -- assemble
  have hmc1 : (p^r).ascFactorial (p*j) = (Nat.factorial (p*j)) * Nat.multichoose (p^r) (p*j) := by
    rw [Nat.multichoose_eq, Nat.ascFactorial_eq_factorial_mul_choose']
  have hmc2 : (p^(r-1)).ascFactorial j = (Nat.factorial j) * Nat.multichoose (p^(r-1)) j := by
    rw [Nat.multichoose_eq, Nat.ascFactorial_eq_factorial_mul_choose']
  have hA : 0 < p^j * (Nat.factorial j) := Nat.mul_pos (pow_pos hp j) (Nat.factorial_pos j)
  apply Nat.eq_of_mul_eq_mul_right hA
  calc (Nat.multichoose (p^r) (p*j) * ∏ s ∈ R, s) * (p^j * (Nat.factorial j))
        = Nat.multichoose (p^r) (p*j) * (p^j * (Nat.factorial j) * ∏ s ∈ R, s) := by ring
      _ = Nat.multichoose (p^r) (p*j) * (Nat.factorial (p*j)) := by rw [← hF]
      _ = (p^r).ascFactorial (p*j) := by rw [hmc1]; ring
      _ = p^j * (p^(r-1)).ascFactorial j * ∏ s ∈ R, (p^r+s) := hG
      _ = p^j * ((Nat.factorial j) * Nat.multichoose (p^(r-1)) j) * ∏ s ∈ R, (p^r+s) := by rw [hmc2]
      _ = (Nat.multichoose (p^(r-1)) j * ∏ s ∈ R, (p^r+s)) * (p^j * (Nat.factorial j)) := by ring

-- absorption identity: k · multichoose(p^r,k) = p^r · C(p^r+k-1, k-1)
lemma mc_absorption (r k : ℕ) (hk : 1 ≤ k) :
    k * (Nat.multichoose (p^r) k) = p^r * (p^r + k - 1).choose (k-1) := by
  rw [Nat.multichoose_eq]
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k-1, by omega⟩
  have h := Nat.choose_succ_right_eq (p^r + j) j
  rw [show p^r + (j+1) - 1 = p^r + j by omega, show (j+1)-1 = j by omega,
      show p^r + j - j = p^r by omega] at *
  rw [mul_comm (j+1), mul_comm (p^r)]; exact h

-- g_k := C(p^r+k-1, k-1) satisfies g_1 = 1 and the recurrence k·g_{k+1} = (p^r+k)·g_k
lemma g_rec (r k : ℕ) (hk : 1 ≤ k) :
    k * ((p^r + (k+1) - 1).choose ((k+1)-1)) = (p^r + k) * ((p^r + k - 1).choose (k-1)) := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k-1, by omega⟩
  rw [show p^r + (j+1+1) - 1 = (p^r+j) + 1 by omega, show (j+1+1)-1 = j+1 by omega,
      show p^r + (j+1) - 1 = (p^r+j) by omega, show (j+1)-1 = j by omega]
  -- use Pascal: C(p^r+j+1, j+1) = C(p^r+j, j) + C(p^r+j, j+1)
  rw [show p^r + j + 1 = (p^r+j)+1 by ring, Nat.choose_succ_succ' (p^r+j) j]
  have hpascal : ((p^r+j)).choose (j+1) * (j+1) = (p^r+j).choose j * (p^r + j - j) :=
    Nat.choose_succ_right_eq (p^r+j) j
  rw [show p^r + j - j = p^r by omega] at hpascal
  set A := (p^r+j).choose j
  set B := (p^r+j).choose (j+1)
  rw [Nat.mul_add, mul_comm (j+1) B, hpascal]
  ring

-- hockey stick: g_k = C(p^r+k-1,k-1) = ∑_{i<k} multichoose(p^r,i)
lemma g_hockey (r k : ℕ) (hk : 1 ≤ k) :
    (p^r + k - 1).choose (k-1) = ∑ i ∈ Finset.range k, Nat.multichoose (p^r) i := by
  have h := Nat.sum_range_multichoose (k-1) (p^r)
  rw [show k - 1 + 1 = k by omega] at h
  rw [h, show k - 1 + p^r = p^r + k - 1 by omega, show k - 1 = (p^r + k - 1) - p^r by omega]
  exact Nat.choose_symm (by omega)

-- ZMod-level: for p∤k, multichoose(p^r,k) = k⁻¹ · p^r · g_k  (g_k = C(p^r+k-1,k-1))
lemma mc_zmod (K r k : ℕ) [hp : Fact p.Prime] (hK : 0 < K) (hk : 1 ≤ k) (hnd : ¬ p ∣ k) :
    ((Nat.multichoose (p^r) k : ℕ) : ZMod (p^K))
      = ((k : ZMod (p^K)))⁻¹ * (p^r : ℕ) * (((p^r + k - 1).choose (k-1) : ℕ)) := by
  haveI : NeZero (p^K) := ⟨(pow_pos hp.out.pos K).ne'⟩
  have hku : IsUnit ((k : ZMod (p^K))) := by
    rw [ZMod.isUnit_iff_coprime]
    exact (Nat.Coprime.pow_right K ((hp.out.coprime_iff_not_dvd.mpr hnd).symm))
  have hcast : ((k : ZMod (p^K))) * ((Nat.multichoose (p^r) k : ℕ) : ZMod (p^K))
      = (p^r : ℕ) * (((p^r + k - 1).choose (k-1) : ℕ)) := by
    have := mc_absorption (p := p) r k hk
    calc ((k : ZMod (p^K))) * ((Nat.multichoose (p^r) k : ℕ) : ZMod (p^K))
        = ((k * (Nat.multichoose (p^r) k) : ℕ) : ZMod (p^K)) := by push_cast; ring
      _ = ((p^r * ((p^r + k - 1).choose (k-1)) : ℕ) : ZMod (p^K)) := by rw [this]
      _ = (p^r : ℕ) * (((p^r + k - 1).choose (k-1) : ℕ)) := by push_cast; ring
  have hinv := ZMod.inv_mul_of_unit _ hku
  calc ((Nat.multichoose (p^r) k : ℕ) : ZMod (p^K))
      = ((k : ZMod (p^K)))⁻¹ * (((k : ZMod (p^K))) * ((Nat.multichoose (p^r) k : ℕ) : ZMod (p^K))) := by
        rw [← mul_assoc, hinv, one_mul]
    _ = ((k : ZMod (p^K)))⁻¹ * ((p^r : ℕ) * (((p^r + k - 1).choose (k-1) : ℕ))) := by rw [hcast]
    _ = ((k : ZMod (p^K)))⁻¹ * (p^r : ℕ) * (((p^r + k - 1).choose (k-1) : ℕ)) := by ring

lemma pv_add_pow (r i : ℕ) [hp : Fact p.Prime] (hi1 : 1 ≤ i) (hi2 : i < p^r) :
    padicValNat p (p^r + i) = padicValNat p i := by
  have hipos : i ≠ 0 := by omega
  have hsum : (p^r + i) ≠ 0 := by positivity
  set v := padicValNat p i with hv
  have hvr : v < r := by
    by_contra h; push_neg at h
    exact absurd (Nat.le_of_dvd (by omega) ((pow_dvd_pow p h).trans pow_padicValNat_dvd)) (by omega)
  have hle : v ≤ padicValNat p (p^r + i) := by
    rw [← padicValNat_dvd_iff_le hsum]
    exact Nat.dvd_add ((pow_dvd_pow p hvr.le)) pow_padicValNat_dvd
  have hlt : padicValNat p (p^r + i) < v + 1 := by
    rw [← not_le, ← padicValNat_dvd_iff_le hsum]
    intro hcon
    have h1 : p ^ (v+1) ∣ p^r := pow_dvd_pow p hvr
    have hdi : p ^ (v+1) ∣ i := (Nat.dvd_add_right h1).mp hcon
    exact (pow_succ_padicValNat_not_dvd hipos) hdi
  omega

-- Full valuation formula for multichoose
lemma pv_multichoose (r : ℕ) [hp : Fact p.Prime] :
    ∀ k, 1 ≤ k → k < p^r → padicValNat p ((p^r).multichoose k) = r - padicValNat p k := by
  have hp1 : 1 < p := hp.out.one_lt
  intro k
  induction k with
  | zero => intro h; omega
  | succ n IH =>
    intro _ hlt
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn; simp [Nat.multichoose_one_right, padicValNat.one]
    · have hprpos : 1 ≤ p^r := Nat.one_le_pow _ _ hp.out.pos
      have mcne : ∀ j, (p^r).multichoose j ≠ 0 := by
        intro j; rw [Nat.multichoose_eq]; exact (Nat.choose_pos (by omega)).ne'
      have hrec : (n+1) * (p^r).multichoose (n+1) = (p^r + n) * (p^r).multichoose n := by
        rw [Nat.multichoose_eq, Nat.multichoose_eq,
            show p^r + (n+1) - 1 = p^r + n by omega]
        have hkey := Nat.add_one_mul_choose_eq (p^r + n - 1) n
        rw [show p^r + n - 1 + 1 = p^r + n by omega] at hkey
        rw [mul_comm (n+1), show p^r + n - 1 = p^r + n - 1 from rfl]
        -- hkey : (p^r+n-1+1) * C(p^r+n-1,n) = C(p^r+n, n+1) * (n+1)
        rw [← hkey]
      -- take padicValNat of both sides
      have h1 : padicValNat p ((n+1) * (p^r).multichoose (n+1))
              = padicValNat p ((p^r + n) * (p^r).multichoose n) := by rw [hrec]
      rw [padicValNat.mul (by omega) (mcne _), padicValNat.mul (by omega) (mcne _),
          pv_add_pow r n hn (by omega), IH hn (by omega)] at h1
      have hle : padicValNat p n ≤ r := by
        by_contra h; push_neg at h
        exact absurd (Nat.le_of_dvd (by omega) ((pow_dvd_pow p h.le).trans pow_padicValNat_dvd)) (by omega)
      omega

-- g_k ≡ 1 mod p  (each multichoose(p^r,i), 1≤i<p^r, is divisible by p)
lemma mc_dvd_p (r i : ℕ) [hp : Fact p.Prime] (hi1 : 1 ≤ i) (hi2 : i < p^r) :
    p ∣ Nat.multichoose (p^r) i := by
  have hv : padicValNat p (Nat.multichoose (p^r) i) = r - padicValNat p i :=
    pv_multichoose r i hi1 hi2
  have hvi : padicValNat p i < r := by
    by_contra h; push_neg at h
    exact absurd (Nat.le_of_dvd (by omega)
      ((pow_dvd_pow p h).trans pow_padicValNat_dvd)) (by omega)
  have hpos : 1 ≤ padicValNat p (Nat.multichoose (p^r) i) := by omega
  have h1 : p ∣ p ^ (padicValNat p (Nat.multichoose (p^r) i)) := by
    simpa using pow_dvd_pow p hpos
  exact h1.trans pow_padicValNat_dvd

-- p^e ≡ 0 in ZMod (p^K) when K ≤ e
lemma p_pow_zero_zmod (K e : ℕ) [hp : Fact p.Prime] (hKe : K ≤ e) :
    ((p : ZMod (p^K)))^e = 0 := by
  haveI : NeZero (p^K) := ⟨(pow_pos hp.out.pos K).ne'⟩
  rw [← Nat.cast_pow, ZMod.natCast_eq_zero_iff]
  exact pow_dvd_pow p hKe

-- factor p^{r(2m+1)} out of the S1 sum in ZMod (p^K)
lemma S1_factor (K r m : ℕ) [hp : Fact p.Prime] (hK : 0 < K) :
    (∑ k ∈ (range (p^r)).filter (fun k => ¬ p ∣ k),
        ((Nat.multichoose (p^r) k ^ (2*m+1) : ℕ) : ZMod (p^K)))
      = ((p : ZMod (p^K)))^(r*(2*m+1)) *
        ∑ k ∈ (range (p^r)).filter (fun k => ¬ p ∣ k),
          (((k : ZMod (p^K)))⁻¹ * (((p^r + k - 1).choose (k-1) : ℕ)))^(2*m+1) := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  rw [mem_filter, mem_range] at hk
  have hnd := hk.2
  have hk1 : 1 ≤ k := by
    rcases Nat.eq_zero_or_pos k with h|h
    · exact absurd (h ▸ dvd_zero p) hnd
    · exact h
  push_cast
  rw [mc_zmod K r k hK hk1 hnd]
  rw [show ((p:ZMod (p^K)))^(r*(2*m+1)) = (((p:ZMod (p^K)))^r)^(2*m+1) from by rw [pow_mul]]
  push_cast
  ring

-- S1 vanishes in ZMod (p^K) whenever K ≤ r(2m+1)  (covers m≥3 and m=2,r≥3)
lemma S1_easy (K r m : ℕ) [hp : Fact p.Prime] (hK : 0 < K) (hKle : K ≤ r*(2*m+1)) :
    (∑ k ∈ (range (p^r)).filter (fun k => ¬ p ∣ k),
        ((Nat.multichoose (p^r) k ^ (2*m+1) : ℕ) : ZMod (p^K))) = 0 := by
  rw [S1_factor K r m hK, p_pow_zero_zmod K (r*(2*m+1)) hKle, zero_mul]

-- bridge: (s : ZMod p^K) = 0 gives (p^K:ℤ) ∣ (s:ℤ)
lemma dvd_of_natCast_zmod_zero (K : ℕ) [hp : Fact p.Prime] (s : ℕ)
    (h : ((s : ℕ) : ZMod (p^K)) = 0) : (p^K : ℤ) ∣ (s : ℤ) := by
  haveI : NeZero (p^K) := ⟨(pow_pos hp.out.pos K).ne'⟩
  rw [ZMod.natCast_eq_zero_iff] at h
  have := Int.natCast_dvd_natCast.mpr h
  rwa [Nat.cast_pow] at this

-- hS1 in the exact ℤ form, for the e≤0 cases (K ≤ r(2m+1))
lemma hS1_easy (K r m : ℕ) [hp : Fact p.Prime] (hK : 0 < K) (hKle : K ≤ r*(2*m+1)) :
    (p^K : ℤ) ∣ ∑ k ∈ (range (p^r)).filter (fun k => ¬ p ∣ k),
        (Nat.multichoose (p^r) k ^ (2*m+1) : ℤ) := by
  have hcast : (∑ k ∈ (range (p^r)).filter (fun k => ¬ p ∣ k),
        (Nat.multichoose (p^r) k ^ (2*m+1) : ℤ))
      = ((∑ k ∈ (range (p^r)).filter (fun k => ¬ p ∣ k),
          Nat.multichoose (p^r) k ^ (2*m+1) : ℕ) : ℤ) := by
    push_cast; ring
  rw [hcast]
  apply dvd_of_natCast_zmod_zero K
  rw [Nat.cast_sum]
  exact S1_easy K r m hK hKle

lemma g_one_mod_p (r k : ℕ) [hp : Fact p.Prime] (hk : 1 ≤ k) (hkr : k ≤ p^r) :
    (((p^r + k - 1).choose (k-1) : ℕ) : ZMod p) = 1 := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k-1, by omega⟩
  rw [g_hockey r (j+1) hk]
  push_cast
  rw [Finset.sum_range_succ']
  haveI : NeZero p := ⟨hp.out.pos.ne'⟩
  have hz : ∀ i ∈ Finset.range j, ((Nat.multichoose (p^r) (i+1) : ℕ) : ZMod p) = 0 := by
    intro i hi
    rw [Finset.mem_range] at hi
    exact (ZMod.natCast_eq_zero_iff _ p).mpr (mc_dvd_p r (i+1) (by omega) (by omega))
  rw [Finset.sum_congr rfl hz, Finset.sum_const_zero, zero_add, Nat.multichoose_zero_right]
  simp
