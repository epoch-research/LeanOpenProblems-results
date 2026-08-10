import FormalConjectures.Util.ProblemImports

open Finset Nat

private def products (n : ℕ) : Finset ℕ :=
  (Icc 1 n).powerset.image (fun s : Finset ℕ => s.prod id)

lemma mem_products {n m : ℕ} :
    m ∈ products n ↔ ∃ s : Finset ℕ, s ⊆ Icc 1 n ∧ s.prod id = m := by
  simp only [products, mem_image, mem_powerset]

example : (1 : ℕ) ∈ products 5 := by
  rw [mem_products]
  exact ⟨∅, by simp, by simp⟩

-- subset of Icc 1 (n+1) not containing (n+1) is a subset of Icc 1 n
lemma subset_Icc_of_not_mem {n : ℕ} {s : Finset ℕ} (hs : s ⊆ Icc 1 (n+1))
    (hn : (n+1) ∉ s) : s ⊆ Icc 1 n := by
  intro y hy
  have := hs hy
  simp only [mem_Icc] at this ⊢
  refine ⟨this.1, ?_⟩
  rcases lt_or_eq_of_le this.2 with h | h
  · omega
  · exact absurd (h ▸ hy) hn

-- products recursion
lemma products_succ (n : ℕ) :
    products (n + 1) = products n ∪ (products n).image (fun x => (n + 1) * x) := by
  ext N
  simp only [mem_products, mem_union, mem_image]
  constructor
  · rintro ⟨s, hs, rfl⟩
    by_cases hn : (n + 1) ∈ s
    · right
      refine ⟨(s.erase (n+1)).prod id, ⟨s.erase (n+1), ?_, rfl⟩, ?_⟩
      · exact subset_Icc_of_not_mem ((erase_subset _ _).trans hs) (notMem_erase _ _)
      · rw [← Finset.prod_erase_mul _ _ hn]; simp [mul_comm]
    · exact Or.inl ⟨s, subset_Icc_of_not_mem hs hn, rfl⟩
  · rintro (⟨s, hs, rfl⟩ | ⟨M, ⟨s, hs, rfl⟩, rfl⟩)
    · exact ⟨s, hs.trans (Finset.Icc_subset_Icc_right (by omega)), rfl⟩
    · have hns : (n+1) ∉ s := fun h => by have := hs h; simp only [mem_Icc] at this; omega
      refine ⟨insert (n+1) s, ?_, ?_⟩
      · rw [insert_subset_iff]
        exact ⟨by simp, hs.trans (Finset.Icc_subset_Icc_right (by omega))⟩
      · rw [Finset.prod_insert hns]; simp

lemma prod_Icc_id (n : ℕ) : (Icc 1 n).prod id = n.factorial := by
  simp only [id]
  induction n with
  | zero => simp
  | succ k ih => rw [Finset.prod_Icc_succ_top (by omega), ih, Nat.factorial_succ]; ring

-- every product is at most n!
lemma products_le_factorial {n N : ℕ} (h : N ∈ products n) : N ≤ n.factorial := by
  rw [mem_products] at h
  obtain ⟨s, hs, rfl⟩ := h
  rw [← prod_Icc_id n]
  apply Finset.prod_le_prod_of_subset_of_one_le' hs
  intro i hi _
  simp only [id]
  exact (mem_Icc.mp hi).1

-- valuation bound: if M0 ≥ 1, p ≥ 2 and M0 p^v ∈ products n then v ≤ n!
lemma val_lt {p n M0 v : ℕ} (hp : 2 ≤ p) (hM0 : 1 ≤ M0)
    (h : M0 * p ^ v ∈ products n) : v < n.factorial + 1 := by
  have h1 : M0 * p ^ v ≤ n.factorial := products_le_factorial h
  have h2 : v < 2 ^ v := Nat.lt_two_pow_self
  have h3 : 2 ^ v ≤ p ^ v := Nat.pow_le_pow_left hp v
  have h4 : p ^ v ≤ M0 * p ^ v := Nat.le_mul_of_pos_left _ hM0
  omega

-- The valuation Finset
def Wf (p n M0 : ℕ) : Finset ℕ :=
  (Finset.range (n.factorial + 1)).filter (fun v => M0 * p ^ v ∈ products n)

lemma mem_Wf {p n M0 v : ℕ} (hp : 2 ≤ p) (hM0 : 1 ≤ M0) :
    v ∈ Wf p n M0 ↔ M0 * p ^ v ∈ products n := by
  simp only [Wf, Finset.mem_filter, Finset.mem_range]
  constructor
  · exact fun h => h.2
  · exact fun h => ⟨val_lt hp hM0 h, h⟩

-- product membership implies X ≥ 1
lemma one_le_of_mem_products {n X : ℕ} (hX : X ∈ products n) : 1 ≤ X := by
  rw [mem_products] at hX
  obtain ⟨s, hs, rfl⟩ := hX
  apply Finset.one_le_prod'
  intro i hi; have := hs hi; simp only [mem_Icc, id] at this ⊢; omega

-- Recursion for products membership. c0, t0 the p-free part and p-valuation of (n+1).
lemma prod_succ_mem {p : ℕ} (hp : p.Prime) (n M0 v : ℕ) (hM0 : 1 ≤ M0) (hpM0 : ¬ p ∣ M0) :
    M0 * p ^ v ∈ products (n+1) ↔ M0 * p ^ v ∈ products n ∨
      (ordCompl[p] (n+1) ∣ M0 ∧ (n+1).factorization p ≤ v ∧
        (M0 / ordCompl[p] (n+1)) * p ^ (v - (n+1).factorization p) ∈ products n) := by
  have hp2 : 2 ≤ p := hp.two_le
  set c0 := ordCompl[p] (n+1) with hc0
  set t0 := (n+1).factorization p with ht0
  have hn1 : (n+1) = c0 * p ^ t0 := by
    rw [hc0, ht0]; exact (Nat.ordProj_mul_ordCompl_eq_self (n+1) p).symm.trans (by ring)
  have hc0pos : 1 ≤ c0 := Nat.ordCompl_pos p (by omega)
  have hcop : ¬ p ∣ c0 := Nat.not_dvd_ordCompl hp (by omega)
  have hcopc0 : Nat.Coprime c0 (p ^ v) := (((hp.coprime_iff_not_dvd).mpr hcop).symm).pow_right _
  rw [products_succ, mem_union, mem_image]
  constructor
  · rintro (h | ⟨X, hX, hXeq⟩)
    · exact Or.inl h
    · right
      have hkey : c0 * p ^ t0 * X = M0 * p ^ v := by rw [← hn1]; exact hXeq
      have hc0dvd : c0 ∣ M0 :=
        hcopc0.dvd_of_dvd_mul_right ⟨p ^ t0 * X, by rw [← hkey]; ring⟩
      obtain ⟨M1, hM0eq⟩ := hc0dvd
      have hM1pos : 1 ≤ M1 := by
        rcases Nat.eq_zero_or_pos M1 with h | h
        · rw [h, mul_zero] at hM0eq; omega
        · exact h
      have hkey2 : c0 * p ^ t0 * X = c0 * M1 * p ^ v := by rw [← hM0eq]; exact hkey
      have hM1 : p ^ t0 * X = M1 * p ^ v :=
        Nat.eq_of_mul_eq_mul_left (show 0 < c0 by omega)
          (by rw [← mul_assoc, ← mul_assoc]; exact hkey2)
      have hpM1 : ¬ p ∣ M1 := fun hd => hpM0 (hM0eq ▸ Dvd.dvd.mul_left hd c0)
      have hcopM1 : Nat.Coprime (p ^ t0) M1 := ((hp.coprime_iff_not_dvd).mpr hpM1).pow_left t0
      have hple : p ^ t0 ∣ p ^ v := hcopM1.dvd_of_dvd_mul_left ⟨X, by rw [← hM1]⟩
      have htv : t0 ≤ v := (Nat.pow_dvd_pow_iff_le_right hp.one_lt).mp hple
      have hXeq2 : X = M1 * p ^ (v - t0) := by
        have hpsplit : p ^ v = p ^ t0 * p ^ (v - t0) := by rw [← pow_add]; congr 1; omega
        have : p ^ t0 * X = p ^ t0 * (M1 * p ^ (v - t0)) := by rw [hM1, hpsplit]; ring
        exact Nat.eq_of_mul_eq_mul_left (by positivity) this
      have hMdiv : M0 / c0 = M1 := by rw [hM0eq]; exact Nat.mul_div_cancel_left M1 (by omega)
      exact ⟨⟨M1, hM0eq⟩, htv, by rw [hMdiv, ← hXeq2]; exact hX⟩
  · rintro (h | ⟨hdvd, htv, hmem⟩)
    · exact Or.inl h
    · right
      obtain ⟨M1, hM0eq⟩ := hdvd
      have hM1pos : 1 ≤ M1 := by
        rcases Nat.eq_zero_or_pos M1 with h | h
        · rw [h, mul_zero] at hM0eq; omega
        · exact h
      have hMdiv : M0 / c0 = M1 := by rw [hM0eq]; exact Nat.mul_div_cancel_left M1 (by omega)
      rw [hMdiv] at hmem
      refine ⟨M1 * p ^ (v - t0), hmem, ?_⟩
      have hps : p ^ t0 * p ^ (v - t0) = p ^ v := by rw [← pow_add]; congr 1; omega
      rw [hM0eq, hn1]
      calc c0 * p ^ t0 * (M1 * p ^ (v - t0))
          = c0 * M1 * (p ^ t0 * p ^ (v - t0)) := by ring
        _ = c0 * M1 * p ^ v := by rw [hps]

-- p does not divide M0/c when p doesn't divide M0
lemma not_dvd_div {p M0 c : ℕ} (hpM0 : ¬ p ∣ M0) (hc : c ∣ M0) : ¬ p ∣ (M0 / c) :=
  fun hd => hpM0 (hd.trans (Nat.div_dvd_of_dvd hc))

-- Finset-level recursion.  For ¬p∣M0, 1≤M0:
--   Wf p (n+1) M0 = Wf p n M0 ∪ (image (·+t0) of Wf p n (M0/c0))  if c0 ∣ M0, else = Wf p n M0
lemma Wf_succ_eq {p : ℕ} (hp : p.Prime) (n M0 : ℕ) (hM0 : 1 ≤ M0) (hpM0 : ¬ p ∣ M0) :
    Wf p (n+1) M0 =
      if ordCompl[p] (n+1) ∣ M0
      then Wf p n M0 ∪ (Wf p n (M0 / ordCompl[p] (n+1))).image (· + (n+1).factorization p)
      else Wf p n M0 := by
  have hp2 := hp.two_le
  set c0 := ordCompl[p] (n+1) with hc0
  set t0 := (n+1).factorization p with ht0
  have hc0pos : 1 ≤ c0 := Nat.ordCompl_pos p (by omega)
  ext v
  rw [mem_Wf hp2 hM0, prod_succ_mem hp n M0 v hM0 hpM0]
  by_cases hdvd : c0 ∣ M0
  · have hM1 : 1 ≤ M0 / c0 := Nat.one_le_div_iff (by omega) |>.mpr (Nat.le_of_dvd (by omega) hdvd)
    simp only [hdvd, if_true, mem_union, mem_image, mem_Wf hp2 hM0, mem_Wf hp2 hM1]
    constructor
    · rintro (h | ⟨_, htv, hmem⟩)
      · exact Or.inl h
      · exact Or.inr ⟨v - t0, hmem, by omega⟩
    · rintro (h | ⟨a, ha, hav⟩)
      · exact Or.inl h
      · exact Or.inr ⟨hdvd, by omega, by rw [show v - t0 = a by omega]; exact ha⟩
  · simp only [hdvd, if_false, mem_Wf hp2 hM0]
    constructor
    · rintro (h | ⟨hd, _, _⟩)
      · exact h
      · exact absurd hd hdvd
    · exact Or.inl

-- Combined invariant: convexity, width, and the two overlap inequalities.
def WInv (p n M0 : ℕ) : Prop :=
  (∀ a b c, a ∈ Wf p n M0 → b ∈ Wf p n M0 → a ≤ c → c ≤ b → c ∈ Wf p n M0) ∧
  (∀ t, p ^ t ≤ n → ∀ h : (Wf p n M0).Nonempty, (Wf p n M0).min' h + t ≤ (Wf p n M0).max' h) ∧
  (∀ c t, ¬ p ∣ c → 2 ≤ c → c ∣ M0 → c * p ^ t ≤ n →
     ∀ (h1 : (Wf p n M0).Nonempty) (h2 : (Wf p n (M0/c)).Nonempty),
        t + (Wf p n (M0/c)).min' h2 ≤ (Wf p n M0).max' h1) ∧
  (∀ c t, ¬ p ∣ c → 2 ≤ c → c ∣ M0 → c * p ^ t ≤ n →
     ∀ (h1 : (Wf p n M0).Nonempty) (h2 : (Wf p n (M0/c)).Nonempty),
        (Wf p n M0).min' h1 ≤ t + (Wf p n (M0/c)).max' h2)

-- image-shift min'/max'
lemma image_add_min' (s : Finset ℕ) (t : ℕ) (h : s.Nonempty) :
    (s.image (· + t)).min' (h.image _) = s.min' h + t := by
  apply le_antisymm
  · exact Finset.min'_le _ _ (Finset.mem_image_of_mem (· + t) (s.min'_mem h))
  · apply Finset.le_min'
    intro y hy
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hy
    exact Nat.add_le_add_right (Finset.min'_le _ _ ha) t

lemma image_add_max' (s : Finset ℕ) (t : ℕ) (h : s.Nonempty) :
    (s.image (· + t)).max' (h.image _) = s.max' h + t := by
  apply le_antisymm
  · apply Finset.max'_le
    intro y hy
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hy
    exact Nat.add_le_add_right (Finset.le_max' _ _ ha) t
  · exact Finset.le_max' _ _ (Finset.mem_image_of_mem (· + t) (s.max'_mem h))

-- membership implies value is a valuation of an element of products
lemma Wf_zero_eq_zero {p M0 v : ℕ} (hp : 2 ≤ p) (hM0 : 1 ≤ M0) (h : v ∈ Wf p 0 M0) : v = 0 := by
  rw [mem_Wf hp hM0] at h
  have hle := products_le_factorial h
  simp only [Nat.factorial_zero] at hle
  have : p ^ v ≤ M0 * p ^ v := Nat.le_mul_of_pos_left _ hM0
  have : p ^ v ≤ 1 := by omega
  by_contra hv
  have : 2 ≤ p ^ v := le_trans hp (Nat.le_self_pow hv p)
  omega

lemma winv {p : ℕ} (hp : p.Prime) :
    ∀ n M0, 1 ≤ M0 → ¬ p ∣ M0 → WInv p n M0 := by
  have hp2 := hp.two_le
  intro n
  induction n with
  | zero =>
    intro M0 hM0 hpM0
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro a b c ha hb hac hcb
      have ea := Wf_zero_eq_zero hp2 hM0 ha
      have eb := Wf_zero_eq_zero hp2 hM0 hb
      have hca : c = a := by omega
      rw [hca]; exact ha
    · intro t ht h
      exfalso; have : 1 ≤ p ^ t := Nat.one_le_pow _ _ (by omega); omega
    · intro c t _ hc _ hct _ _
      exfalso; have : 0 < c * p ^ t := Nat.mul_pos (by omega) (pow_pos (by omega) t); omega
    · intro c t _ hc _ hct _ _
      exfalso; have : 0 < c * p ^ t := Nat.mul_pos (by omega) (pow_pos (by omega) t); omega
  | succ n ih =>
    intro M0 hM0 hpM0
    -- The clean half: when ordCompl[p](n+1) does not divide M0, Wf is unchanged.
    by_cases hdvd : ordCompl[p] (n+1) ∣ M0
    · sorry
    · have heq : Wf p (n+1) M0 = Wf p n M0 := by
        rw [Wf_succ_eq hp n M0 hM0 hpM0, if_neg hdvd]
      -- n+1 is impure so c0 ≥ 2; used to reduce bounds p^t ≤ n+1 to p^t ≤ n
      have hc0 : 2 ≤ ordCompl[p] (n+1) := by
        have h1 : 1 ≤ ordCompl[p] (n+1) := Nat.ordCompl_pos p (by omega)
        rcases Nat.eq_or_lt_of_le h1 with h | h
        · exact absurd (h ▸ one_dvd M0) hdvd
        · omega
      obtain ⟨conv_n, wid_n, invB_n, invA_n⟩ := ih M0 hM0 hpM0
      have hn1 : (n+1 : ℕ) = ordCompl[p] (n+1) * p ^ (n+1).factorization p :=
        (Nat.ordProj_mul_ordCompl_eq_self (n+1) p).symm.trans (by ring)
      have hordpow : ∀ s : ℕ, ordCompl[p] (p ^ s) = 1 := by
        intro s
        rw [Nat.factorization_pow, Finsupp.smul_apply, Nat.Prime.factorization_self hp,
          smul_eq_mul, mul_one, Nat.div_self (by positivity)]
      have hbnd : ∀ t : ℕ, p ^ t ≤ n + 1 → p ^ t ≤ n := by
        intro t ht
        rcases Nat.lt_or_ge (p ^ t) (n+1) with h1 | h1
        · omega
        · exfalso; have he : p ^ t = n + 1 := le_antisymm ht h1
          have : ordCompl[p] (n+1) = 1 := by rw [← he]; exact hordpow t
          omega
      -- key: n+1 impure ⟹ for c∣M0, c*p^t ≤ n+1 reduces to ≤ n (else c would equal c0)
      have hcbnd : ∀ c t : ℕ, ¬ p ∣ c → c ∣ M0 → c * p ^ t ≤ n + 1 → c * p ^ t ≤ n := by
        intro c t hpc hcM ht
        rcases Nat.lt_or_ge (c * p ^ t) (n+1) with h1 | h1
        · omega
        · exfalso
          have he : c * p ^ t = n + 1 := le_antisymm ht h1
          apply hdvd
          have hoc : ordCompl[p] (n + 1) = c := by
            rw [← he, Nat.ordCompl_mul]
            have e1 : ordCompl[p] c = c := by
              rw [Nat.factorization_eq_zero_of_not_dvd hpc]; simp
            rw [e1, hordpow t, mul_one]
          rw [hoc]; exact hcM
      have hc0notdvd : ∀ c : ℕ, c ∣ M0 → ¬ ordCompl[p] (n+1) ∣ (M0 / c) := by
        intro c hcM hcon
        exact hdvd (hcon.trans (Nat.div_dvd_of_dvd hcM))
      have heqc : ∀ c : ℕ, 1 ≤ c → c ∣ M0 → Wf p (n+1) (M0 / c) = Wf p n (M0 / c) := by
        intro c hc1 hcM
        have h0 : 1 ≤ M0 / c := (Nat.one_le_div_iff (by omega)).mpr (Nat.le_of_dvd (by omega) hcM)
        rw [Wf_succ_eq hp n (M0/c) h0 (not_dvd_div hpM0 hcM), if_neg (hc0notdvd c hcM)]
      refine ⟨?_, ?_, ?_, ?_⟩
      · rw [heq]; exact conv_n
      · intro t ht; rw [heq]; exact wid_n t (hbnd t ht)
      · intro c t hpc hc hcM hct; rw [heq, heqc c (by omega) hcM]
        exact invB_n c t hpc hc hcM (hcbnd c t hpc hcM hct)
      · intro c t hpc hc hcM hct; rw [heq, heqc c (by omega) hcM]
        exact invA_n c t hpc hc hcM (hcbnd c t hpc hcM hct)

-- Convexity of the p-adic valuation slice
def Wconv (p n M0 : ℕ) : Prop :=
  ∀ a b c : ℕ, M0 * p ^ a ∈ products n → M0 * p ^ b ∈ products n →
    a ≤ c → c ≤ b → M0 * p ^ c ∈ products n

-- The main conjecture follows from convexity for all M0
theorem conj_of_conv (n : ℕ)
    (H : ∀ p, Nat.Prime p → p ≤ n → ∀ M0, Wconv p n M0) :
    ∀ p, Nat.Prime p → p ≤ n →
    ∀ m a, m ∈ products n → (p ^ a * m) ∈ products n →
    ∀ k, 0 < k → k < a → (p ^ k * m) ∈ products n := by
  intro p hp hpn m a hm hpa k hk hka
  have hm0 : m ≠ 0 := by
    rw [mem_products] at hm
    obtain ⟨s, hsub, hs⟩ := hm
    rw [← hs]
    apply Finset.prod_ne_zero_iff.mpr
    intro x hx
    have : x ∈ Icc 1 n := hsub hx
    simp only [mem_Icc, id] at this ⊢
    omega
  set M0 := ordCompl[p] m with hM0
  set w := m.factorization p with hw
  have hmeq : m = M0 * p ^ w := by
    rw [hM0, hw]; exact (Nat.ordProj_mul_ordCompl_eq_self m p).symm.trans (by ring)
  have e1 : M0 * p ^ w ∈ products n := hmeq ▸ hm
  have e2 : M0 * p ^ (w + a) ∈ products n := by
    have : p ^ a * m = M0 * p ^ (w + a) := by rw [hmeq]; ring
    rwa [this] at hpa
  have e3 : M0 * p ^ (w + k) ∈ products n :=
    H p hp hpn M0 w (w + a) (w + k) e1 e2 (by omega) (by omega)
  have : p ^ k * m = M0 * p ^ (w + k) := by rw [hmeq]; ring
  rwa [this]
