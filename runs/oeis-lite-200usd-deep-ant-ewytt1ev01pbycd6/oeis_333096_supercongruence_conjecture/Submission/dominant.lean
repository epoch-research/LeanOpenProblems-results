import Submission.structA
import Submission.gk
import Submission.lemmaA

open PowerSeries Finset

/-- p-adic cancellation: if `p^v ∣ X` exactly and `p^(v+k) ∣ X*Y`, then `p^k ∣ Y`. -/
lemma pcancel (p : ℕ) (hp : p.Prime) (v k : ℕ) (X Y : ℤ)
    (hdvd : (p:ℤ)^v ∣ X) (hnd : ¬ ((p:ℤ)^(v+1) ∣ X)) (hXY : (p:ℤ)^(v+k) ∣ X*Y) :
    (p:ℤ)^k ∣ Y := by
  have hpint : Prime (p:ℤ) := Nat.prime_iff_prime_int.mp hp
  obtain ⟨X', hX'⟩ := hdvd
  have hnpX' : ¬ ((p:ℤ) ∣ X') := by
    intro h
    obtain ⟨t, ht⟩ := h
    apply hnd
    exact ⟨t, by rw [hX', ht, pow_succ]; ring⟩
  have hpv0 : ((p:ℤ)^v) ≠ 0 := pow_ne_zero v (by exact_mod_cast hp.ne_zero)
  rw [hX', mul_assoc, pow_add, mul_dvd_mul_iff_left hpv0] at hXY
  exact hpint.pow_dvd_of_dvd_mul_left k hnpX' hXY

/-- Abel/summation-by-parts identity for finite sums, with vanishing boundary. -/
lemma abel_id (N : ℕ) (g c : ℕ → ℤ) (hg0 : g 0 = 0) (hgN : g N = 0) :
    ∑ i ∈ Finset.range (N+1), (g (i-1) - g i) * c i
      = ∑ i ∈ Finset.range (N+1), g i * (c (i+1) - c i) := by
  have key : (∑ i ∈ Finset.range (N+1), (g (i-1) - g i) * c i)
           - (∑ i ∈ Finset.range (N+1), g i * (c (i+1) - c i))
           = g 0 * c 0 - g N * c (N+1) := by
    have e1 : ∑ i ∈ Finset.range (N+1), (g (i-1) - g i) * c i
            = (∑ i ∈ Finset.range (N+1), g (i-1) * c i)
                - ∑ i ∈ Finset.range (N+1), g i * c i := by
      rw [← Finset.sum_sub_distrib]; apply Finset.sum_congr rfl; intro i _; ring
    have e2 : ∑ i ∈ Finset.range (N+1), g i * (c (i+1) - c i)
            = (∑ i ∈ Finset.range (N+1), g i * c (i+1))
                - ∑ i ∈ Finset.range (N+1), g i * c i := by
      rw [← Finset.sum_sub_distrib]; apply Finset.sum_congr rfl; intro i _; ring
    have e3 : ∑ i ∈ Finset.range (N+1), g (i-1) * c i
            = g 0 * c 0 + ∑ i ∈ Finset.range N, g i * c (i+1) := by
      rw [Finset.sum_range_succ']
      simp only [Nat.add_sub_cancel, Nat.zero_sub]
      ring
    have e4 : ∑ i ∈ Finset.range (N+1), g i * c (i+1)
            = (∑ i ∈ Finset.range N, g i * c (i+1)) + g N * c (N+1) := by
      rw [Finset.sum_range_succ]
    rw [e1, e2, e3, e4]; ring
  have : (∑ i ∈ Finset.range (N+1), (g (i-1) - g i) * c i)
           - (∑ i ∈ Finset.range (N+1), g i * (c (i+1) - c i)) = 0 := by
    rw [key, hg0, hgN]; ring
  linarith

/-- Prefix reflection identity for an antipalindromic sequence with zero total sum. -/
lemma prefix_reflect (W : ℕ → ℤ) (w : ℕ) (hanti : ∀ k, W (w - k) = - W k)
    (i : ℕ) (hi : i < w) :
    ∑ k ∈ Finset.range (i+1), W k = ∑ k ∈ Finset.range (w-i), W k := by
  have htot : ∑ k ∈ Finset.range (w+1), W k = 0 := by
    have hrefl := Finset.sum_range_reflect (fun k => W k) (w+1)
    simp only [Nat.add_sub_cancel] at hrefl
    have hneg : ∑ k ∈ Finset.range (w+1), W (w - k) = - ∑ k ∈ Finset.range (w+1), W k := by
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro k _; exact hanti k
    rw [hneg] at hrefl
    linarith
  have hC : ∑ m ∈ Finset.Ico (i + 1) (w + 1), W m
          = ∑ k ∈ Finset.range (w - i), W (i + 1 + k) := by
    rw [Finset.sum_Ico_eq_sum_range, show (w + 1) - (i + 1) = w - i from by omega]
  have hD : (∑ k ∈ Finset.range (i + 1), W k)
              + (∑ m ∈ Finset.Ico (i + 1) (w + 1), W m) = 0 := by
    rw [Finset.sum_range_add_sum_Ico (fun k => W k) (show i + 1 ≤ w + 1 from by omega)]
    exact htot
  have hB : ∑ k ∈ Finset.range (w - i), W (w - i - 1 - k)
          = - ∑ k ∈ Finset.range (w - i), W (i + 1 + k) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro k hk
    rw [Finset.mem_range] at hk
    have hidx : w - (i + 1 + k) = w - i - 1 - k := by omega
    have hh := hanti (i + 1 + k)
    rw [hidx] at hh
    linarith
  have hA := Finset.sum_range_reflect (fun k => W k) (w - i)
  calc ∑ k ∈ Finset.range (i + 1), W k
      = - ∑ m ∈ Finset.Ico (i + 1) (w + 1), W m := by linarith [hD]
    _ = - ∑ k ∈ Finset.range (w - i), W (i + 1 + k) := by rw [hC]
    _ = ∑ k ∈ Finset.range (w - i), W (w - i - 1 - k) := hB.symm
    _ = ∑ k ∈ Finset.range (w - i), W k := hA

/-- Summed descent identity (local copy; depends only on `descKey`). -/
lemma descent_sum (s : ℤ) (n : ℕ) (c : ℕ → ℤ) (hsupp : ∀ i, n ≤ i → c i = 0) :
    s * (∑ i ∈ range (n + 1), c i *
          (Ring.choose (s - 1) (n - i - 1) - Ring.choose (s - 1) (n - i)))
      = ∑ i ∈ range (n + 1), (2 * ((n : ℤ) - (i : ℤ)) - s) * c i * Ring.choose s (n - i) := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.mem_range] at hi
  rcases lt_or_eq_of_le (Nat.lt_succ_iff.mp hi) with hlt | heq
  · have hk : n - i - 1 + 1 = n - i := by omega
    have hcast : ((n - i : ℕ) : ℤ) = (n : ℤ) - (i : ℤ) := by
      rw [Nat.cast_sub (le_of_lt hlt)]
    have hdk := descKey s (n - i - 1)
    rw [hk] at hdk
    have hcast2 : ((n - i - 1 : ℕ) : ℤ) + 1 = (n : ℤ) - (i : ℤ) := by
      have : ((n - i - 1 : ℕ) : ℤ) + 1 = ((n - i : ℕ) : ℤ) := by
        rw [← hk]; push_cast; ring
      rw [this, hcast]
    calc s * (c i * (Ring.choose (s - 1) (n - i - 1) - Ring.choose (s - 1) (n - i)))
        = c i * (s * (Ring.choose (s - 1) (n - i - 1) - Ring.choose (s - 1) (n - i))) := by ring
      _ = c i * ((2 * (((n - i - 1 : ℕ) : ℤ) + 1) - s) * Ring.choose s (n - i)) := by rw [hdk]
      _ = (2 * ((n : ℤ) - (i : ℤ)) - s) * c i * Ring.choose s (n - i) := by rw [hcast2]; ring
  · subst heq
    rw [hsupp i (le_refl i)]; ring

/-- The descent integral form. -/
noncomputable def Lint (A : ℤ) (M : ℕ) (V : ℕ → ℤ) (w : ℕ) : ℤ :=
  ∑ i ∈ Finset.range (M+1), V i *
    (Ring.choose (A*(M:ℤ) - (w:ℤ) - 1) (M-i-1) - Ring.choose (A*(M:ℤ) - (w:ℤ) - 1) (M-i))

/-- Antipalindromic first-moment sequence. -/
noncomputable def Wtil (w : ℕ) (V : ℕ → ℤ) (i : ℕ) : ℤ := ((w:ℤ) - 2*(i:ℤ)) * V i

/-- Negative partial sums of `Wtil` (the "next level" palindromic sequence). -/
noncomputable def Vpr (w : ℕ) (V : ℕ → ℤ) (i : ℕ) : ℤ :=
  - ∑ k ∈ Finset.range (i+1), Wtil w V k

/-- **Descent divisibility (key induction).** -/
lemma DESC (p : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) (A : ℤ) (M : ℕ) (hM : 0 < M) :
    ∀ w : ℕ, ∀ V : ℕ → ℤ,
      (∀ i, V i = V (w - i)) →
      (∀ i, w < i → V i = 0) →
      (∃ t₀, 1 ≤ t₀ ∧ ∀ i, i < t₀ → V i = 0) →
      w < p ^ (padicValNat p M) →
      (p:ℤ)^(2 * padicValNat p M)
        ∣ (p:ℤ)^(padicValNat p w.factorial + padicValNat p (w-1).factorial) * Lint A M V w := by
  haveI : Fact p.Prime := ⟨hp⟩
  intro w
  induction w using Nat.strong_induction_on with
  | _ w IH =>
    intro V hpal hsU hsL hsm
    obtain ⟨t₀, ht₀1, ht₀L⟩ := hsL
    set E := padicValNat p M with hEdef
    have hpEM : p ^ E ∣ M := pow_padicValNat_dvd
    have hpEMle : p ^ E ≤ M := Nat.le_of_dvd hM hpEM
    have hwM : w < M := lt_of_lt_of_le hsm hpEMle
    by_cases hbase : w < 2 * t₀
    · -- base: V ≡ 0
      have hV0all : ∀ i, V i = 0 := by
        intro i
        by_cases hi : i < t₀
        · exact ht₀L i hi
        · by_cases hiw : w < i
          · exact hsU i hiw
          · have : V (w - i) = 0 := ht₀L (w - i) (by omega)
            rw [hpal i]; exact this
      have hLint0 : Lint A M V w = 0 := by
        unfold Lint; apply Finset.sum_eq_zero; intro i _; rw [hV0all i, zero_mul]
      rw [hLint0, mul_zero]; exact dvd_zero _
    · -- inductive step
      push_neg at hbase
      have hw2 : 2 ≤ w := by omega
      have hwpos : 0 < w := by omega
      have hV0 : V 0 = 0 := ht₀L 0 (by omega)
      have hVw : V w = 0 := by rw [hpal w, Nat.sub_self]; exact hV0
      -- antipalindromy of Wtil
      have hWanti : ∀ i, Wtil w V (w - i) = - Wtil w V i := by
        intro i
        by_cases hiw : i ≤ w
        · have hVeq : V (w - i) = V i := by
            have h := hpal (w - i); rw [show w - (w - i) = i from by omega] at h; rw [h]
          simp only [Wtil]; rw [hVeq, Nat.cast_sub hiw]; ring
        · push_neg at hiw
          have hVi : V i = 0 := hsU i hiw
          have hz : w - i = 0 := by omega
          simp only [Wtil, hz, hVi, hV0, Nat.cast_zero]; ring
      -- (X-1)·Vpr = Wtil (Nat-subtraction convention)
      have hrel : ∀ i, Wtil w V i = Vpr w V (i-1) - Vpr w V i := by
        intro i
        rcases Nat.eq_zero_or_pos i with hi0 | hipos
        · subst hi0
          have h0 : Wtil w V 0 = 0 := by simp only [Wtil]; rw [hV0]; ring
          simp only [Nat.zero_sub]; rw [h0]; ring
        · simp only [Vpr]
          rw [show i - 1 + 1 = i from by omega, Finset.sum_range_succ]; ring
      -- total sum of Wtil is zero
      have hWtot : ∑ k ∈ Finset.range (w+1), Wtil w V k = 0 := by
        have hrefl := Finset.sum_range_reflect (fun k => Wtil w V k) (w+1)
        simp only [Nat.add_sub_cancel] at hrefl
        have hneg : ∑ k ∈ Finset.range (w+1), Wtil w V (w - k)
            = - ∑ k ∈ Finset.range (w+1), Wtil w V k := by
          rw [← Finset.sum_neg_distrib]; apply Finset.sum_congr rfl; intro k _; exact hWanti k
        rw [hneg] at hrefl; linarith
      -- Vpr support (lower)
      have hVprL : ∀ i, i < t₀ → Vpr w V i = 0 := by
        intro i hi
        simp only [Vpr]
        have hz : ∀ k ∈ Finset.range (i+1), Wtil w V k = 0 := by
          intro k hk; rw [Finset.mem_range] at hk
          simp only [Wtil]; rw [ht₀L k (by omega), mul_zero]
        rw [Finset.sum_eq_zero hz]; ring
      -- Vpr support (upper)
      have hVprU : ∀ i, w - 1 < i → Vpr w V i = 0 := by
        intro i hi
        simp only [Vpr]
        have heq : ∑ k ∈ Finset.range (i+1), Wtil w V k
            = ∑ k ∈ Finset.range (w+1), Wtil w V k := by
          symm; apply Finset.sum_subset
          · intro x hx; rw [Finset.mem_range] at hx ⊢; omega
          · intro x hx hxns; rw [Finset.mem_range] at hx hxns
            simp only [Wtil]; rw [hsU x (by omega), mul_zero]
        rw [heq, hWtot]; ring
      have hVpr0 : Vpr w V 0 = 0 := hVprL 0 (by omega)
      have hVprM : Vpr w V M = 0 := hVprU M (by omega)
      -- Vpr palindromy about (w-1)/2
      have hVprpal : ∀ i, Vpr w V i = Vpr w V ((w-1) - i) := by
        intro i
        by_cases hi : i < w
        · simp only [Vpr]; congr 1
          rw [show (w - 1 - i) + 1 = w - i from by omega]
          exact prefix_reflect (Wtil w V) w hWanti i hi
        · push_neg at hi
          have h1 : Vpr w V i = 0 := hVprU i (by omega)
          have h2 : Vpr w V ((w-1)-i) = 0 := by
            rw [show w - 1 - i = 0 from by omega]; exact hVprL 0 (by omega)
          rw [h1, h2]
      -- set abbreviations
      set vw := padicValNat p w with hvwdef
      set G := padicValNat p (w-1).factorial with hGdef
      set Fw := padicValNat p w.factorial + padicValNat p (w-1).factorial with hFwdef
      set P1 : ℤ := ∑ i ∈ Finset.range (M+1), V i * Ring.choose (A*(M:ℤ)-(w:ℤ)) (M-i)
        with hPdef
      -- factorial valuation splits
      have hwfact : w.factorial = w * (w-1).factorial := by
        conv_lhs => rw [show w = (w-1)+1 from by omega]
        rw [Nat.factorial_succ, show (w-1)+1 = w from by omega]
      have hval : padicValNat p w.factorial = vw + G := by
        rw [hwfact, padicValNat.mul (by omega) (Nat.factorial_ne_zero _)]
      have hFw2 : Fw = vw + 2*G := by rw [hFwdef, hval]; ring
      -- recursion identity
      have hsupp : ∀ i, M ≤ i → V i = 0 := by intro i hi; exact hsU i (by omega)
      have hrec : (A*(M:ℤ) - (w:ℤ)) * Lint A M V w
          = -((A - 2)*(M:ℤ)) * P1 + Lint A M (Vpr w V) (w - 1) := by
        have hds := descent_sum (A*(M:ℤ) - (w:ℤ)) M V hsupp
        have hL : Lint A M V w
            = ∑ i ∈ Finset.range (M+1), V i *
                (Ring.choose ((A*(M:ℤ)-(w:ℤ)) - 1) (M-i-1) - Ring.choose ((A*(M:ℤ)-(w:ℤ))-1) (M-i)) := rfl
        rw [hL, hds]
        -- split the RHS
        have hsplit : (∑ i ∈ Finset.range (M+1),
              (2*((M:ℤ)-(i:ℤ)) - (A*(M:ℤ)-(w:ℤ))) * V i * Ring.choose (A*(M:ℤ)-(w:ℤ)) (M-i))
            = -((A-2)*(M:ℤ)) * P1
                + ∑ i ∈ Finset.range (M+1), Wtil w V i * Ring.choose (A*(M:ℤ)-(w:ℤ)) (M-i) := by
          rw [hPdef, Finset.mul_sum, ← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl
          intro i _; simp only [Wtil]; ring
        rw [hsplit]
        -- abel: the Wtil-sum becomes next-level Lint
        have habel : (∑ i ∈ Finset.range (M+1), Wtil w V i * Ring.choose (A*(M:ℤ)-(w:ℤ)) (M-i))
            = Lint A M (Vpr w V) (w - 1) := by
          have key := abel_id M (Vpr w V) (fun i => Ring.choose (A*(M:ℤ)-(w:ℤ)) (M-i)) hVpr0 hVprM
          calc ∑ i ∈ Finset.range (M+1), Wtil w V i * Ring.choose (A*(M:ℤ)-(w:ℤ)) (M-i)
              = ∑ i ∈ Finset.range (M+1), (Vpr w V (i-1) - Vpr w V i)
                  * (fun i => Ring.choose (A*(M:ℤ)-(w:ℤ)) (M-i)) i := by
                apply Finset.sum_congr rfl; intro i _; rw [hrel i]
            _ = ∑ i ∈ Finset.range (M+1), Vpr w V i
                  * ((fun i => Ring.choose (A*(M:ℤ)-(w:ℤ)) (M-i)) (i+1)
                      - (fun i => Ring.choose (A*(M:ℤ)-(w:ℤ)) (M-i)) i) := key
            _ = Lint A M (Vpr w V) (w-1) := by
                unfold Lint
                apply Finset.sum_congr rfl
                intro i _
                dsimp only
                have hcast : A*(M:ℤ) - ((w-1 : ℕ):ℤ) - 1 = A*(M:ℤ) - (w:ℤ) := by
                  rw [Nat.cast_sub (by omega : 1 ≤ w)]; push_cast; ring
                rw [hcast, show M - (i+1) = M - i - 1 from by omega]
        rw [habel]
      -- (5) GK sum: p^E ∣ (w-1)! · P1
      have hgk : (p:ℤ)^E ∣ ((w-1).factorial : ℤ) * P1 := by
        rw [hPdef, Finset.mul_sum]
        apply Finset.dvd_sum
        intro i hi; rw [Finset.mem_range] at hi
        by_cases hpos : 0 < i ∧ i < w
        · have hgki := GK p hp A M w i hpos.2 hpos.1
          have hre : ((w-1).factorial:ℤ) * (V i * Ring.choose (A*(M:ℤ)-(w:ℤ)) (M-i))
               = V i * (((w-1).factorial:ℤ) * Ring.choose (A*(M:ℤ)-(w:ℤ)) (M-i)) := by ring
          rw [hre]
          exact Dvd.dvd.mul_left hgki (V i)
        · have hVi0 : V i = 0 := by
            rcases Nat.eq_zero_or_pos i with h0 | h0
            · rw [h0]; exact hV0
            · push_neg at hpos
              have hiw : w ≤ i := hpos h0
              rcases eq_or_lt_of_le hiw with he | hl
              · rw [← he]; exact hVw
              · exact hsU i hl
          rw [hVi0]; simp
      -- exact valuations for cancellations
      have hGdvd : (p:ℤ)^G ∣ ((w-1).factorial : ℤ) := by
        have h : p^G ∣ (w-1).factorial := by rw [hGdef]; exact pow_padicValNat_dvd
        exact_mod_cast h
      have hGnd : ¬ ((p:ℤ)^(G+1) ∣ ((w-1).factorial:ℤ)) := by
        intro hcon
        have h : p^(G+1) ∣ (w-1).factorial := by exact_mod_cast hcon
        rw [hGdef] at h
        exact pow_succ_padicValNat_not_dvd (Nat.factorial_pos _).ne' h
      have hP1div : (p:ℤ)^(E - G) ∣ P1 := by
        rcases le_or_gt G E with hGE | hEG
        · have hh : (p:ℤ)^(G + (E-G)) ∣ ((w-1).factorial:ℤ) * P1 := by
            rw [show G + (E - G) = E from by omega]; exact hgk
          exact pcancel p hp G (E-G) ((w-1).factorial:ℤ) P1 hGdvd hGnd hh
        · rw [show E - G = 0 from by omega, pow_zero]; exact one_dvd _
      have hAM2 : (p:ℤ)^E ∣ (A-2)*(M:ℤ) := by
        have hMint : (p:ℤ)^E ∣ (M:ℤ) := by exact_mod_cast hpEM
        exact hMint.mul_left (A-2)
      -- TermA
      have hTermA : (p:ℤ)^(2*E) ∣ (p:ℤ)^(2*G) * ((A-2)*(M:ℤ)*P1) := by
        have hmul : (p:ℤ)^(E + (E - G)) ∣ (A-2)*(M:ℤ) * P1 := by
          rw [pow_add]; exact mul_dvd_mul hAM2 hP1div
        have hmul2 : (p:ℤ)^(2*G + (E + (E-G))) ∣ (p:ℤ)^(2*G) * ((A-2)*(M:ℤ)*P1) := by
          rw [pow_add]; exact mul_dvd_mul_left _ hmul
        exact dvd_trans (pow_dvd_pow (p:ℤ) (by omega : 2*E ≤ 2*G + (E + (E-G)))) hmul2
      have hTermA' : (p:ℤ)^(vw + 2*E) ∣ (p:ℤ)^Fw * ((A-2)*(M:ℤ)*P1) := by
        have h1 : (p:ℤ)^Fw * ((A-2)*(M:ℤ)*P1)
            = (p:ℤ)^vw * ((p:ℤ)^(2*G) * ((A-2)*(M:ℤ)*P1)) := by
          rw [hFw2, pow_add, mul_assoc]
        rw [h1, pow_add]
        exact mul_dvd_mul_left _ hTermA
      -- TermB via IH
      have hIH := IH (w-1) (by omega) (Vpr w V) hVprpal hVprU
        ⟨t₀, ht₀1, hVprL⟩ (by omega)
      set Fw1 := padicValNat p (w-1).factorial + padicValNat p (w-1-1).factorial with hFw1def
      have hwfact1 : (w-1).factorial = (w-1) * (w-1-1).factorial := by
        conv_lhs => rw [show w-1 = (w-1-1)+1 from by omega]
        rw [Nat.factorial_succ, show (w-1-1)+1 = w-1 from by omega]
      have hval1 : G = padicValNat p (w-1) + padicValNat p (w-1-1).factorial := by
        rw [hGdef, hwfact1, padicValNat.mul (by omega) (Nat.factorial_ne_zero _)]
      have hle : vw + Fw1 ≤ Fw := by
        rw [hFwdef, hFw1def, ← hGdef]; omega
      have hTermB : (p:ℤ)^(vw + 2*E) ∣ (p:ℤ)^Fw * Lint A M (Vpr w V) (w-1) := by
        have step1 : (p:ℤ)^(vw + 2*E)
            ∣ (p:ℤ)^vw * ((p:ℤ)^Fw1 * Lint A M (Vpr w V) (w-1)) := by
          rw [pow_add]; exact mul_dvd_mul_left _ hIH
        have step2 : (p:ℤ)^vw * ((p:ℤ)^Fw1 * Lint A M (Vpr w V) (w-1))
            = (p:ℤ)^(vw+Fw1) * Lint A M (Vpr w V) (w-1) := by rw [← mul_assoc, ← pow_add]
        rw [step2] at step1
        exact dvd_trans step1 (mul_dvd_mul_right (pow_dvd_pow _ hle) _)
      -- big divisibility
      have hbig : (p:ℤ)^(vw + 2*E)
          ∣ (A*(M:ℤ)-(w:ℤ)) * ((p:ℤ)^Fw * Lint A M V w) := by
        have hEq : (A*(M:ℤ)-(w:ℤ)) * ((p:ℤ)^Fw * Lint A M V w)
            = -((p:ℤ)^Fw * ((A-2)*(M:ℤ) * P1)) + (p:ℤ)^Fw * Lint A M (Vpr w V) (w-1) := by
          have hh : (A*(M:ℤ)-(w:ℤ)) * ((p:ℤ)^Fw * Lint A M V w)
               = (p:ℤ)^Fw * ((A*(M:ℤ)-(w:ℤ)) * Lint A M V w) := by ring
          rw [hh, hrec]; ring
        rw [hEq]; apply dvd_add
        · rw [dvd_neg]; exact hTermA'
        · exact hTermB
      -- valuation of A*M - w is exactly vw
      have hvwE : vw < E := by
        have h1 : p^vw ∣ w := by rw [hvwdef]; exact pow_padicValNat_dvd
        have h2 : p^vw ≤ w := Nat.le_of_dvd hwpos h1
        exact (Nat.pow_lt_pow_iff_right hp.one_lt).mp (lt_of_le_of_lt h2 hsm)
      have hXdvd : (p:ℤ)^vw ∣ (A*(M:ℤ) - (w:ℤ)) := by
        apply dvd_sub
        · have hnat : p^vw ∣ M := dvd_trans (pow_dvd_pow p (le_of_lt hvwE)) hpEM
          have : (p:ℤ)^vw ∣ (M:ℤ) := by exact_mod_cast hnat
          exact this.mul_left A
        · have hnat : p^vw ∣ w := by rw [hvwdef]; exact pow_padicValNat_dvd
          exact_mod_cast hnat
      have hXnd : ¬ ((p:ℤ)^(vw+1) ∣ (A*(M:ℤ) - (w:ℤ))) := by
        intro hcon
        have hAMdvd : (p:ℤ)^(vw+1) ∣ A*(M:ℤ) := by
          have hnat : p^(vw+1) ∣ M := dvd_trans (pow_dvd_pow p (by omega : vw+1 ≤ E)) hpEM
          have : (p:ℤ)^(vw+1) ∣ (M:ℤ) := by exact_mod_cast hnat
          exact this.mul_left A
        have hwdvd : (p:ℤ)^(vw+1) ∣ (w:ℤ) := by
          have hsub := dvd_sub hAMdvd hcon
          rwa [show A*(M:ℤ) - (A*(M:ℤ) - (w:ℤ)) = (w:ℤ) from by ring] at hsub
        have hwnat : p^(vw+1) ∣ w := by exact_mod_cast hwdvd
        rw [hvwdef] at hwnat
        exact pow_succ_padicValNat_not_dvd hwpos.ne' hwnat
      -- cancel p^vw
      exact pcancel p hp vw (2*E) (A*(M:ℤ)-(w:ℤ)) ((p:ℤ)^Fw * Lint A M V w) hXdvd hXnd hbig

/-- **Prop 5 (dominant regime), clean form.** -/
theorem prop5dom (p : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) (A : ℤ) (M : ℕ) (hM : 0 < M) (j : ℕ)
    (hj : 3 ≤ j) (hE : j - 1 < p ^ (padicValNat p M)) :
    (p : ℤ) ^ (2 * padicValNat p M)
      ∣ (p : ℤ) ^ (padicValNat p (j-1).factorial + padicValNat p (j-2).factorial)
          * ℓ (ψ p j) (A * (M : ℤ)) M := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨S, hSpal, hSU, hSL, hSrel⟩ := structA p hp hp5 j hj
  have hpEM : p ^ (padicValNat p M) ∣ M := pow_padicValNat_dvd
  have hjM : j - 1 < M := lt_of_lt_of_le hE (Nat.le_of_dvd hM hpEM)
  have hSM : S M = 0 := hSU M (by omega)
  have hS0 : S 0 = 0 := hSL 0 (Nat.add_pos_left one_pos _)
  have hell : ℓ (ψ p j) (A * (M:ℤ)) M = Lint A M S (j-1) := by
    rw [closed_form_ell p hp.pos A M j]
    have hrefl := Finset.sum_range_reflect
      (fun k => Ring.choose (A*(M:ℤ)-(j:ℤ)) k
        * PowerSeries.coeff (p*(M-k)) (qser p^j*Gser)) (M+1)
    simp only [Nat.add_sub_cancel] at hrefl
    rw [← hrefl]
    have hstep : ∀ k ∈ Finset.range (M+1),
        Ring.choose (A*(M:ℤ)-(j:ℤ)) (M-k) * PowerSeries.coeff (p*(M-(M-k))) (qser p^j*Gser)
        = (S (k-1) - S k) * Ring.choose (A*(M:ℤ)-(j:ℤ)) (M-k) := by
      intro k hk; rw [Finset.mem_range] at hk
      rw [show M-(M-k) = k from by omega, hSrel k]
      by_cases hk0 : k = 0
      · subst hk0; simp [hS0]
      · rw [if_neg hk0]; ring
    rw [Finset.sum_congr rfl hstep]
    calc ∑ k ∈ Finset.range (M+1), (S (k-1) - S k) * Ring.choose (A*(M:ℤ)-(j:ℤ)) (M-k)
        = ∑ k ∈ Finset.range (M+1), (S (k-1) - S k)
            * (fun i => Ring.choose (A*(M:ℤ)-(j:ℤ)) (M-i)) k := by
          apply Finset.sum_congr rfl; intro k _; rfl
      _ = ∑ i ∈ Finset.range (M+1), S i
            * ((fun i => Ring.choose (A*(M:ℤ)-(j:ℤ)) (M-i)) (i+1)
                - (fun i => Ring.choose (A*(M:ℤ)-(j:ℤ)) (M-i)) i) :=
          abel_id M S (fun i => Ring.choose (A*(M:ℤ)-(j:ℤ)) (M-i)) hS0 hSM
      _ = Lint A M S (j-1) := by
          unfold Lint
          apply Finset.sum_congr rfl
          intro i _; dsimp only
          have hcast : A*(M:ℤ) - ((j-1:ℕ):ℤ) - 1 = A*(M:ℤ) - (j:ℤ) := by
            rw [Nat.cast_sub (by omega : 1 ≤ j)]; push_cast; ring
          rw [hcast, show M - (i+1) = M - i - 1 from by omega]
  rw [hell]
  have hdesc := DESC p hp hp5 A M hM (j-1) S hSpal hSU
    ⟨1 + (j-1)/p, Nat.le_add_right 1 _, hSL⟩ hE
  rw [show j - 1 - 1 = j - 2 from by omega] at hdesc
  exact hdesc

#print axioms prop5dom
