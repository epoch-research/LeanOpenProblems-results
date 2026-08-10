import FormalConjectures.Util.ProblemImports

open Nat Finset

/--
A281009: Number of odd divisors of $n$ minus the number of middle divisors of $n$.
A divisor $d$ of $n$ is a "middle divisor" if $\sqrt{n/2} \le d < \sqrt{2n}$,
which is equivalent to $n \le 2d^2$ and $d^2 < 2n$ for $d \in \mathbb{N}$.
-/
def A281009 (n : ℕ) : ℤ :=
  if h : n = 0 then
    0
  else
    let odd_div_count : ℕ := (divisors n).filter (fun d => d % 2 = 1) |>.card
    let middle_div_condition (d : ℕ) : Prop := n ≤ 2 * d ^ 2 ∧ d ^ 2 < 2 * n
    let middle_div_count : ℕ := (divisors n).filter middle_div_condition |>.card
    (odd_div_count : ℤ) - (middle_div_count : ℤ)

/--
Conjecture 1: a(n) is also twice the number of odd divisors of n greater than sqrt(2*n).
-/
theorem oeis_281009_conjecture_0 (n : ℕ) (hn : n ≠ 0) :
    (A281009 n : ℤ) = 2 * (↑(((divisors n).filter (fun d => d % 2 = 1 ∧ 2 * n < d ^ 2)).card) : ℤ) :=
by
  classical
  set a := n.factorization 2 with ha_def
  set m := ordCompl[2] n with hm_def
  have hn_eq : 2 ^ a * m = n := Nat.ordProj_mul_ordCompl_eq_self n 2
  have hm_pos : 0 < m := Nat.ordCompl_pos 2 hn
  have hm_odd : ¬ (2 ∣ m) := Nat.not_dvd_ordCompl Nat.prime_two hn
  have h2n : 2 * n = 2 ^ (a + 1) * m := by
    rw [← hn_eq]; ring
  -- d odd ∧ d ∣ n → d ∣ m
  have hdvdm : ∀ d : ℕ, d ∣ n → d % 2 = 1 → d ∣ m := by
    intro d hdn hodd
    have hcop2 : Nat.Coprime d 2 := by
      rw [Nat.coprime_two_right]; exact Nat.odd_iff.mpr hodd
    have hcop : Nat.Coprime d (2 ^ a) := hcop2.pow_right a
    have : d ∣ 2 ^ a * m := hn_eq ▸ hdn
    exact hcop.dvd_of_dvd_mul_left this
  -- divisor of m is odd
  have hodd_of_dvd_m : ∀ d : ℕ, d ∣ m → d % 2 = 1 := by
    intro d hd
    rcases Nat.mod_two_eq_zero_or_one d with h | h
    · exact absurd ((Nat.dvd_of_mod_eq_zero h).trans hd) hm_odd
    · exact h
  -- abbreviations
  set Sodd := (n.divisors).filter (fun d => d % 2 = 1) with hSodd
  set Slt := (n.divisors).filter (fun d => d % 2 = 1 ∧ d ^ 2 < 2 * n) with hSlt
  set Sgt := (n.divisors).filter (fun d => d % 2 = 1 ∧ 2 * n < d ^ 2) with hSgt
  set Mid := (n.divisors).filter (fun d => n ≤ 2 * d ^ 2 ∧ d ^ 2 < 2 * n) with hMid
  -- (1) Sodd.card = Slt.card + Sgt.card
  have step1 : Sodd.card = Slt.card + Sgt.card := by
    have hpart := Finset.card_filter_add_card_filter_not (s := Sodd) (fun d => d ^ 2 < 2 * n)
    have e1 : Sodd.filter (fun d => d ^ 2 < 2 * n) = Slt := by
      rw [hSodd, hSlt, Finset.filter_filter]
    have e2 : Sodd.filter (fun d => ¬ (d ^ 2 < 2 * n)) = Sgt := by
      rw [hSodd, hSgt, Finset.filter_filter]
      apply Finset.filter_congr
      intro d hd
      rw [Nat.mem_divisors] at hd
      have hne : ∀ ho : d % 2 = 1, d ^ 2 ≠ 2 * n := by
        intro ho he
        have h1 : d ^ 2 % 2 = 1 := by
          rw [pow_two, Nat.mul_mod, ho]
        rw [he] at h1
        omega
      constructor
      · rintro ⟨ho, hle⟩
        exact ⟨ho, lt_of_le_of_ne (not_lt.mp hle) (fun h => (hne ho) h.symm)⟩
      · rintro ⟨ho, hlt⟩
        exact ⟨ho, not_lt.mpr (le_of_lt hlt)⟩
    rw [e1, e2] at hpart
    omega
  -- helpers
  have hm_dvd_n : m ∣ n := Nat.ordCompl_dvd n 2
  have ordCompl_odd : ∀ x : ℕ, x % 2 = 1 → ordCompl[2] x = x := by
    intro x hx
    have hf : x.factorization 2 = 0 := Nat.factorization_eq_zero_of_not_dvd (by omega)
    rw [show ordCompl[2] x = x / 2 ^ (x.factorization 2) from rfl, hf, pow_zero, Nat.div_one]
  have memSlt : ∀ d, d ∈ Slt ↔ (d ∣ n ∧ d % 2 = 1 ∧ d ^ 2 < 2 * n) := by
    intro d
    rw [hSlt, Finset.mem_filter, Nat.mem_divisors]
    constructor
    · rintro ⟨⟨h1, _⟩, h2, h3⟩; exact ⟨h1, h2, h3⟩
    · rintro ⟨h1, h2, h3⟩; exact ⟨⟨h1, hn⟩, h2, h3⟩
  have memSgt : ∀ d, d ∈ Sgt ↔ (d ∣ n ∧ d % 2 = 1 ∧ 2 * n < d ^ 2) := by
    intro d
    rw [hSgt, Finset.mem_filter, Nat.mem_divisors]
    constructor
    · rintro ⟨⟨h1, _⟩, h2, h3⟩; exact ⟨h1, h2, h3⟩
    · rintro ⟨h1, h2, h3⟩; exact ⟨⟨h1, hn⟩, h2, h3⟩
  have memMid : ∀ d, d ∈ Mid ↔ (d ∣ n ∧ n ≤ 2 * d ^ 2 ∧ d ^ 2 < 2 * n) := by
    intro d
    rw [hMid, Finset.mem_filter, Nat.mem_divisors]
    constructor
    · rintro ⟨⟨h1, _⟩, h2, h3⟩; exact ⟨h1, h2, h3⟩
    · rintro ⟨h1, h2, h3⟩; exact ⟨⟨h1, hn⟩, h2, h3⟩
  -- (2) Slt.card = Mid.card + Sgt.card
  have step2 : Slt.card = Mid.card + Sgt.card := by
    have hsplit := Finset.card_filter_add_card_filter_not (s := Slt)
      (fun d => m ≤ 2 ^ (a + 1) * d ^ 2)
    set A := Slt.filter (fun d => m ≤ 2 ^ (a + 1) * d ^ 2) with hA_def
    set Bneg := Slt.filter (fun d => ¬ (m ≤ 2 ^ (a + 1) * d ^ 2)) with hB_def
    have memA : ∀ d, d ∈ A ↔ (d ∣ n ∧ d % 2 = 1 ∧ d ^ 2 < 2 * n) ∧ m ≤ 2 ^ (a + 1) * d ^ 2 := by
      intro d; rw [hA_def, Finset.mem_filter, memSlt]
    have memB : ∀ d, d ∈ Bneg ↔ (d ∣ n ∧ d % 2 = 1 ∧ d ^ 2 < 2 * n) ∧ 2 ^ (a + 1) * d ^ 2 < m := by
      intro d; rw [hB_def, Finset.mem_filter, memSlt]
      constructor
      · rintro ⟨h1, h2⟩; exact ⟨h1, not_le.mp h2⟩
      · rintro ⟨h1, h2⟩; exact ⟨h1, not_le.mpr h2⟩
    -- Bijection A ↔ Mid
    have hAcard : A.card = Mid.card := by
      symm
      apply Finset.card_bij (fun c _ => ordCompl[2] c)
      · -- maps into A
        intro c hc
        rw [memMid] at hc
        obtain ⟨hcn, hmid1, hmid2⟩ := hc
        have hcpos : 0 < c := Nat.pos_of_dvd_of_pos hcn (Nat.pos_of_ne_zero hn)
        set b := c.factorization 2 with hb_def
        set oc := ordCompl[2] c with hoc_def
        have hco : 2 ^ b * oc = c := Nat.ordProj_mul_ordCompl_eq_self c 2
        have hoc_odd : oc % 2 = 1 := by
          have := Nat.not_dvd_ordCompl Nat.prime_two hcpos.ne'
          omega
        have hoc_dvd : oc ∣ n := (Nat.ordCompl_dvd c 2).trans hcn
        have hoc_le : oc ≤ c := Nat.le_of_dvd hcpos (Nat.ordCompl_dvd c 2)
        have hba : b ≤ a := by
          have hdvd : 2 ^ b ∣ n := (Nat.ordProj_dvd c 2).trans hcn
          exact (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two hn).mp hdvd
        rw [memA]
        refine ⟨⟨hoc_dvd, hoc_odd, ?_⟩, ?_⟩
        · -- oc^2 < 2n
          have : oc ^ 2 ≤ c ^ 2 := Nat.pow_le_pow_left hoc_le 2
          exact lt_of_le_of_lt this hmid2
        · -- m ≤ 2^(a+1)*oc^2
          have hcsq : c ^ 2 = (2 ^ b) ^ 2 * oc ^ 2 := by rw [← hco]; ring
          have key : 2 ^ a * m ≤ 2 ^ a * (2 ^ (a + 1) * oc ^ 2) := by
            calc 2 ^ a * m = n := hn_eq
              _ ≤ 2 * c ^ 2 := hmid1
              _ = 2 * (2 ^ b) ^ 2 * oc ^ 2 := by rw [hcsq]; ring
              _ ≤ 2 * (2 ^ a) ^ 2 * oc ^ 2 := by
                  have hXY : (2 ^ b) ^ 2 ≤ (2 ^ a) ^ 2 :=
                    Nat.pow_le_pow_left (Nat.pow_le_pow_right (by norm_num) hba) 2
                  nlinarith [hXY, Nat.zero_le (oc ^ 2)]
              _ = 2 ^ a * (2 ^ (a + 1) * oc ^ 2) := by rw [pow_succ]; ring
          exact Nat.le_of_mul_le_mul_left key (pow_pos (show (0:ℕ) < 2 by norm_num) a)
      · -- injective
        intro c1 hc1 c2 hc2 heq
        rw [memMid] at hc1 hc2
        obtain ⟨hc1n, hm11, hm12⟩ := hc1
        obtain ⟨hc2n, hm21, hm22⟩ := hc2
        have hc1pos : 0 < c1 := Nat.pos_of_dvd_of_pos hc1n (Nat.pos_of_ne_zero hn)
        have hc2pos : 0 < c2 := Nat.pos_of_dvd_of_pos hc2n (Nat.pos_of_ne_zero hn)
        set oc := ordCompl[2] c1 with hoc1
        have heq2 : ordCompl[2] c2 = oc := heq.symm
        set b1 := c1.factorization 2 with hb1
        set b2 := c2.factorization 2 with hb2
        have hco1 : 2 ^ b1 * oc = c1 := Nat.ordProj_mul_ordCompl_eq_self c1 2
        have hco2 : 2 ^ b2 * oc = c2 := by rw [hb2, ← heq2]; exact Nat.ordProj_mul_ordCompl_eq_self c2 2
        -- show b1 = b2
        have hbeq : b1 = b2 := by
          rcases lt_trichotomy b1 b2 with h | h | h
          · exfalso
            have h2 : 2 * 2 ^ b1 ≤ 2 ^ b2 := by
              rw [← _root_.pow_succ']; exact Nat.pow_le_pow_right (by norm_num) h
            have hc2ge : 2 * c1 ≤ c2 := by
              have e : 2 * c1 = (2 * 2 ^ b1) * oc := by rw [← hco1]; ring
              rw [e, ← hco2]; exact mul_le_mul_right' h2 oc
            have hsq : (2 * c1) ^ 2 ≤ c2 ^ 2 := Nat.pow_le_pow_left hc2ge 2
            have h4 : (2 * c1) ^ 2 = 4 * c1 ^ 2 := by ring
            rw [h4] at hsq
            omega
          · exact h
          · exfalso
            have h2 : 2 * 2 ^ b2 ≤ 2 ^ b1 := by
              rw [← _root_.pow_succ']; exact Nat.pow_le_pow_right (by norm_num) h
            have hc1ge : 2 * c2 ≤ c1 := by
              have e : 2 * c2 = (2 * 2 ^ b2) * oc := by rw [← hco2]; ring
              rw [e, ← hco1]; exact mul_le_mul_right' h2 oc
            have hsq : (2 * c2) ^ 2 ≤ c1 ^ 2 := Nat.pow_le_pow_left hc1ge 2
            have h4 : (2 * c2) ^ 2 = 4 * c2 ^ 2 := by ring
            rw [h4] at hsq
            omega
        rw [← hco1, ← hco2, hbeq]
      · -- surjective
        intro d hd
        rw [memA] at hd
        obtain ⟨⟨hdn, hdodd, hdlt⟩, hdge⟩ := hd
        have hdpos : 0 < d := Nat.pos_of_dvd_of_pos hdn (Nat.pos_of_ne_zero hn)
        have hdm : d ∣ m := hdvdm d hdn hdodd
        have hex : ∃ b, n ≤ 2 * (2 ^ b) ^ 2 * d ^ 2 := by
          refine ⟨a, ?_⟩
          calc n = 2 ^ a * m := hn_eq.symm
            _ ≤ 2 ^ a * (2 ^ (a + 1) * d ^ 2) := by gcongr
            _ = 2 * (2 ^ a) ^ 2 * d ^ 2 := by rw [pow_succ]; ring
        set b0 := Nat.find hex with hb0def
        have hb0spec : n ≤ 2 * (2 ^ b0) ^ 2 * d ^ 2 := Nat.find_spec hex
        have hb0le : b0 ≤ a := Nat.find_le (by
          calc n = 2 ^ a * m := hn_eq.symm
            _ ≤ 2 ^ a * (2 ^ (a + 1) * d ^ 2) := by gcongr
            _ = 2 * (2 ^ a) ^ 2 * d ^ 2 := by rw [pow_succ]; ring)
        refine ⟨2 ^ b0 * d, ?_, ?_⟩
        · -- middle
          rw [memMid]
          have hcdvd : 2 ^ b0 * d ∣ n := by
            rw [← hn_eq]
            exact Nat.mul_dvd_mul (pow_dvd_pow 2 hb0le) hdm
          refine ⟨hcdvd, ?_, ?_⟩
          · -- n ≤ 2*(2^b0*d)^2
            have : 2 * (2 ^ b0 * d) ^ 2 = 2 * (2 ^ b0) ^ 2 * d ^ 2 := by ring
            rw [this]; exact hb0spec
          · -- (2^b0*d)^2 < 2n
            rcases Nat.eq_zero_or_pos b0 with hb0 | hb0
            · rw [hb0]; simpa using hdlt
            · have hmin : ¬ (n ≤ 2 * (2 ^ (b0 - 1)) ^ 2 * d ^ 2) :=
                Nat.find_min hex (by omega)
              have hlt : 2 * (2 ^ (b0 - 1)) ^ 2 * d ^ 2 < n := not_le.mp hmin
              have hpow : (2 ^ b0 : ℕ) = 2 * 2 ^ (b0 - 1) := by
                rw [← _root_.pow_succ']; congr 1; omega
              have : (2 ^ b0 * d) ^ 2 = 2 * (2 * (2 ^ (b0 - 1)) ^ 2 * d ^ 2) := by
                rw [hpow]; ring
              rw [this]
              omega
        · -- ordCompl = d
          rw [Nat.ordCompl_self_pow_mul d b0 Nat.prime_two, ordCompl_odd d hdodd]
    -- Bijection Bneg ↔ Sgt
    have hBcard : Bneg.card = Sgt.card := by
      apply Finset.card_nbij' (fun d => m / d) (fun e => m / e)
      · -- MapsTo to Sgt
        intro d hd
        rw [Finset.mem_coe, memB] at hd
        obtain ⟨⟨hdn, hdodd, hdlt⟩, hdgt⟩ := hd
        have hdpos : 0 < d := Nat.pos_of_dvd_of_pos hdn (Nat.pos_of_ne_zero hn)
        have hdm : d ∣ m := hdvdm d hdn hdodd
        have hk : d * (m / d) = m := Nat.mul_div_cancel' hdm
        have hkpos : 0 < m / d := by
          rcases Nat.eq_zero_or_pos (m / d) with h | h
          · rw [h, mul_zero] at hk; omega
          · exact h
        rw [Finset.mem_coe, memSgt]
        refine ⟨(Nat.div_dvd_of_dvd hdm).trans hm_dvd_n, ?_, ?_⟩
        · exact hodd_of_dvd_m _ (Nat.div_dvd_of_dvd hdm)
        · -- 2n < (m/d)^2
          rw [h2n]
          have hdk : 2 ^ (a + 1) * d < m / d := by
            have h1 : d * (2 ^ (a + 1) * d) < d * (m / d) := by
              rw [hk]
              calc d * (2 ^ (a + 1) * d) = 2 ^ (a + 1) * d ^ 2 := by ring
                _ < m := hdgt
            exact Nat.lt_of_mul_lt_mul_left h1
          calc 2 ^ (a + 1) * m = (2 ^ (a + 1) * d) * (m / d) := by rw [mul_assoc, hk]
            _ < (m / d) * (m / d) := mul_lt_mul_of_pos_right hdk hkpos
            _ = (m / d) ^ 2 := by ring
      · -- MapsTo to Bneg
        intro e he
        rw [Finset.mem_coe, memSgt] at he
        obtain ⟨hen, heodd, hegt⟩ := he
        have hepos : 0 < e := Nat.pos_of_dvd_of_pos hen (Nat.pos_of_ne_zero hn)
        have hem : e ∣ m := hdvdm e hen heodd
        have hk : e * (m / e) = m := Nat.mul_div_cancel' hem
        have hkpos : 0 < m / e := by
          rcases Nat.eq_zero_or_pos (m / e) with h | h
          · rw [h, mul_zero] at hk; omega
          · exact h
        rw [Finset.mem_coe, memB]
        have hdivdvd : m / e ∣ m := Nat.div_dvd_of_dvd hem
        have hek : 2 ^ (a + 1) * (m / e) < e := by
          have h1 : e * (2 ^ (a + 1) * (m / e)) < e * e := by
            calc e * (2 ^ (a + 1) * (m / e)) = 2 ^ (a + 1) * (e * (m / e)) := by ring
              _ = 2 ^ (a + 1) * m := by rw [hk]
              _ = 2 * n := h2n.symm
              _ < e ^ 2 := hegt
              _ = e * e := by ring
          exact Nat.lt_of_mul_lt_mul_left h1
        have hprod : 2 ^ (a + 1) * (m / e) ^ 2 < m := by
          calc 2 ^ (a + 1) * (m / e) ^ 2 = (2 ^ (a + 1) * (m / e)) * (m / e) := by ring
            _ < e * (m / e) := mul_lt_mul_of_pos_right hek hkpos
            _ = m := hk
        refine ⟨⟨hdivdvd.trans hm_dvd_n, hodd_of_dvd_m _ hdivdvd, ?_⟩, ?_⟩
        · -- (m/e)^2 < 2n
          show (m / e) ^ 2 < 2 * n
          have hle1 : (m / e) ^ 2 ≤ 2 ^ (a + 1) * (m / e) ^ 2 :=
            Nat.le_mul_of_pos_left _ (pow_pos (show (0:ℕ) < 2 by norm_num) (a + 1))
          have hmlt2n : m < 2 * n := by
            rw [h2n]
            have h1 : (1 : ℕ) < 2 ^ (a + 1) := Nat.one_lt_two_pow (by omega)
            calc m = 1 * m := by ring
              _ < 2 ^ (a + 1) * m := mul_lt_mul_of_pos_right h1 hm_pos
          omega
        · -- 2^(a+1)*(m/e)^2 < m
          exact hprod
      · -- left inverse
        intro d hd
        rw [Finset.mem_coe, memB] at hd
        obtain ⟨⟨hdn, hdodd, _⟩, _⟩ := hd
        have hdm : d ∣ m := hdvdm d hdn hdodd
        exact Nat.div_div_self hdm hm_pos.ne'
      · -- right inverse
        intro e he
        rw [Finset.mem_coe, memSgt] at he
        obtain ⟨hen, heodd, _⟩ := he
        have hem : e ∣ m := hdvdm e hen heodd
        exact Nat.div_div_self hem hm_pos.ne'
    omega
  -- conclude
  have hA : A281009 n = (Sodd.card : ℤ) - (Mid.card : ℤ) := by
    rw [A281009, dif_neg hn]
  rw [hA, step1, step2]
  push_cast
  ring
