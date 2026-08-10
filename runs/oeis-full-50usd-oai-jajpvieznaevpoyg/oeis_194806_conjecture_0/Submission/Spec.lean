import FormalConjectures.Util.ProblemImports

open Finset Nat

/-- The set of all products of elements from a Finset S. -/
def set_prod (S : Finset ℕ) : Finset ℕ :=
  (S.product S).image fun p : ℕ × ℕ => p.fst * p.snd

/--
A194806: Size of the smallest subset $S$ of $T = \{1,2,3,\dots,n\}$ such that $S \cdot S$ contains $T$,
where $S \cdot S$ is the set of all products of elements of $S$.
-/
noncomputable def a (n : ℕ) : ℕ :=
  if h : n = 0 then 0
  else
    let T_n := Icc 1 n

    -- The set of subsets $S \subseteq T_n$ such that $T_n \subseteq S \cdot S$.
    let valid_subsets : Finset (Finset ℕ) :=
      T_n.powerset.filter (fun S : Finset ℕ => T_n ⊆ set_prod S)

    -- Proof that $T_n$ is guaranteed to be a valid subset, ensuring `valid_subsets` is non-empty.
    have T_n_is_valid : T_n ∈ valid_subsets := by
      apply mem_filter.mpr
      constructor
      -- 1. T_n ∈ T_n.powerset (i.e., T_n ⊆ T_n)
      apply mem_powerset.mpr; rfl
      -- 2. T_n ⊆ set_prod T_n
      intro k hk

      have one_le_n : 1 ≤ n := Nat.succ_le_of_lt (Nat.pos_of_ne_zero h)
      have h1 : 1 ∈ T_n := mem_Icc.mpr ⟨Nat.le_refl 1, one_le_n⟩

      -- We show k = k * 1 is in set_prod T_n
      -- set_prod T_n is the image of T_n × T_n under multiplication.
      simp only [set_prod, mem_image, Prod.exists]
      use k, 1
      constructor
      -- Show that (k, 1) ∈ T_n × T_n
      · exact mem_product.mpr ⟨hk, h1⟩
      -- Show that k * 1 = k
      · exact Nat.mul_one k

    have h_nonempty : valid_subsets.Nonempty := ⟨T_n, T_n_is_valid⟩

    let sizes := valid_subsets.image Finset.card

    -- The min' function requires proof that the finset is non-empty.
    have h_sizes_nonempty : sizes.Nonempty := h_nonempty.image Finset.card

    -- We return the minimum card of all valid subsets.
    sizes.min' h_sizes_nonempty

open Filter Asymptotics
open scoped Topology

namespace Nat
lemma maxPrimeFac_dvd_of_one_lt (n : ℕ) (h : 1 < n) : maxPrimeFac n ∣ n := by
  set s := {p : ℕ | p.Prime ∧ p ∣ n} with hs
  have hs₀ : s.Nonempty := by
    simp only [Set.Nonempty, Set.mem_setOf_eq, ← ne_one_iff_exists_prime_dvd, hs]
    omega
  have hs₁ : BddAbove s := by
    use n
    simp only [hs, mem_upperBounds, Set.mem_setOf_eq, and_imp]
    exact fun p _ hp ↦ Nat.le_of_dvd (zero_lt_of_lt h) hp
  exact (Nat.sSup_mem hs₀ hs₁).2

lemma le_maxPrimeFac_of_prime_dvd {n p : ℕ} (hn : 0 < n) (hp : p.Prime) (hpdvd : p ∣ n) :
    p ≤ maxPrimeFac n := by
  set s := {p : ℕ | p.Prime ∧ p ∣ n}
  have hs₁ : BddAbove s := by
    use n
    simp only [s, mem_upperBounds, Set.mem_setOf_eq, and_imp]
    exact fun p _ hp ↦ Nat.le_of_dvd hn hp
  exact ConditionallyCompleteLattice.le_csSup s p hs₁ ⟨hp, hpdvd⟩
end Nat

lemma exists_two_factors_le_of_primeFactors_le
    (B T N m : ℕ) (hTpos : 0 < T) (hBN : B * N ≤ T * T) (hmN : m ≤ N)
    (hpf : ∀ p : ℕ, p.Prime → p ∣ m → p ≤ B) :
    ∃ x y : ℕ, x ≤ T ∧ y ≤ T ∧ m = x * y := by
  induction m using Nat.strong_induction_on with
  | h m ih =>
    by_cases hmT : m ≤ T
    · exact ⟨1, m, Nat.succ_le_of_lt hTpos, hmT, by simp⟩
    · have hmpos : 0 < m := by omega
      have hm1 : m ≠ 1 := by intro hm; subst hm; exact hmT (Nat.succ_le_of_lt hTpos)
      obtain ⟨p, hp_and⟩ := Nat.exists_prime_and_dvd hm1
      have hp : Nat.Prime p := hp_and.1
      have hpdvd0 : p ∣ m := hp_and.2
      obtain ⟨q, hqeq⟩ := hpdvd0
      have hpB : p ≤ B := hpf p hp hp_and.2
      have hp2 : 2 ≤ p := hp.two_le
      have hqpos : 0 < q := by
        by_contra hq0
        have : q = 0 := by omega
        simp [this] at hqeq
        omega
      have hqm : q < m := by
        rw [hqeq]
        nlinarith [hp2, hqpos]
      have hqN : q ≤ N := le_trans (Nat.le_of_lt hqm) hmN
      have hpfq : ∀ r : ℕ, r.Prime → r ∣ q → r ≤ B := by
        intro r hr hrdvd
        apply hpf r hr
        exact dvd_trans hrdvd (by rw [hqeq]; exact dvd_mul_left q p)
      obtain ⟨x,y,hx,hy,hqxy⟩ := ih q hqm hqN hpfq
      by_cases hpx : p * x ≤ T
      · refine ⟨p*x, y, hpx, hy, ?_⟩
        rw [hqeq, hqxy]
        ring
      · by_cases hpy : p * y ≤ T
        · refine ⟨x, p*y, hx, hpy, ?_⟩
          rw [hqeq, hqxy]
          ring
        · have hlt1 : T < p * x := Nat.lt_of_not_ge hpx
          have hlt2 : T < p * y := Nat.lt_of_not_ge hpy
          have hTTlt : T * T < (p * x) * (p * y) := mul_lt_mul'' hlt1 hlt2 (Nat.zero_le _) (Nat.zero_le _)
          have heq : (p * x) * (p * y) = p * m := by
            rw [hqeq, hqxy]
            ring
          have hle : p * m ≤ B * N := Nat.mul_le_mul hpB hmN
          omega

def basisSet (n : ℕ) : Finset ℕ :=
  let B := Nat.nthRoot 4 n + 1
  let T := B ^ 3
  (Icc 1 (min T n)) ∪ (n + 1).primesBelow

lemma root4_conditions (n : ℕ) :
    let B := Nat.nthRoot 4 n + 1
    let T := B ^ 3
    0 < T ∧ B * n ≤ T * T ∧ n ≤ B * T := by
  intro B T
  have hBpos : 0 < B := by dsimp [B]; omega
  have hnlt4 : n < B ^ 4 := by
    dsimp [B]
    simpa [pow_succ] using Nat.lt_pow_nthRoot_add_one (by norm_num : (4:ℕ) ≠ 0) n
  have hnle5 : n ≤ B ^ 5 := by
    exact (Nat.le_of_lt hnlt4).trans (by
      have : B ^ 4 ≤ B ^ 5 := by
        calc B^4 ≤ B^4 * B := by
              nth_rewrite 1 [← mul_one (B^4)]
              exact Nat.mul_le_mul_left _ (by omega : 1 ≤ B)
          _ = B^5 := by ring
      simpa using this)
  have hBN : B * n ≤ T * T := by
    dsimp [T]
    calc B * n ≤ B * B ^ 5 := Nat.mul_le_mul_left B hnle5
      _ = B^3 * B^3 := by ring
  have hBT : n ≤ B * T := by
    apply Nat.le_of_lt
    dsimp [T]
    calc n < B^4 := hnlt4
      _ = B * B^3 := by ring
  exact ⟨by positivity, hBN, hBT⟩

lemma mem_basis_small {n x : ℕ} (hx1 : 1 ≤ x) (hxT : x ≤ (Nat.nthRoot 4 n + 1)^3) (hxn : x ≤ n) :
    x ∈ basisSet n := by
  simp [basisSet, hx1, hxT, hxn]

lemma mem_basis_prime {n p : ℕ} (hp : p.Prime) (hpn : p ≤ n) : p ∈ basisSet n := by
  simp [basisSet, Nat.primesBelow, hp, Nat.lt_succ_iff, hpn]

lemma Icc_subset_set_prod_basis (n : ℕ) : Icc 1 n ⊆ set_prod (basisSet n) := by
  intro k hk
  rcases mem_Icc.mp hk with ⟨hk1,hkn⟩
  let B := Nat.nthRoot 4 n + 1
  let T := B^3
  have hcond := root4_conditions n
  dsimp only at hcond
  change 0 < T ∧ B * n ≤ T * T ∧ n ≤ B * T at hcond
  rcases hcond with ⟨hTpos,hBN,hBT⟩
  have one_mem : 1 ∈ basisSet n := by
    apply mem_basis_small (n:=n) (by omega) (by simpa [B,T] using Nat.succ_le_of_lt hTpos) (by omega)
  have prod_mem (x y : ℕ) (hx : x ∈ basisSet n) (hy : y ∈ basisSet n) (hxy : k = x*y) : k ∈ set_prod (basisSet n) := by
    simp only [set_prod, mem_image, Prod.exists]
    refine ⟨x,y,?_,hxy.symm⟩
    exact mem_product.mpr ⟨hx,hy⟩
  by_cases hkprime : k.Prime
  · exact prod_mem k 1 (mem_basis_prime hkprime hkn) one_mem (by simp)
  · by_cases hkT : k ≤ T
    · exact prod_mem k 1 (by simpa [B,T] using mem_basis_small (n:=n) hk1 hkT hkn) one_mem (by simp)
    · have hkgt1 : 1 < k := by omega
      let P := Nat.maxPrimeFac k
      have hPprime : P.Prime := Nat.prime_maxPrimeFac_of_one_lt k hkgt1
      have hPdvd : P ∣ k := Nat.maxPrimeFac_dvd_of_one_lt k hkgt1
      have hPdvd0 : P ∣ k := hPdvd
      by_cases hPB : P ≤ B
      · have hpf : ∀ p : ℕ, p.Prime → p ∣ k → p ≤ B := by
          intro p hp hpd
          exact (Nat.le_maxPrimeFac_of_prime_dvd (by omega : 0 < k) hp hpd).trans hPB
        obtain ⟨x,y,hxT,hyT,hkxy⟩ := exists_two_factors_le_of_primeFactors_le B T n k hTpos hBN hkn hpf
        have hxpos : 1 ≤ x := by
          by_contra hx0
          have hxzero : x = 0 := by omega
          have : k = 0 := by rw [hkxy, hxzero, zero_mul]
          omega
        have hypos : 1 ≤ y := by
          by_contra hy0
          have hyzero : y = 0 := by omega
          have : k = 0 := by rw [hkxy, hyzero, mul_zero]
          omega
        exact prod_mem x y (by simpa [B,T] using mem_basis_small (n:=n) hxpos hxT (by
              calc x = x * 1 := by simp
                _ ≤ x * y := Nat.mul_le_mul_left x hypos
                _ = k := hkxy.symm
                _ ≤ n := hkn))
          (by simpa [B,T] using mem_basis_small (n:=n) hypos hyT (by
              calc y = 1 * y := by simp
                _ ≤ x * y := Nat.mul_le_mul_right y hxpos
                _ = k := hkxy.symm
                _ ≤ n := hkn)) hkxy
      · obtain ⟨q, hkPq⟩ := hPdvd
        have hqpos : 1 ≤ q := by
          have : 0 < q := by
            by_contra hq0
            have : q = 0 := by omega
            simp [this] at hkPq
            omega
          omega
        have hqT : q ≤ T := by
          by_contra hqnot
          have hTq : T < q := Nat.lt_of_not_ge hqnot
          have hPBlt : B < P := Nat.lt_of_not_ge hPB
          have hBTlt : B * T < P * q := mul_lt_mul'' hPBlt hTq (Nat.zero_le _) (Nat.zero_le _)
          have hle : P * q ≤ B * T := by
            rw [← hkPq]
            exact hkn.trans hBT
          omega
        have hPmem : P ∈ basisSet n := by
          apply mem_basis_prime hPprime
          exact (Nat.le_of_dvd (by omega : 0 < k) hPdvd0).trans hkn
        exact prod_mem P q hPmem (by simpa [B,T] using mem_basis_small (n:=n) hqpos hqT (by
              calc q = 1 * q := by simp
                _ ≤ P * q := Nat.mul_le_mul_right q (by exact hPprime.one_le)
                _ = k := hkPq.symm
                _ ≤ n := hkn)) hkPq

lemma card_basisSet_le (n : ℕ) :
    (basisSet n).card ≤ (Nat.nthRoot 4 n + 1)^3 + Nat.primeCounting n := by
  dsimp [basisSet]
  refine (card_union_le _ _).trans ?_
  gcongr
  · rw [card_Icc]
    omega
  · simpa [Nat.primeCounting, Nat.primesBelow_card_eq_primeCounting']

lemma a_le_basis_bound (n : ℕ) (hn : n ≠ 0) :
    a n ≤ (Nat.nthRoot 4 n + 1)^3 + Nat.primeCounting n := by
  classical
  let Tn := Icc 1 n
  let valid_subsets : Finset (Finset ℕ) := Tn.powerset.filter (fun S : Finset ℕ => Tn ⊆ set_prod S)
  have hvalid : basisSet n ∈ valid_subsets := by
    apply mem_filter.mpr
    constructor
    · apply mem_powerset.mpr
      intro x hx
      simp only [Tn, mem_Icc]
      simp only [basisSet, mem_union, mem_Icc, mem_primesBelow] at hx
      rcases hx with hx | hx
      · exact ⟨hx.1, hx.2.trans (min_le_right _ _)⟩
      · exact ⟨hx.2.one_le, Nat.lt_succ_iff.mp hx.1⟩
    · exact Icc_subset_set_prod_basis n
  rw [a, dif_neg hn]
  dsimp only
  change (valid_subsets.image Finset.card).min' _ ≤ (Nat.nthRoot 4 n + 1)^3 + Nat.primeCounting n
  exact (Finset.min'_le _ _ (Finset.mem_image.mpr ⟨basisSet n, hvalid, rfl⟩)).trans (card_basisSet_le n)

lemma centralBinom_le_pow_primeCounting (n : ℕ) (hn : 0 < n) :
    n.centralBinom ≤ (2 * n) ^ Nat.primeCounting (2 * n) := by
  classical
  rw [← Nat.prod_pow_factorization_centralBinom n]
  let S : Finset ℕ := {p ∈ Finset.range (2 * n + 1) | Nat.Prime p}
  have hprod : ∏ p ∈ Finset.range (2 * n + 1), p ^ n.centralBinom.factorization p =
      ∏ p ∈ S, p ^ n.centralBinom.factorization p := by
    dsimp [S]
    rw [Finset.prod_filter]
    apply Finset.prod_congr rfl
    intro p hp
    by_cases hprime : Nat.Prime p
    · simp [hprime]
    · simp [hprime, Nat.factorization_eq_zero_of_not_prime n.centralBinom hprime]
  rw [hprod]
  calc
    ∏ p ∈ S, p ^ n.centralBinom.factorization p ≤ ∏ p ∈ S, (2 * n) := by
      apply Finset.prod_le_prod
      · intro p hp; exact pow_nonneg (Nat.zero_le _) _
      · intro p hp
        simpa [Nat.centralBinom] using (Nat.pow_factorization_choose_le (p:=p) (n:=2*n) (k:=n) (by positivity : 0 < 2*n))
    _ = (2 * n) ^ S.card := by simp
    _ = (2 * n) ^ Nat.primeCounting (2 * n) := by
      congr 1
      dsimp [S]
      simp [Nat.primeCounting, ← Nat.primesBelow_card_eq_primeCounting', Nat.primesBelow]


lemma test_little : (fun x : ℝ => Real.log x + x ^ ((3:ℝ)/4) * Real.log (2*x)) =o[atTop] (fun x => x) := by
  have hlog : Real.log =o[atTop] (fun x : ℝ => x) := by
    simpa [Real.rpow_one] using (isLittleO_log_rpow_atTop (by norm_num : (0:ℝ)<(1:ℝ)))
  have hcomp : (fun x : ℝ => Real.log (2*x)) =o[atTop] (fun x : ℝ => (2*x) ^ ((1:ℝ)/4)) := by
    exact (isLittleO_log_rpow_atTop (by norm_num : (0:ℝ)<(1/4:ℝ))).comp_tendsto ((tendsto_const_mul_atTop_iff_pos tendsto_id).mpr (by norm_num : (0:ℝ)<2))
  have hbig : (fun x : ℝ => (2*x) ^ ((1:ℝ)/4)) =O[atTop] (fun x : ℝ => x ^ ((1:ℝ)/4)) := by
    refine IsBigO.of_bound (2 ^ ((1:ℝ)/4)) ?_
    filter_upwards [eventually_ge_atTop (0:ℝ)] with x hx
    rw [Real.norm_of_nonneg (by positivity : 0 ≤ (2*x)^((1:ℝ)/4)), Real.norm_of_nonneg (by positivity : 0 ≤ x^((1:ℝ)/4))]
    rw [Real.mul_rpow (by norm_num : (0:ℝ)≤2) hx]
  have hlog2 : (fun x : ℝ => Real.log (2*x)) =o[atTop] (fun x : ℝ => x ^ ((1:ℝ)/4)) := hcomp.trans_isBigO hbig
  have hx34 : (fun x : ℝ => x ^ ((3:ℝ)/4)) =O[atTop] (fun x : ℝ => x ^ ((3:ℝ)/4)) := isBigO_refl _ _
  have hprod := hx34.mul_isLittleO hlog2
  have hprod' : (fun x : ℝ => x ^ ((3:ℝ)/4) * Real.log (2*x)) =o[atTop] (fun x : ℝ => x) := by
    -- hprod target x^(3/4)*x^(1/4)
    refine hprod.trans_isBigO ?_
    refine (Eventually.isBigO ?_)
    filter_upwards [eventually_ge_atTop (1:ℝ)] with x hx
    rw [← Real.rpow_add (zero_lt_one.trans_le hx)]
    rw [show ((3:ℝ)/4 + (1:ℝ)/4) = 1 by norm_num, Real.rpow_one, Real.norm_of_nonneg (zero_le_one.trans hx)]
  exact hlog.add hprod'

lemma eventually_rpow_le_primeCounting_two :
    ∀ᶠ m : ℕ in atTop, (m : ℝ) ^ ((3:ℝ)/4) ≤ (Nat.primeCounting (2*m) : ℝ) := by
  have hlittle := test_little
  have hlog4pos : 0 < Real.log 4 := Real.log_pos (by norm_num : (1:ℝ) < 4)
  have hscale : (fun x : ℝ => (2 / Real.log 4) * (Real.log x + x ^ ((3:ℝ)/4) * Real.log (2*x))) =o[atTop] (fun x => x) :=
    hlittle.const_mul_left _
  have hev := hscale.eventuallyLE
  have hev_nat : ∀ᶠ m : ℕ in atTop, ‖(2 / Real.log 4) * (Real.log (m:ℝ) + (m:ℝ) ^ ((3:ℝ)/4) * Real.log (2*(m:ℝ)))‖ ≤ ‖(m:ℝ)‖ := by
    simpa using tendsto_natCast_atTop_atTop.eventually hev
  filter_upwards [hev_nat, eventually_ge_atTop (4:ℕ)] with m hmle hm4
  by_contra hnot
  have hmpos_nat : 0 < m := by omega
  have hmpos : (0:ℝ) < m := by exact_mod_cast hmpos_nat
  have hmone : (1:ℝ) ≤ m := by exact_mod_cast (by omega : 1 ≤ m)
  have htwompos : (0:ℝ) < (2*m:ℕ) := by exact_mod_cast (by positivity : 0 < 2*m)
  have htwom_ge1 : (1:ℝ) ≤ (2*m:ℕ) := by exact_mod_cast (by omega : 1 ≤ 2*m)
  have hpi_lt : (Nat.primeCounting (2*m) : ℝ) < (m : ℝ) ^ ((3:ℝ)/4) := lt_of_not_ge hnot
  have hcentral_nat : 4 ^ m ≤ m * m.centralBinom := Nat.le_of_lt (Nat.four_pow_lt_mul_centralBinom m (by omega : 4 ≤ m))
  have hupper_nat : m * m.centralBinom ≤ m * (2*m) ^ Nat.primeCounting (2*m) := by
    exact Nat.mul_le_mul_left m (centralBinom_le_pow_primeCounting m hmpos_nat)
  have hpow_nat : 4 ^ m ≤ m * (2*m) ^ Nat.primeCounting (2*m) := hcentral_nat.trans hupper_nat
  have hpow_real : (4:ℝ)^m ≤ (m:ℝ) * (((2*m : ℕ) : ℝ) ^ Nat.primeCounting (2*m)) := by exact_mod_cast hpow_nat
  have hlogineq := Real.log_le_log (by positivity) hpow_real
  rw [Real.log_pow, Real.log_mul (by exact_mod_cast (Nat.ne_of_gt hmpos_nat)) (by positivity : (((2*m : ℕ) : ℝ) ^ Nat.primeCounting (2*m)) ≠ 0), Real.log_pow] at hlogineq
  have hlog2_nonneg : 0 ≤ Real.log (((2*m : ℕ) : ℝ)) := Real.log_nonneg htwom_ge1
  have hrhs_le : Real.log (m:ℝ) + (Nat.primeCounting (2*m) : ℝ) * Real.log (((2*m : ℕ) : ℝ)) ≤
      Real.log (m:ℝ) + (m:ℝ)^((3:ℝ)/4) * Real.log (2*(m:ℝ)) := by
    rw [show (((2*m : ℕ) : ℝ)) = 2*(m:ℝ) by norm_num]
    have hmul2 : (Nat.primeCounting (2*m) : ℝ) * Real.log (2 * (m:ℝ)) ≤ (m:ℝ)^((3:ℝ)/4) * Real.log (2 * (m:ℝ)) :=
      mul_le_mul_of_nonneg_right (le_of_lt hpi_lt) (by rwa [show (2*(m:ℝ)) = (((2*m:ℕ):ℝ)) by norm_num])
    linarith
  have hf_le : Real.log (m:ℝ) + (m:ℝ)^((3:ℝ)/4) * Real.log (2*(m:ℝ)) ≤ (Real.log 4 / 2) * (m:ℝ) := by
    have hf_nonneg : 0 ≤ Real.log (m:ℝ) + (m:ℝ)^((3:ℝ)/4) * Real.log (2*(m:ℝ)) := by
      apply add_nonneg
      · exact Real.log_nonneg hmone
      · have hcast2 : (2*(m:ℝ)) = (((2*m:ℕ):ℝ)) := by norm_num
        exact mul_nonneg (by positivity) (by rwa [hcast2])
    have hcoefpos : 0 < 2 / Real.log 4 := div_pos (by norm_num) hlog4pos
    have hmle' := hmle
    rw [Real.norm_of_nonneg (mul_nonneg hcoefpos.le hf_nonneg), Real.norm_of_nonneg (by exact le_trans (by norm_num) hmone)] at hmle'
    have hhalf_nonneg : 0 ≤ Real.log 4 / 2 := by positivity
    have hmul := mul_le_mul_of_nonneg_left hmle' hhalf_nonneg
    have hcoef : (Real.log 4 / 2) * (2 / Real.log 4) = 1 := by field_simp [hlog4pos.ne']
    rwa [← mul_assoc, hcoef, one_mul] at hmul
  have : (m:ℝ) * Real.log 4 ≤ (Real.log 4 / 2) * (m:ℝ) := hlogineq.trans (hrhs_le.trans hf_le)
  nlinarith [hlog4pos, hmpos]
lemma threshold_le_eight (n : ℕ) (hn : 1 ≤ n) :
    (((Nat.nthRoot 4 n + 1)^3 : ℕ) : ℝ) ≤ 8 * (n : ℝ) ^ ((3:ℝ)/4) := by
  let r := Nat.nthRoot 4 n
  have hr1 : 1 ≤ r := by
    rw [Nat.le_nthRoot_iff (by norm_num : (4:ℕ) ≠ 0)]
    simpa using hn
  have hr4nat : r ^ 4 ≤ n := by
    exact Nat.pow_nthRoot_le (Or.inl (by norm_num : (4:ℕ) ≠ 0))
  have hr4 : (r:ℝ)^4 ≤ (n:ℝ) := by exact_mod_cast hr4nat
  have hr_nonneg : 0 ≤ (r:ℝ) := by positivity
  have hn_nonneg : 0 ≤ (n:ℝ) := by positivity
  have hr_le : (r:ℝ) ≤ (n:ℝ)^((1:ℝ)/4) := by
    have h := Real.rpow_le_rpow (show 0 ≤ (r:ℝ)^4 by positivity) hr4 (by norm_num : (0:ℝ) ≤ 1/4)
    rw [← Real.rpow_natCast, ← Real.rpow_mul hr_nonneg] at h
    norm_num at h
    exact h
  calc
    (((r + 1)^3 : ℕ) : ℝ) ≤ ((2*r)^3 : ℕ) := by
      exact_mod_cast Nat.pow_le_pow_left (by omega : r + 1 ≤ 2*r) 3
    _ = (8:ℝ) * (r:ℝ)^3 := by norm_num [pow_succ]; ring
    _ ≤ 8 * ((n:ℝ)^((1:ℝ)/4))^3 := by gcongr
    _ = 8 * (n:ℝ)^((3:ℝ)/4) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hn_nonneg]
      norm_num

lemma threshold_le_32_half (n : ℕ) (hn : 2 ≤ n) :
    (((Nat.nthRoot 4 n + 1)^3 : ℕ) : ℝ) ≤ 32 * ((n / 2 : ℕ) : ℝ) ^ ((3:ℝ)/4) := by
  have h1 : 1 ≤ n := by omega
  have hbase := threshold_le_eight n h1
  let m := n / 2
  have hm1 : 1 ≤ m := by dsimp [m]; omega
  have hn_le : (n:ℝ) ≤ 4 * (m:ℝ) := by
    have hn_nat : n ≤ 4 * m := by
      dsimp [m]
      omega
    exact_mod_cast hn_nat
  have hrpow : (n:ℝ)^((3:ℝ)/4) ≤ (4*(m:ℝ))^((3:ℝ)/4) :=
    Real.rpow_le_rpow (by positivity) hn_le (by norm_num : (0:ℝ) ≤ 3/4)
  have hmul : (4*(m:ℝ))^((3:ℝ)/4) ≤ 4 * (m:ℝ)^((3:ℝ)/4) := by
    rw [Real.mul_rpow (by norm_num : (0:ℝ)≤4) (by positivity : 0 ≤ (m:ℝ))]
    have h4 : (4:ℝ)^((3:ℝ)/4) ≤ 4 := by
      have := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 4) (by norm_num : ((3:ℝ)/4) ≤ 1)
      simpa [Real.rpow_one] using this
    gcongr
  calc
    (((Nat.nthRoot 4 n + 1)^3 : ℕ) : ℝ) ≤ 8 * (n:ℝ)^((3:ℝ)/4) := hbase
    _ ≤ 8 * ((4*(m:ℝ))^((3:ℝ)/4)) := by gcongr
    _ ≤ 8 * (4 * (m:ℝ)^((3:ℝ)/4)) := by gcongr
    _ = 32 * (m:ℝ)^((3:ℝ)/4) := by ring

lemma a_le_self (n : ℕ) (hn : n ≠ 0) : a n ≤ n := by
  classical
  let Tn := Icc 1 n
  let valid_subsets : Finset (Finset ℕ) := Tn.powerset.filter (fun S : Finset ℕ => Tn ⊆ set_prod S)
  have hvalid : Tn ∈ valid_subsets := by
    apply mem_filter.mpr
    constructor
    · exact mem_powerset.mpr (by intro x hx; exact hx)
    · intro k hk
      have one_le_n : 1 ≤ n := Nat.succ_le_of_lt (Nat.pos_of_ne_zero hn)
      have h1 : 1 ∈ Tn := mem_Icc.mpr ⟨Nat.le_refl 1, one_le_n⟩
      simp only [set_prod, mem_image, Prod.exists]
      refine ⟨k,1,?_, by simp⟩
      exact mem_product.mpr ⟨hk,h1⟩
  rw [a, dif_neg hn]
  dsimp only
  change (valid_subsets.image Finset.card).min' _ ≤ n
  calc
    (valid_subsets.image Finset.card).min' _ ≤ Tn.card := Finset.min'_le _ _ (Finset.mem_image.mpr ⟨Tn,hvalid,rfl⟩)
    _ = n := by simp [Tn]

lemma primeCounting_pos_of_two_le {n : ℕ} (hn : 2 ≤ n) : 0 < Nat.primeCounting n := by
  have hne : Nat.primeCounting n ≠ 0 := by
    intro hzero
    have hle1 := Nat.primeCounting_eq_zero_iff.mp hzero
    omega
  exact Nat.pos_of_ne_zero hne


/--
**OEIS A194806 Conjecture:** Is $a(n)/\pi(n)$ bounded as $n \to \infty$?
(Where $\pi(n) = A000720(n)$ is the prime counting function `Nat.primeCounting n`).
-/
theorem oeis_194806_conjecture_0 :
  ∃ C : ℝ, ∀ n : ℕ, 2 ≤ n →
    (a n : ℝ) / (Nat.primeCounting n : ℝ) ≤ C := by
  classical
  obtain ⟨K, hK⟩ := Filter.eventually_atTop.1 eventually_rpow_le_primeCounting_two
  let N0 : ℕ := max (2 * K) 2
  refine ⟨max (33 : ℝ) (N0 : ℝ), ?_⟩
  intro n hn2
  have hden_nat : 0 < Nat.primeCounting n := primeCounting_pos_of_two_le hn2
  have hden_pos : 0 < (Nat.primeCounting n : ℝ) := by exact_mod_cast hden_nat
  by_cases hnlarge : N0 ≤ n
  · let m : ℕ := n / 2
    have hmK : K ≤ m := by
      dsimp [N0] at hnlarge
      dsimp [m]
      omega
    have hm2 : 2 * m ≤ n := by dsimp [m]; omega
    have hlow_m : (m : ℝ) ^ ((3:ℝ)/4) ≤ (Nat.primeCounting (2*m) : ℝ) := hK m hmK
    have hmono_nat : Nat.primeCounting (2*m) ≤ Nat.primeCounting n := Nat.monotone_primeCounting hm2
    have hlow : (m : ℝ) ^ ((3:ℝ)/4) ≤ (Nat.primeCounting n : ℝ) := hlow_m.trans (by exact_mod_cast hmono_nat)
    have hT : (((Nat.nthRoot 4 n + 1)^3 : ℕ) : ℝ) ≤ 32 * (Nat.primeCounting n : ℝ) := by
      calc
        (((Nat.nthRoot 4 n + 1)^3 : ℕ) : ℝ) ≤ 32 * (m : ℝ) ^ ((3:ℝ)/4) := threshold_le_32_half n hn2
        _ ≤ 32 * (Nat.primeCounting n : ℝ) := by gcongr
    have ha_nat := a_le_basis_bound n (by omega : n ≠ 0)
    have ha : (a n : ℝ) ≤ 33 * (Nat.primeCounting n : ℝ) := by
      have hcast : (a n : ℝ) ≤ (((Nat.nthRoot 4 n + 1)^3 : ℕ) : ℝ) + (Nat.primeCounting n : ℝ) := by exact_mod_cast ha_nat
      nlinarith [hT]
    have hdiv : (a n : ℝ) / (Nat.primeCounting n : ℝ) ≤ (33 : ℝ) := (div_le_iff₀ hden_pos).2 (by simpa [mul_comm] using ha)
    exact hdiv.trans (le_max_left _ _)
  · have hnsmall : n ≤ N0 := by omega
    have ha_nat := a_le_self n (by omega : n ≠ 0)
    have ha_real : (a n : ℝ) ≤ (N0 : ℝ) := by exact_mod_cast (ha_nat.trans hnsmall)
    have hden_ge_one : (1 : ℝ) ≤ (Nat.primeCounting n : ℝ) := by exact_mod_cast hden_nat
    have hratio_le_a : (a n : ℝ) / (Nat.primeCounting n : ℝ) ≤ (a n : ℝ) := by
      rw [div_le_iff₀ hden_pos]
      have ha_nonneg : 0 ≤ (a n : ℝ) := by exact_mod_cast Nat.zero_le (a n)
      nlinarith [mul_le_mul_of_nonneg_left hden_ge_one ha_nonneg]
    exact (hratio_le_a.trans ha_real).trans (le_max_right _ _)
