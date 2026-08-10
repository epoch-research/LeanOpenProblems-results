import FormalConjectures.Util.ProblemImports

open Nat List

/--
A340592: $a(n)$ is the concatenation of the prime factors (with multiplicity) of $n$ modulo $n$.
The prime factors are taken in non-decreasing order as given by $n.\operatorname{primeFactorsList}$.
-/
def a (n : ℕ) : ℕ :=
  if n < 2 then 0
  else
    let factors_list := n.primeFactorsList

    -- Calculates 10^(number of decimal digits of k)
    let pow10_len (k : ℕ) : ℕ := 10 ^ (Nat.digits 10 k).length

    -- The concatenation operation: acc || factor
    let concat_op (acc factor : ℕ) : ℕ :=
      acc * pow10_len factor + factor

    (factors_list.foldl concat_op 0) % n

/-- The property of being composite (n > 1 and not prime) -/
def Nat.composite (n : ℕ) : Prop := ¬ (Nat.Prime n) ∧ 1 < n

set_option linter.unusedVariables false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def facAux : ℕ → ℕ → ℕ → List ℕ
  | 0, k, n => []
  | fuel+1, k, n =>
      if n < 2 then []
      else if n < k*k then [n]
      else if k ∣ n then k :: facAux fuel k (n / k)
      else facAux fuel (k+1) n

private lemma prime_of_no_small_dvd {k n : ℕ} (hk : 2 ≤ k) (hn : 2 ≤ n) (hsmall : n < k*k)
    (hmin : ∀ d, 2 ≤ d → d < k → ¬ d ∣ n) : Nat.Prime n := by
  refine Nat.prime_def_lt'.2 ⟨hn, ?_⟩
  intro m hm2 hmn hmd
  by_cases hmk : m < k
  · exact hmin m hm2 hmk hmd
  · push_neg at hmk
    rcases hmd with ⟨q, rfl⟩
    have hmpos : 0 < m := by omega
    have hqpos : 0 < q := by
      by_contra hq
      have : q = 0 := by omega
      subst q
      simp at hn
    have hq2 : 2 ≤ q := by
      by_contra hqnot
      have hqeq : q = 1 := by omega
      subst q
      have : ¬ m < m * 1 := by simp
      exact this hmn
    have hkq : k ≤ q := by
      by_contra hqknot
      have hqk : q < k := by omega
      have hqdvd : q ∣ m * q := ⟨m, by rw [mul_comm]⟩
      exact hmin q hq2 hqk hqdvd
    have : k * k ≤ m * q := Nat.mul_le_mul hmk hkq
    omega

private lemma facAux_correct : ∀ fuel k n : ℕ,
    n < k + fuel → 2 ≤ k → (∀ d, 2 ≤ d → d < k → ¬ d ∣ n) →
    ((facAux fuel k n).prod = if n < 2 then 1 else n) ∧
    (∀ p ∈ facAux fuel k n, Nat.Prime p) ∧
    (facAux fuel k n).SortedLE ∧
    (∀ p ∈ facAux fuel k n, k ≤ p)
  | 0, k, n, hf, hk, hmin => by
      simp [facAux]
      by_cases hn : n < 2
      · simp [hn]
        rw [List.sortedLE_iff_pairwise]
        simp
      · have hn2 : 2 ≤ n := by omega
        have hnk : n < k := by simpa using hf
        exact False.elim (hmin n hn2 hnk dvd_rfl)
  | fuel+1, k, n, hf, hk, hmin => by
      by_cases hnlt : n < 2
      · simp [facAux, hnlt]
        rw [List.sortedLE_iff_pairwise]
        simp
      · have hn2 : 2 ≤ n := by omega
        by_cases hs : n < k*k
        · have hp : Nat.Prime n := prime_of_no_small_dvd hk hn2 hs hmin
          have hkn : k ≤ n := by
            by_contra hnot
            have hnk : n < k := by omega
            exact hmin n hn2 hnk dvd_rfl
          simp [facAux, hnlt, hs, hp, hkn]
          rw [List.sortedLE_iff_pairwise]
          simp
        · by_cases hd : k ∣ n
          · have hkprime : Nat.Prime k := by
              refine Nat.prime_def_lt'.2 ⟨hk, ?_⟩
              intro m hm2 hmk hmd
              exact hmin m hm2 hmk (hmd.trans hd)
            have hdivlt : n / k < n := Nat.div_lt_self (by omega) (by omega)
            have hf' : n / k < k + fuel := by omega
            have hmin' : ∀ d, 2 ≤ d → d < k → ¬ d ∣ n / k := by
              intro d hd2 hdk hdnk
              exact hmin d hd2 hdk (hdnk.trans (Nat.div_dvd_of_dvd hd))
            have ih := facAux_correct fuel k (n / k) hf' hk hmin'
            rcases ih with ⟨hprod, hprime, hsort, hge⟩
            have hnkdvd : k * (n / k) = n := by
              simpa [Nat.mul_comm] using (Nat.div_mul_cancel hd)
            have hnkdge2 : ¬ n / k < 2 := by
              -- since n is not less than k*k and k divides n, quotient is at least k, hence at least 2
              by_contra hq
              have hqle : n / k ≤ 1 := by omega
              have hnle : n ≤ k := by
                rw [← hnkdvd]
                simpa using (Nat.mul_le_mul_left k hqle)
              have hklt : k < k*k := by nlinarith [hk]
              have : n < k*k := lt_of_le_of_lt hnle hklt
              exact hs this
            -- easier establish product by cases on quotient <2 using contradiction above
            have hprod' : (facAux fuel k (n / k)).prod = n / k := by simpa [hnkdge2] using hprod
            constructor
            · simp [facAux, hnlt, hs, hd, hprod', hnkdvd]
            constructor
            · intro p hp
              simp [facAux, hnlt, hs, hd] at hp
              rcases hp with rfl | hp
              · exact hkprime
              · exact hprime p hp
            constructor
            · -- sorted cons: all recursive factors are >= k
              simp [facAux, hnlt, hs, hd]
              rw [List.sortedLE_iff_pairwise] at hsort ⊢
              simpa using And.intro hge hsort
            · intro p hp
              simp [facAux, hnlt, hs, hd] at hp
              rcases hp with rfl | hp
              · exact le_rfl
              · exact hge p hp
          · have hmin2 : ∀ d, 2 ≤ d → d < k + 1 → ¬ d ∣ n := by
              intro d hd2 hdk1 hdn
              have hdk_or : d < k ∨ d = k := by omega
              rcases hdk_or with hdk | rfl
              · exact hmin d hd2 hdk hdn
              · exact hd hdn
            have ih := facAux_correct fuel (k+1) n (by omega) (by omega) hmin2
            rcases ih with ⟨hprod, hprime, hsort, hge⟩
            constructor
            · simpa [facAux, hnlt, hs, hd] using hprod
            constructor
            · simpa [facAux, hnlt, hs, hd] using hprime
            constructor
            · simpa [facAux, hnlt, hs, hd] using hsort
            · intro p hp
              have hp' : p ∈ facAux fuel (k+1) n := by simpa [facAux, hnlt, hs, hd] using hp
              exact le_trans (Nat.le_succ k) (hge p hp')


abbrev fastFactors (n : ℕ) : List ℕ := facAux n 2 n

private def concatValOrig (l : List ℕ) : ℕ :=
  l.foldl (fun acc factor => acc * 10 ^ (Nat.digits 10 factor).length + factor) 0

private def concatValLog (l : List ℕ) : ℕ :=
  l.foldl (fun acc factor => acc * 10 ^ (Nat.log 10 factor + 1) + factor) 0

private lemma primeFactorsList_eq_of_cert {n : ℕ} {l : List ℕ}
    (hprod : l.prod = n) (hprime : ∀ p ∈ l, Nat.Prime p) (hsort : l.SortedLE) :
    n.primeFactorsList = l := by
  have hp : l ~ n.primeFactorsList := Nat.primeFactorsList_unique hprod hprime
  exact (List.Perm.eq_of_sortedLE hsort (Nat.primeFactorsList_sorted n) hp).symm

private lemma fastFactors_eq_primeFactorsList (n : ℕ) : n.primeFactorsList = fastFactors n := by
  by_cases hn : n < 2
  · interval_cases n <;> simp [fastFactors, facAux]
  · have hc := facAux_correct n 2 n (by omega) (by omega) (by intro d hd2 hdk; omega)
    rcases hc with ⟨hprod, hprime, hsort, hge⟩
    apply primeFactorsList_eq_of_cert
    · simpa [hn, fastFactors] using hprod
    · simpa [fastFactors] using hprime
    · simpa [fastFactors] using hsort

private lemma concatVal_eq_log_aux : ∀ (l : List ℕ) (acc : ℕ),
    (∀ p ∈ l, p ≠ 0) →
    l.foldl (fun acc factor => acc * 10 ^ (Nat.digits 10 factor).length + factor) acc =
    l.foldl (fun acc factor => acc * 10 ^ (Nat.log 10 factor + 1) + factor) acc
  | [], acc, h => rfl
  | x :: xs, acc, h => by
      have hx : x ≠ 0 := h x (by simp)
      have hxs : ∀ p ∈ xs, p ≠ 0 := by intro p hp; exact h p (by simp [hp])
      simp only [List.foldl_cons]
      rw [Nat.digits_len 10 x (by norm_num) hx]
      exact concatVal_eq_log_aux xs _ hxs

private lemma concatVal_eq_log (l : List ℕ) (h : ∀ p ∈ l, p ≠ 0) :
    concatValOrig l = concatValLog l := by
  exact concatVal_eq_log_aux l 0 h

abbrev fastA (n : ℕ) : ℕ := if n < 2 then 0 else concatValLog (fastFactors n) % n

private lemma a_eq_fastA (n : ℕ) : a n = fastA n := by
  by_cases hn : n < 2
  · simp [a, fastA, hn]
  · rw [a]
    simp only [hn, ↓reduceIte]
    rw [fastFactors_eq_primeFactorsList n]
    have hc := facAux_correct n 2 n (by omega) (by omega) (by intro d hd2 hdk; omega)
    rcases hc with ⟨hprod, hprime, hsort, hge⟩
    have hpos : ∀ p ∈ fastFactors n, p ≠ 0 := by
      intro p hp
      exact (hprime p (by simpa [fastFactors] using hp)).ne_zero
    change concatValOrig (fastFactors n) % n = fastA n
    rw [concatVal_eq_log (fastFactors n) hpos]
    simp [fastA, hn]


private lemma fastFactors_length_gt_one_of_composite {n : ℕ} (hc : ¬ Nat.Prime n ∧ 1 < n) :
    1 < (fastFactors n).length := by
  rw [← fastFactors_eq_primeFactorsList n]
  cases hlist : n.primeFactorsList with
  | nil =>
      have : n = 0 ∨ n = 1 := (Nat.primeFactorsList_eq_nil n).1 hlist
      omega
  | cons p t =>
      cases t with
      | nil =>
          have hp : Nat.Prime p := Nat.prime_of_mem_primeFactorsList (by rw [hlist]; simp)
          have hprod := Nat.prod_primeFactorsList (n := n) (by omega)
          rw [hlist] at hprod
          simp at hprod
          have hnprime : Nat.Prime n := by simpa [hprod] using hp
          exact False.elim (hc.1 hnprime)
      | cons q u =>
          simp


private theorem fast_no_zero_0_19 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 0)).length → fastA (i.val + 0) ≠ 0 := by
  decide

private theorem fast_no_zero_20_39 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 20)).length → fastA (i.val + 20) ≠ 0 := by
  decide

private theorem fast_no_zero_40_59 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 40)).length → fastA (i.val + 40) ≠ 0 := by
  decide

private theorem fast_no_zero_60_79 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 60)).length → fastA (i.val + 60) ≠ 0 := by
  decide

private theorem fast_no_zero_80_99 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 80)).length → fastA (i.val + 80) ≠ 0 := by
  decide

private theorem fast_no_zero_100_119 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 100)).length → fastA (i.val + 100) ≠ 0 := by
  decide

private theorem fast_no_zero_120_139 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 120)).length → fastA (i.val + 120) ≠ 0 := by
  decide

private theorem fast_no_zero_140_159 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 140)).length → fastA (i.val + 140) ≠ 0 := by
  decide

private theorem fast_no_zero_160_179 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 160)).length → fastA (i.val + 160) ≠ 0 := by
  decide

private theorem fast_no_zero_180_199 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 180)).length → fastA (i.val + 180) ≠ 0 := by
  decide

private theorem fast_no_zero_200_219 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 200)).length → fastA (i.val + 200) ≠ 0 := by
  decide

private theorem fast_no_zero_220_239 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 220)).length → fastA (i.val + 220) ≠ 0 := by
  decide

private theorem fast_no_zero_240_259 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 240)).length → fastA (i.val + 240) ≠ 0 := by
  decide

private theorem fast_no_zero_260_279 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 260)).length → fastA (i.val + 260) ≠ 0 := by
  decide

private theorem fast_no_zero_280_299 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 280)).length → fastA (i.val + 280) ≠ 0 := by
  decide

private theorem fast_no_zero_300_319 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 300)).length → fastA (i.val + 300) ≠ 0 := by
  decide

private theorem fast_no_zero_320_339 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 320)).length → fastA (i.val + 320) ≠ 0 := by
  decide

private theorem fast_no_zero_340_359 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 340)).length → fastA (i.val + 340) ≠ 0 := by
  decide

private theorem fast_no_zero_360_379 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 360)).length → fastA (i.val + 360) ≠ 0 := by
  decide

private theorem fast_no_zero_380_399 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 380)).length → fastA (i.val + 380) ≠ 0 := by
  decide

private theorem fast_no_zero_400_419 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 400)).length → fastA (i.val + 400) ≠ 0 := by
  decide

private theorem fast_no_zero_420_439 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 420)).length → fastA (i.val + 420) ≠ 0 := by
  decide

private theorem fast_no_zero_440_459 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 440)).length → fastA (i.val + 440) ≠ 0 := by
  decide

private theorem fast_no_zero_460_479 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 460)).length → fastA (i.val + 460) ≠ 0 := by
  decide

private theorem fast_no_zero_480_499 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 480)).length → fastA (i.val + 480) ≠ 0 := by
  decide

private theorem fast_no_zero_500_519 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 500)).length → fastA (i.val + 500) ≠ 0 := by
  decide

private theorem fast_no_zero_520_539 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 520)).length → fastA (i.val + 520) ≠ 0 := by
  decide

private theorem fast_no_zero_540_559 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 540)).length → fastA (i.val + 540) ≠ 0 := by
  decide

private theorem fast_no_zero_560_579 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 560)).length → fastA (i.val + 560) ≠ 0 := by
  decide

private theorem fast_no_zero_580_599 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 580)).length → fastA (i.val + 580) ≠ 0 := by
  decide

private theorem fast_no_zero_600_619 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 600)).length → fastA (i.val + 600) ≠ 0 := by
  decide

private theorem fast_no_zero_620_639 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 620)).length → fastA (i.val + 620) ≠ 0 := by
  decide

private theorem fast_no_zero_640_659 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 640)).length → fastA (i.val + 640) ≠ 0 := by
  decide

private theorem fast_no_zero_660_679 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 660)).length → fastA (i.val + 660) ≠ 0 := by
  decide

private theorem fast_no_zero_680_699 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 680)).length → fastA (i.val + 680) ≠ 0 := by
  decide

private theorem fast_no_zero_700_719 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 700)).length → fastA (i.val + 700) ≠ 0 := by
  decide

private theorem fast_no_zero_720_739 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 720)).length → fastA (i.val + 720) ≠ 0 := by
  decide

private theorem fast_no_zero_740_759 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 740)).length → fastA (i.val + 740) ≠ 0 := by
  decide

private theorem fast_no_zero_760_779 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 760)).length → fastA (i.val + 760) ≠ 0 := by
  decide

private theorem fast_no_zero_780_799 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 780)).length → fastA (i.val + 780) ≠ 0 := by
  decide

private theorem fast_no_zero_800_819 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 800)).length → fastA (i.val + 800) ≠ 0 := by
  decide

private theorem fast_no_zero_820_839 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 820)).length → fastA (i.val + 820) ≠ 0 := by
  decide

private theorem fast_no_zero_840_859 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 840)).length → fastA (i.val + 840) ≠ 0 := by
  decide

private theorem fast_no_zero_860_879 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 860)).length → fastA (i.val + 860) ≠ 0 := by
  decide

private theorem fast_no_zero_880_899 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 880)).length → fastA (i.val + 880) ≠ 0 := by
  decide

private theorem fast_no_zero_900_919 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 900)).length → fastA (i.val + 900) ≠ 0 := by
  decide

private theorem fast_no_zero_920_939 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 920)).length → fastA (i.val + 920) ≠ 0 := by
  decide

private theorem fast_no_zero_940_959 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 940)).length → fastA (i.val + 940) ≠ 0 := by
  decide

private theorem fast_no_zero_960_979 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 960)).length → fastA (i.val + 960) ≠ 0 := by
  decide

private theorem fast_no_zero_980_999 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 980)).length → fastA (i.val + 980) ≠ 0 := by
  decide

private theorem fast_no_zero_1000_1019 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 1000)).length → fastA (i.val + 1000) ≠ 0 := by
  decide

private theorem fast_no_zero_1020_1039 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 1020)).length → fastA (i.val + 1020) ≠ 0 := by
  decide

private theorem fast_no_zero_1040_1059 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 1040)).length → fastA (i.val + 1040) ≠ 0 := by
  decide

private theorem fast_no_zero_1060_1079 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 1060)).length → fastA (i.val + 1060) ≠ 0 := by
  decide

private theorem fast_no_zero_1080_1099 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 1080)).length → fastA (i.val + 1080) ≠ 0 := by
  decide

private theorem fast_no_zero_1100_1119 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 1100)).length → fastA (i.val + 1100) ≠ 0 := by
  decide

private theorem fast_no_zero_1120_1139 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 1120)).length → fastA (i.val + 1120) ≠ 0 := by
  decide

private theorem fast_no_zero_1140_1159 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 1140)).length → fastA (i.val + 1140) ≠ 0 := by
  decide

private theorem fast_no_zero_1160_1179 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 1160)).length → fastA (i.val + 1160) ≠ 0 := by
  decide

private theorem fast_no_zero_1180_1199 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 1180)).length → fastA (i.val + 1180) ≠ 0 := by
  decide

private theorem fast_no_zero_1200_1219 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 1200)).length → fastA (i.val + 1200) ≠ 0 := by
  decide

private theorem fast_no_zero_1220_1239 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 1220)).length → fastA (i.val + 1220) ≠ 0 := by
  decide

private theorem fast_no_zero_1240_1259 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 1240)).length → fastA (i.val + 1240) ≠ 0 := by
  decide

private theorem fast_no_zero_1260_1279 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 1260)).length → fastA (i.val + 1260) ≠ 0 := by
  decide

private theorem fast_no_zero_1280_1299 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 1280)).length → fastA (i.val + 1280) ≠ 0 := by
  decide

private theorem fast_no_zero_1300_1319 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 1300)).length → fastA (i.val + 1300) ≠ 0 := by
  decide

private theorem fast_no_zero_1320_1339 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 1320)).length → fastA (i.val + 1320) ≠ 0 := by
  decide

private theorem fast_no_zero_1340_1359 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 1340)).length → fastA (i.val + 1340) ≠ 0 := by
  decide

private theorem fast_no_zero_1360_1379 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 1360)).length → fastA (i.val + 1360) ≠ 0 := by
  decide

private theorem fast_no_zero_1380_1399 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 1380)).length → fastA (i.val + 1380) ≠ 0 := by
  decide

private theorem fast_no_zero_1400_1419 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 1400)).length → fastA (i.val + 1400) ≠ 0 := by
  decide

private theorem fast_no_zero_1420_1439 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 1420)).length → fastA (i.val + 1420) ≠ 0 := by
  decide

private theorem fast_no_zero_1440_1459 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 1440)).length → fastA (i.val + 1440) ≠ 0 := by
  decide

private theorem fast_no_zero_1460_1479 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 1460)).length → fastA (i.val + 1460) ≠ 0 := by
  decide

private theorem fast_no_zero_1480_1499 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 1480)).length → fastA (i.val + 1480) ≠ 0 := by
  decide

private theorem fast_no_zero_1500_1519 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 1500)).length → fastA (i.val + 1500) ≠ 0 := by
  decide

private theorem fast_no_zero_1520_1539 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 1520)).length → fastA (i.val + 1520) ≠ 0 := by
  decide

private theorem fast_no_zero_1540_1559 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 1540)).length → fastA (i.val + 1540) ≠ 0 := by
  decide

private theorem fast_no_zero_1560_1579 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 1560)).length → fastA (i.val + 1560) ≠ 0 := by
  decide

private theorem fast_no_zero_1580_1599 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 1580)).length → fastA (i.val + 1580) ≠ 0 := by
  decide

private theorem fast_no_zero_1600_1619 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 1600)).length → fastA (i.val + 1600) ≠ 0 := by
  decide

private theorem fast_no_zero_1620_1639 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 1620)).length → fastA (i.val + 1620) ≠ 0 := by
  decide

private theorem fast_no_zero_1640_1659 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 1640)).length → fastA (i.val + 1640) ≠ 0 := by
  decide

private theorem fast_no_zero_1660_1679 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 1660)).length → fastA (i.val + 1660) ≠ 0 := by
  decide

private theorem fast_no_zero_1680_1699 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 1680)).length → fastA (i.val + 1680) ≠ 0 := by
  decide

private theorem fast_no_zero_1700_1719 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 1700)).length → fastA (i.val + 1700) ≠ 0 := by
  decide

private theorem fast_no_zero_1720_1739 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 1720)).length → fastA (i.val + 1720) ≠ 0 := by
  decide

private theorem fast_no_zero_1740_1759 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 1740)).length → fastA (i.val + 1740) ≠ 0 := by
  decide

private theorem fast_no_zero_1760_1779 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 1760)).length → fastA (i.val + 1760) ≠ 0 := by
  decide

private theorem fast_no_zero_1780_1799 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 1780)).length → fastA (i.val + 1780) ≠ 0 := by
  decide

private theorem fast_no_zero_1800_1819 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 1800)).length → fastA (i.val + 1800) ≠ 0 := by
  decide

private theorem fast_no_zero_1820_1839 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 1820)).length → fastA (i.val + 1820) ≠ 0 := by
  decide

private theorem fast_no_zero_1840_1859 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 1840)).length → fastA (i.val + 1840) ≠ 0 := by
  decide

private theorem fast_no_zero_1860_1879 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 1860)).length → fastA (i.val + 1860) ≠ 0 := by
  decide

private theorem fast_no_zero_1880_1899 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 1880)).length → fastA (i.val + 1880) ≠ 0 := by
  decide

private theorem fast_no_zero_1900_1919 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 1900)).length → fastA (i.val + 1900) ≠ 0 := by
  decide

private theorem fast_no_zero_1920_1939 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 1920)).length → fastA (i.val + 1920) ≠ 0 := by
  decide

private theorem fast_no_zero_1940_1959 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 1940)).length → fastA (i.val + 1940) ≠ 0 := by
  decide

private theorem fast_no_zero_1960_1979 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 1960)).length → fastA (i.val + 1960) ≠ 0 := by
  decide

private theorem fast_no_zero_1980_1999 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 1980)).length → fastA (i.val + 1980) ≠ 0 := by
  decide

private theorem fast_no_zero_2000_2019 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 2000)).length → fastA (i.val + 2000) ≠ 0 := by
  decide

private theorem fast_no_zero_2020_2039 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 2020)).length → fastA (i.val + 2020) ≠ 0 := by
  decide

private theorem fast_no_zero_2040_2059 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 2040)).length → fastA (i.val + 2040) ≠ 0 := by
  decide

private theorem fast_no_zero_2060_2079 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 2060)).length → fastA (i.val + 2060) ≠ 0 := by
  decide

private theorem fast_no_zero_2080_2099 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 2080)).length → fastA (i.val + 2080) ≠ 0 := by
  decide

private theorem fast_no_zero_2100_2119 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 2100)).length → fastA (i.val + 2100) ≠ 0 := by
  decide

private theorem fast_no_zero_2120_2139 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 2120)).length → fastA (i.val + 2120) ≠ 0 := by
  decide

private theorem fast_no_zero_2140_2159 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 2140)).length → fastA (i.val + 2140) ≠ 0 := by
  decide

private theorem fast_no_zero_2160_2179 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 2160)).length → fastA (i.val + 2160) ≠ 0 := by
  decide

private theorem fast_no_zero_2180_2199 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 2180)).length → fastA (i.val + 2180) ≠ 0 := by
  decide

private theorem fast_no_zero_2200_2219 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 2200)).length → fastA (i.val + 2200) ≠ 0 := by
  decide

private theorem fast_no_zero_2220_2239 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 2220)).length → fastA (i.val + 2220) ≠ 0 := by
  decide

private theorem fast_no_zero_2240_2259 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 2240)).length → fastA (i.val + 2240) ≠ 0 := by
  decide

private theorem fast_no_zero_2260_2279 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 2260)).length → fastA (i.val + 2260) ≠ 0 := by
  decide

private theorem fast_no_zero_2280_2299 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 2280)).length → fastA (i.val + 2280) ≠ 0 := by
  decide

private theorem fast_no_zero_2300_2319 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 2300)).length → fastA (i.val + 2300) ≠ 0 := by
  decide

private theorem fast_no_zero_2320_2339 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 2320)).length → fastA (i.val + 2320) ≠ 0 := by
  decide

private theorem fast_no_zero_2340_2359 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 2340)).length → fastA (i.val + 2340) ≠ 0 := by
  decide

private theorem fast_no_zero_2360_2379 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 2360)).length → fastA (i.val + 2360) ≠ 0 := by
  decide

private theorem fast_no_zero_2380_2399 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 2380)).length → fastA (i.val + 2380) ≠ 0 := by
  decide

private theorem fast_no_zero_2400_2419 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 2400)).length → fastA (i.val + 2400) ≠ 0 := by
  decide

private theorem fast_no_zero_2420_2439 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 2420)).length → fastA (i.val + 2420) ≠ 0 := by
  decide

private theorem fast_no_zero_2440_2459 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 2440)).length → fastA (i.val + 2440) ≠ 0 := by
  decide

private theorem fast_no_zero_2460_2479 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 2460)).length → fastA (i.val + 2460) ≠ 0 := by
  decide

private theorem fast_no_zero_2480_2499 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 2480)).length → fastA (i.val + 2480) ≠ 0 := by
  decide

private theorem fast_no_zero_2500_2519 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 2500)).length → fastA (i.val + 2500) ≠ 0 := by
  decide

private theorem fast_no_zero_2520_2539 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 2520)).length → fastA (i.val + 2520) ≠ 0 := by
  decide

private theorem fast_no_zero_2540_2559 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 2540)).length → fastA (i.val + 2540) ≠ 0 := by
  decide

private theorem fast_no_zero_2560_2579 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 2560)).length → fastA (i.val + 2560) ≠ 0 := by
  decide

private theorem fast_no_zero_2580_2599 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 2580)).length → fastA (i.val + 2580) ≠ 0 := by
  decide

private theorem fast_no_zero_2600_2619 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 2600)).length → fastA (i.val + 2600) ≠ 0 := by
  decide

private theorem fast_no_zero_2620_2639 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 2620)).length → fastA (i.val + 2620) ≠ 0 := by
  decide

private theorem fast_no_zero_2640_2659 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 2640)).length → fastA (i.val + 2640) ≠ 0 := by
  decide

private theorem fast_no_zero_2660_2679 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 2660)).length → fastA (i.val + 2660) ≠ 0 := by
  decide

private theorem fast_no_zero_2680_2699 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 2680)).length → fastA (i.val + 2680) ≠ 0 := by
  decide

private theorem fast_no_zero_2700_2719 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 2700)).length → fastA (i.val + 2700) ≠ 0 := by
  decide

private theorem fast_no_zero_2720_2739 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 2720)).length → fastA (i.val + 2720) ≠ 0 := by
  decide

private theorem fast_no_zero_2740_2759 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 2740)).length → fastA (i.val + 2740) ≠ 0 := by
  decide

private theorem fast_no_zero_2760_2779 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 2760)).length → fastA (i.val + 2760) ≠ 0 := by
  decide

private theorem fast_no_zero_2780_2799 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 2780)).length → fastA (i.val + 2780) ≠ 0 := by
  decide

private theorem fast_no_zero_2800_2819 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 2800)).length → fastA (i.val + 2800) ≠ 0 := by
  decide

private theorem fast_no_zero_2820_2839 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 2820)).length → fastA (i.val + 2820) ≠ 0 := by
  decide

private theorem fast_no_zero_2840_2859 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 2840)).length → fastA (i.val + 2840) ≠ 0 := by
  decide

private theorem fast_no_zero_2860_2879 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 2860)).length → fastA (i.val + 2860) ≠ 0 := by
  decide

private theorem fast_no_zero_2880_2899 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 2880)).length → fastA (i.val + 2880) ≠ 0 := by
  decide

private theorem fast_no_zero_2900_2919 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 2900)).length → fastA (i.val + 2900) ≠ 0 := by
  decide

private theorem fast_no_zero_2920_2939 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 2920)).length → fastA (i.val + 2920) ≠ 0 := by
  decide

private theorem fast_no_zero_2940_2959 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 2940)).length → fastA (i.val + 2940) ≠ 0 := by
  decide

private theorem fast_no_zero_2960_2979 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 2960)).length → fastA (i.val + 2960) ≠ 0 := by
  decide

private theorem fast_no_zero_2980_2999 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 2980)).length → fastA (i.val + 2980) ≠ 0 := by
  decide

private theorem fast_no_zero_3000_3019 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 3000)).length → fastA (i.val + 3000) ≠ 0 := by
  decide

private theorem fast_no_zero_3020_3039 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 3020)).length → fastA (i.val + 3020) ≠ 0 := by
  decide

private theorem fast_no_zero_3040_3059 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 3040)).length → fastA (i.val + 3040) ≠ 0 := by
  decide

private theorem fast_no_zero_3060_3079 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 3060)).length → fastA (i.val + 3060) ≠ 0 := by
  decide

private theorem fast_no_zero_3080_3099 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 3080)).length → fastA (i.val + 3080) ≠ 0 := by
  decide

private theorem fast_no_zero_3100_3119 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 3100)).length → fastA (i.val + 3100) ≠ 0 := by
  decide

private theorem fast_no_zero_3120_3139 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 3120)).length → fastA (i.val + 3120) ≠ 0 := by
  decide

private theorem fast_no_zero_3140_3159 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 3140)).length → fastA (i.val + 3140) ≠ 0 := by
  decide

private theorem fast_no_zero_3160_3179 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 3160)).length → fastA (i.val + 3160) ≠ 0 := by
  decide

private theorem fast_no_zero_3180_3199 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 3180)).length → fastA (i.val + 3180) ≠ 0 := by
  decide

private theorem fast_no_zero_3200_3219 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 3200)).length → fastA (i.val + 3200) ≠ 0 := by
  decide

private theorem fast_no_zero_3220_3239 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 3220)).length → fastA (i.val + 3220) ≠ 0 := by
  decide

private theorem fast_no_zero_3240_3259 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 3240)).length → fastA (i.val + 3240) ≠ 0 := by
  decide

private theorem fast_no_zero_3260_3279 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 3260)).length → fastA (i.val + 3260) ≠ 0 := by
  decide

private theorem fast_no_zero_3280_3299 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 3280)).length → fastA (i.val + 3280) ≠ 0 := by
  decide

private theorem fast_no_zero_3300_3319 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 3300)).length → fastA (i.val + 3300) ≠ 0 := by
  decide

private theorem fast_no_zero_3320_3339 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 3320)).length → fastA (i.val + 3320) ≠ 0 := by
  decide

private theorem fast_no_zero_3340_3359 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 3340)).length → fastA (i.val + 3340) ≠ 0 := by
  decide

private theorem fast_no_zero_3360_3379 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 3360)).length → fastA (i.val + 3360) ≠ 0 := by
  decide

private theorem fast_no_zero_3380_3399 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 3380)).length → fastA (i.val + 3380) ≠ 0 := by
  decide

private theorem fast_no_zero_3400_3419 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 3400)).length → fastA (i.val + 3400) ≠ 0 := by
  decide

private theorem fast_no_zero_3420_3439 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 3420)).length → fastA (i.val + 3420) ≠ 0 := by
  decide

private theorem fast_no_zero_3440_3459 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 3440)).length → fastA (i.val + 3440) ≠ 0 := by
  decide

private theorem fast_no_zero_3460_3479 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 3460)).length → fastA (i.val + 3460) ≠ 0 := by
  decide

private theorem fast_no_zero_3480_3499 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 3480)).length → fastA (i.val + 3480) ≠ 0 := by
  decide

private theorem fast_no_zero_3500_3519 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 3500)).length → fastA (i.val + 3500) ≠ 0 := by
  decide

private theorem fast_no_zero_3520_3539 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 3520)).length → fastA (i.val + 3520) ≠ 0 := by
  decide

private theorem fast_no_zero_3540_3559 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 3540)).length → fastA (i.val + 3540) ≠ 0 := by
  decide

private theorem fast_no_zero_3560_3579 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 3560)).length → fastA (i.val + 3560) ≠ 0 := by
  decide

private theorem fast_no_zero_3580_3599 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 3580)).length → fastA (i.val + 3580) ≠ 0 := by
  decide

private theorem fast_no_zero_3600_3619 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 3600)).length → fastA (i.val + 3600) ≠ 0 := by
  decide

private theorem fast_no_zero_3620_3639 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 3620)).length → fastA (i.val + 3620) ≠ 0 := by
  decide

private theorem fast_no_zero_3640_3659 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 3640)).length → fastA (i.val + 3640) ≠ 0 := by
  decide

private theorem fast_no_zero_3660_3679 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 3660)).length → fastA (i.val + 3660) ≠ 0 := by
  decide

private theorem fast_no_zero_3680_3699 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 3680)).length → fastA (i.val + 3680) ≠ 0 := by
  decide

private theorem fast_no_zero_3700_3719 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 3700)).length → fastA (i.val + 3700) ≠ 0 := by
  decide

private theorem fast_no_zero_3720_3739 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 3720)).length → fastA (i.val + 3720) ≠ 0 := by
  decide

private theorem fast_no_zero_3740_3759 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 3740)).length → fastA (i.val + 3740) ≠ 0 := by
  decide

private theorem fast_no_zero_3760_3779 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 3760)).length → fastA (i.val + 3760) ≠ 0 := by
  decide

private theorem fast_no_zero_3780_3799 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 3780)).length → fastA (i.val + 3780) ≠ 0 := by
  decide

private theorem fast_no_zero_3800_3819 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 3800)).length → fastA (i.val + 3800) ≠ 0 := by
  decide

private theorem fast_no_zero_3820_3839 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 3820)).length → fastA (i.val + 3820) ≠ 0 := by
  decide

private theorem fast_no_zero_3840_3859 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 3840)).length → fastA (i.val + 3840) ≠ 0 := by
  decide

private theorem fast_no_zero_3860_3879 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 3860)).length → fastA (i.val + 3860) ≠ 0 := by
  decide

private theorem fast_no_zero_3880_3899 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 3880)).length → fastA (i.val + 3880) ≠ 0 := by
  decide

private theorem fast_no_zero_3900_3919 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 3900)).length → fastA (i.val + 3900) ≠ 0 := by
  decide

private theorem fast_no_zero_3920_3939 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 3920)).length → fastA (i.val + 3920) ≠ 0 := by
  decide

private theorem fast_no_zero_3940_3959 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 3940)).length → fastA (i.val + 3940) ≠ 0 := by
  decide

private theorem fast_no_zero_3960_3979 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 3960)).length → fastA (i.val + 3960) ≠ 0 := by
  decide

private theorem fast_no_zero_3980_3999 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 3980)).length → fastA (i.val + 3980) ≠ 0 := by
  decide

private theorem fast_no_zero_4000_4019 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 4000)).length → fastA (i.val + 4000) ≠ 0 := by
  decide

private theorem fast_no_zero_4020_4039 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 4020)).length → fastA (i.val + 4020) ≠ 0 := by
  decide

private theorem fast_no_zero_4040_4059 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 4040)).length → fastA (i.val + 4040) ≠ 0 := by
  decide

private theorem fast_no_zero_4060_4079 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 4060)).length → fastA (i.val + 4060) ≠ 0 := by
  decide

private theorem fast_no_zero_4080_4099 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 4080)).length → fastA (i.val + 4080) ≠ 0 := by
  decide

private theorem fast_no_zero_4100_4119 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 4100)).length → fastA (i.val + 4100) ≠ 0 := by
  decide

private theorem fast_no_zero_4120_4139 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 4120)).length → fastA (i.val + 4120) ≠ 0 := by
  decide

private theorem fast_no_zero_4140_4159 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 4140)).length → fastA (i.val + 4140) ≠ 0 := by
  decide

private theorem fast_no_zero_4160_4179 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 4160)).length → fastA (i.val + 4160) ≠ 0 := by
  decide

private theorem fast_no_zero_4180_4199 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 4180)).length → fastA (i.val + 4180) ≠ 0 := by
  decide

private theorem fast_no_zero_4200_4219 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 4200)).length → fastA (i.val + 4200) ≠ 0 := by
  decide

private theorem fast_no_zero_4220_4239 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 4220)).length → fastA (i.val + 4220) ≠ 0 := by
  decide

private theorem fast_no_zero_4240_4259 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 4240)).length → fastA (i.val + 4240) ≠ 0 := by
  decide

private theorem fast_no_zero_4260_4279 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 4260)).length → fastA (i.val + 4260) ≠ 0 := by
  decide

private theorem fast_no_zero_4280_4299 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 4280)).length → fastA (i.val + 4280) ≠ 0 := by
  decide

private theorem fast_no_zero_4300_4319 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 4300)).length → fastA (i.val + 4300) ≠ 0 := by
  decide

private theorem fast_no_zero_4320_4339 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 4320)).length → fastA (i.val + 4320) ≠ 0 := by
  decide

private theorem fast_no_zero_4340_4359 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 4340)).length → fastA (i.val + 4340) ≠ 0 := by
  decide

private theorem fast_no_zero_4360_4379 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 4360)).length → fastA (i.val + 4360) ≠ 0 := by
  decide

private theorem fast_no_zero_4380_4399 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 4380)).length → fastA (i.val + 4380) ≠ 0 := by
  decide

private theorem fast_no_zero_4400_4419 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 4400)).length → fastA (i.val + 4400) ≠ 0 := by
  decide

private theorem fast_no_zero_4420_4439 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 4420)).length → fastA (i.val + 4420) ≠ 0 := by
  decide

private theorem fast_no_zero_4440_4459 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 4440)).length → fastA (i.val + 4440) ≠ 0 := by
  decide

private theorem fast_no_zero_4460_4479 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 4460)).length → fastA (i.val + 4460) ≠ 0 := by
  decide

private theorem fast_no_zero_4480_4499 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 4480)).length → fastA (i.val + 4480) ≠ 0 := by
  decide

private theorem fast_no_zero_4500_4519 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 4500)).length → fastA (i.val + 4500) ≠ 0 := by
  decide

private theorem fast_no_zero_4520_4539 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 4520)).length → fastA (i.val + 4520) ≠ 0 := by
  decide

private theorem fast_no_zero_4540_4559 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 4540)).length → fastA (i.val + 4540) ≠ 0 := by
  decide

private theorem fast_no_zero_4560_4579 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 4560)).length → fastA (i.val + 4560) ≠ 0 := by
  decide

private theorem fast_no_zero_4580_4599 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 4580)).length → fastA (i.val + 4580) ≠ 0 := by
  decide

private theorem fast_no_zero_4600_4619 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 4600)).length → fastA (i.val + 4600) ≠ 0 := by
  decide

private theorem fast_no_zero_4620_4639 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 4620)).length → fastA (i.val + 4620) ≠ 0 := by
  decide

private theorem fast_no_zero_4640_4659 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 4640)).length → fastA (i.val + 4640) ≠ 0 := by
  decide

private theorem fast_no_zero_4660_4679 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 4660)).length → fastA (i.val + 4660) ≠ 0 := by
  decide

private theorem fast_no_zero_4680_4699 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 4680)).length → fastA (i.val + 4680) ≠ 0 := by
  decide

private theorem fast_no_zero_4700_4719 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 4700)).length → fastA (i.val + 4700) ≠ 0 := by
  decide

private theorem fast_no_zero_4720_4739 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 4720)).length → fastA (i.val + 4720) ≠ 0 := by
  decide

private theorem fast_no_zero_4740_4759 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 4740)).length → fastA (i.val + 4740) ≠ 0 := by
  decide

private theorem fast_no_zero_4760_4779 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 4760)).length → fastA (i.val + 4760) ≠ 0 := by
  decide

private theorem fast_no_zero_4780_4799 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 4780)).length → fastA (i.val + 4780) ≠ 0 := by
  decide

private theorem fast_no_zero_4800_4819 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 4800)).length → fastA (i.val + 4800) ≠ 0 := by
  decide

private theorem fast_no_zero_4820_4839 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 4820)).length → fastA (i.val + 4820) ≠ 0 := by
  decide

private theorem fast_no_zero_4840_4859 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 4840)).length → fastA (i.val + 4840) ≠ 0 := by
  decide

private theorem fast_no_zero_4860_4879 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 4860)).length → fastA (i.val + 4860) ≠ 0 := by
  decide

private theorem fast_no_zero_4880_4899 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 4880)).length → fastA (i.val + 4880) ≠ 0 := by
  decide

private theorem fast_no_zero_4900_4919 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 4900)).length → fastA (i.val + 4900) ≠ 0 := by
  decide

private theorem fast_no_zero_4920_4939 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 4920)).length → fastA (i.val + 4920) ≠ 0 := by
  decide

private theorem fast_no_zero_4940_4959 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 4940)).length → fastA (i.val + 4940) ≠ 0 := by
  decide

private theorem fast_no_zero_4960_4979 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 4960)).length → fastA (i.val + 4960) ≠ 0 := by
  decide

private theorem fast_no_zero_4980_4999 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 4980)).length → fastA (i.val + 4980) ≠ 0 := by
  decide

private theorem fast_no_zero_5000_5019 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 5000)).length → fastA (i.val + 5000) ≠ 0 := by
  decide

private theorem fast_no_zero_5020_5039 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 5020)).length → fastA (i.val + 5020) ≠ 0 := by
  decide

private theorem fast_no_zero_5040_5059 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 5040)).length → fastA (i.val + 5040) ≠ 0 := by
  decide

private theorem fast_no_zero_5060_5079 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 5060)).length → fastA (i.val + 5060) ≠ 0 := by
  decide

private theorem fast_no_zero_5080_5099 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 5080)).length → fastA (i.val + 5080) ≠ 0 := by
  decide

private theorem fast_no_zero_5100_5119 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 5100)).length → fastA (i.val + 5100) ≠ 0 := by
  decide

private theorem fast_no_zero_5120_5139 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 5120)).length → fastA (i.val + 5120) ≠ 0 := by
  decide

private theorem fast_no_zero_5140_5159 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 5140)).length → fastA (i.val + 5140) ≠ 0 := by
  decide

private theorem fast_no_zero_5160_5179 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 5160)).length → fastA (i.val + 5160) ≠ 0 := by
  decide

private theorem fast_no_zero_5180_5199 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 5180)).length → fastA (i.val + 5180) ≠ 0 := by
  decide

private theorem fast_no_zero_5200_5219 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 5200)).length → fastA (i.val + 5200) ≠ 0 := by
  decide

private theorem fast_no_zero_5220_5239 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 5220)).length → fastA (i.val + 5220) ≠ 0 := by
  decide

private theorem fast_no_zero_5240_5259 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 5240)).length → fastA (i.val + 5240) ≠ 0 := by
  decide

private theorem fast_no_zero_5260_5279 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 5260)).length → fastA (i.val + 5260) ≠ 0 := by
  decide

private theorem fast_no_zero_5280_5299 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 5280)).length → fastA (i.val + 5280) ≠ 0 := by
  decide

private theorem fast_no_zero_5300_5319 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 5300)).length → fastA (i.val + 5300) ≠ 0 := by
  decide

private theorem fast_no_zero_5320_5339 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 5320)).length → fastA (i.val + 5320) ≠ 0 := by
  decide

private theorem fast_no_zero_5340_5359 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 5340)).length → fastA (i.val + 5340) ≠ 0 := by
  decide

private theorem fast_no_zero_5360_5379 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 5360)).length → fastA (i.val + 5360) ≠ 0 := by
  decide

private theorem fast_no_zero_5380_5399 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 5380)).length → fastA (i.val + 5380) ≠ 0 := by
  decide

private theorem fast_no_zero_5400_5419 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 5400)).length → fastA (i.val + 5400) ≠ 0 := by
  decide

private theorem fast_no_zero_5420_5439 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 5420)).length → fastA (i.val + 5420) ≠ 0 := by
  decide

private theorem fast_no_zero_5440_5459 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 5440)).length → fastA (i.val + 5440) ≠ 0 := by
  decide

private theorem fast_no_zero_5460_5479 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 5460)).length → fastA (i.val + 5460) ≠ 0 := by
  decide

private theorem fast_no_zero_5480_5499 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 5480)).length → fastA (i.val + 5480) ≠ 0 := by
  decide

private theorem fast_no_zero_5500_5519 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 5500)).length → fastA (i.val + 5500) ≠ 0 := by
  decide

private theorem fast_no_zero_5520_5539 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 5520)).length → fastA (i.val + 5520) ≠ 0 := by
  decide

private theorem fast_no_zero_5540_5559 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 5540)).length → fastA (i.val + 5540) ≠ 0 := by
  decide

private theorem fast_no_zero_5560_5579 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 5560)).length → fastA (i.val + 5560) ≠ 0 := by
  decide

private theorem fast_no_zero_5580_5599 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 5580)).length → fastA (i.val + 5580) ≠ 0 := by
  decide

private theorem fast_no_zero_5600_5619 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 5600)).length → fastA (i.val + 5600) ≠ 0 := by
  decide

private theorem fast_no_zero_5620_5639 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 5620)).length → fastA (i.val + 5620) ≠ 0 := by
  decide

private theorem fast_no_zero_5640_5659 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 5640)).length → fastA (i.val + 5640) ≠ 0 := by
  decide

private theorem fast_no_zero_5660_5679 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 5660)).length → fastA (i.val + 5660) ≠ 0 := by
  decide

private theorem fast_no_zero_5680_5699 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 5680)).length → fastA (i.val + 5680) ≠ 0 := by
  decide

private theorem fast_no_zero_5700_5719 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 5700)).length → fastA (i.val + 5700) ≠ 0 := by
  decide

private theorem fast_no_zero_5720_5739 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 5720)).length → fastA (i.val + 5720) ≠ 0 := by
  decide

private theorem fast_no_zero_5740_5759 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 5740)).length → fastA (i.val + 5740) ≠ 0 := by
  decide

private theorem fast_no_zero_5760_5779 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 5760)).length → fastA (i.val + 5760) ≠ 0 := by
  decide

private theorem fast_no_zero_5780_5799 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 5780)).length → fastA (i.val + 5780) ≠ 0 := by
  decide

private theorem fast_no_zero_5800_5819 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 5800)).length → fastA (i.val + 5800) ≠ 0 := by
  decide

private theorem fast_no_zero_5820_5839 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 5820)).length → fastA (i.val + 5820) ≠ 0 := by
  decide

private theorem fast_no_zero_5840_5859 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 5840)).length → fastA (i.val + 5840) ≠ 0 := by
  decide

private theorem fast_no_zero_5860_5879 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 5860)).length → fastA (i.val + 5860) ≠ 0 := by
  decide

private theorem fast_no_zero_5880_5899 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 5880)).length → fastA (i.val + 5880) ≠ 0 := by
  decide

private theorem fast_no_zero_5900_5919 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 5900)).length → fastA (i.val + 5900) ≠ 0 := by
  decide

private theorem fast_no_zero_5920_5939 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 5920)).length → fastA (i.val + 5920) ≠ 0 := by
  decide

private theorem fast_no_zero_5940_5959 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 5940)).length → fastA (i.val + 5940) ≠ 0 := by
  decide

private theorem fast_no_zero_5960_5979 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 5960)).length → fastA (i.val + 5960) ≠ 0 := by
  decide

private theorem fast_no_zero_5980_5999 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 5980)).length → fastA (i.val + 5980) ≠ 0 := by
  decide

private theorem fast_no_zero_6000_6019 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 6000)).length → fastA (i.val + 6000) ≠ 0 := by
  decide

private theorem fast_no_zero_6020_6039 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 6020)).length → fastA (i.val + 6020) ≠ 0 := by
  decide

private theorem fast_no_zero_6040_6059 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 6040)).length → fastA (i.val + 6040) ≠ 0 := by
  decide

private theorem fast_no_zero_6060_6079 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 6060)).length → fastA (i.val + 6060) ≠ 0 := by
  decide

private theorem fast_no_zero_6080_6099 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 6080)).length → fastA (i.val + 6080) ≠ 0 := by
  decide

private theorem fast_no_zero_6100_6119 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 6100)).length → fastA (i.val + 6100) ≠ 0 := by
  decide

private theorem fast_no_zero_6120_6139 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 6120)).length → fastA (i.val + 6120) ≠ 0 := by
  decide

private theorem fast_no_zero_6140_6159 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 6140)).length → fastA (i.val + 6140) ≠ 0 := by
  decide

private theorem fast_no_zero_6160_6179 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 6160)).length → fastA (i.val + 6160) ≠ 0 := by
  decide

private theorem fast_no_zero_6180_6199 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 6180)).length → fastA (i.val + 6180) ≠ 0 := by
  decide

private theorem fast_no_zero_6200_6219 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 6200)).length → fastA (i.val + 6200) ≠ 0 := by
  decide

private theorem fast_no_zero_6220_6239 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 6220)).length → fastA (i.val + 6220) ≠ 0 := by
  decide

private theorem fast_no_zero_6240_6259 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 6240)).length → fastA (i.val + 6240) ≠ 0 := by
  decide

private theorem fast_no_zero_6260_6279 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 6260)).length → fastA (i.val + 6260) ≠ 0 := by
  decide

private theorem fast_no_zero_6280_6299 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 6280)).length → fastA (i.val + 6280) ≠ 0 := by
  decide

private theorem fast_no_zero_6300_6319 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 6300)).length → fastA (i.val + 6300) ≠ 0 := by
  decide

private theorem fast_no_zero_6320_6339 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 6320)).length → fastA (i.val + 6320) ≠ 0 := by
  decide

private theorem fast_no_zero_6340_6359 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 6340)).length → fastA (i.val + 6340) ≠ 0 := by
  decide

private theorem fast_no_zero_6360_6379 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 6360)).length → fastA (i.val + 6360) ≠ 0 := by
  decide

private theorem fast_no_zero_6380_6399 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 6380)).length → fastA (i.val + 6380) ≠ 0 := by
  decide

private theorem fast_no_zero_6400_6419 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 6400)).length → fastA (i.val + 6400) ≠ 0 := by
  decide

private theorem fast_no_zero_6420_6439 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 6420)).length → fastA (i.val + 6420) ≠ 0 := by
  decide

private theorem fast_no_zero_6440_6459 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 6440)).length → fastA (i.val + 6440) ≠ 0 := by
  decide

private theorem fast_no_zero_6460_6479 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 6460)).length → fastA (i.val + 6460) ≠ 0 := by
  decide

private theorem fast_no_zero_6480_6499 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 6480)).length → fastA (i.val + 6480) ≠ 0 := by
  decide

private theorem fast_no_zero_6500_6519 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 6500)).length → fastA (i.val + 6500) ≠ 0 := by
  decide

private theorem fast_no_zero_6520_6539 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 6520)).length → fastA (i.val + 6520) ≠ 0 := by
  decide

private theorem fast_no_zero_6540_6559 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 6540)).length → fastA (i.val + 6540) ≠ 0 := by
  decide

private theorem fast_no_zero_6560_6579 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 6560)).length → fastA (i.val + 6560) ≠ 0 := by
  decide

private theorem fast_no_zero_6580_6599 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 6580)).length → fastA (i.val + 6580) ≠ 0 := by
  decide

private theorem fast_no_zero_6600_6619 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 6600)).length → fastA (i.val + 6600) ≠ 0 := by
  decide

private theorem fast_no_zero_6620_6639 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 6620)).length → fastA (i.val + 6620) ≠ 0 := by
  decide

private theorem fast_no_zero_6640_6659 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 6640)).length → fastA (i.val + 6640) ≠ 0 := by
  decide

private theorem fast_no_zero_6660_6679 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 6660)).length → fastA (i.val + 6660) ≠ 0 := by
  decide

private theorem fast_no_zero_6680_6699 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 6680)).length → fastA (i.val + 6680) ≠ 0 := by
  decide

private theorem fast_no_zero_6700_6719 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 6700)).length → fastA (i.val + 6700) ≠ 0 := by
  decide

private theorem fast_no_zero_6720_6739 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 6720)).length → fastA (i.val + 6720) ≠ 0 := by
  decide

private theorem fast_no_zero_6740_6759 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 6740)).length → fastA (i.val + 6740) ≠ 0 := by
  decide

private theorem fast_no_zero_6760_6779 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 6760)).length → fastA (i.val + 6760) ≠ 0 := by
  decide

private theorem fast_no_zero_6780_6799 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 6780)).length → fastA (i.val + 6780) ≠ 0 := by
  decide

private theorem fast_no_zero_6800_6819 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 6800)).length → fastA (i.val + 6800) ≠ 0 := by
  decide

private theorem fast_no_zero_6820_6839 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 6820)).length → fastA (i.val + 6820) ≠ 0 := by
  decide

private theorem fast_no_zero_6840_6859 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 6840)).length → fastA (i.val + 6840) ≠ 0 := by
  decide

private theorem fast_no_zero_6860_6879 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 6860)).length → fastA (i.val + 6860) ≠ 0 := by
  decide

private theorem fast_no_zero_6880_6899 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 6880)).length → fastA (i.val + 6880) ≠ 0 := by
  decide

private theorem fast_no_zero_6900_6919 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 6900)).length → fastA (i.val + 6900) ≠ 0 := by
  decide

private theorem fast_no_zero_6920_6939 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 6920)).length → fastA (i.val + 6920) ≠ 0 := by
  decide

private theorem fast_no_zero_6940_6959 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 6940)).length → fastA (i.val + 6940) ≠ 0 := by
  decide

private theorem fast_no_zero_6960_6979 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 6960)).length → fastA (i.val + 6960) ≠ 0 := by
  decide

private theorem fast_no_zero_6980_6999 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 6980)).length → fastA (i.val + 6980) ≠ 0 := by
  decide

private theorem fast_no_zero_7000_7019 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 7000)).length → fastA (i.val + 7000) ≠ 0 := by
  decide

private theorem fast_no_zero_7020_7039 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 7020)).length → fastA (i.val + 7020) ≠ 0 := by
  decide

private theorem fast_no_zero_7040_7059 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 7040)).length → fastA (i.val + 7040) ≠ 0 := by
  decide

private theorem fast_no_zero_7060_7079 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 7060)).length → fastA (i.val + 7060) ≠ 0 := by
  decide

private theorem fast_no_zero_7080_7099 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 7080)).length → fastA (i.val + 7080) ≠ 0 := by
  decide

private theorem fast_no_zero_7100_7119 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 7100)).length → fastA (i.val + 7100) ≠ 0 := by
  decide

private theorem fast_no_zero_7120_7139 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 7120)).length → fastA (i.val + 7120) ≠ 0 := by
  decide

private theorem fast_no_zero_7140_7159 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 7140)).length → fastA (i.val + 7140) ≠ 0 := by
  decide

private theorem fast_no_zero_7160_7179 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 7160)).length → fastA (i.val + 7160) ≠ 0 := by
  decide

private theorem fast_no_zero_7180_7199 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 7180)).length → fastA (i.val + 7180) ≠ 0 := by
  decide

private theorem fast_no_zero_7200_7219 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 7200)).length → fastA (i.val + 7200) ≠ 0 := by
  decide

private theorem fast_no_zero_7220_7239 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 7220)).length → fastA (i.val + 7220) ≠ 0 := by
  decide

private theorem fast_no_zero_7240_7259 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 7240)).length → fastA (i.val + 7240) ≠ 0 := by
  decide

private theorem fast_no_zero_7260_7279 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 7260)).length → fastA (i.val + 7260) ≠ 0 := by
  decide

private theorem fast_no_zero_7280_7299 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 7280)).length → fastA (i.val + 7280) ≠ 0 := by
  decide

private theorem fast_no_zero_7300_7319 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 7300)).length → fastA (i.val + 7300) ≠ 0 := by
  decide

private theorem fast_no_zero_7320_7339 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 7320)).length → fastA (i.val + 7320) ≠ 0 := by
  decide

private theorem fast_no_zero_7340_7359 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 7340)).length → fastA (i.val + 7340) ≠ 0 := by
  decide

private theorem fast_no_zero_7360_7379 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 7360)).length → fastA (i.val + 7360) ≠ 0 := by
  decide

private theorem fast_no_zero_7380_7399 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 7380)).length → fastA (i.val + 7380) ≠ 0 := by
  decide

private theorem fast_no_zero_7400_7419 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 7400)).length → fastA (i.val + 7400) ≠ 0 := by
  decide

private theorem fast_no_zero_7420_7439 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 7420)).length → fastA (i.val + 7420) ≠ 0 := by
  decide

private theorem fast_no_zero_7440_7459 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 7440)).length → fastA (i.val + 7440) ≠ 0 := by
  decide

private theorem fast_no_zero_7460_7479 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 7460)).length → fastA (i.val + 7460) ≠ 0 := by
  decide

private theorem fast_no_zero_7480_7499 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 7480)).length → fastA (i.val + 7480) ≠ 0 := by
  decide

private theorem fast_no_zero_7500_7519 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 7500)).length → fastA (i.val + 7500) ≠ 0 := by
  decide

private theorem fast_no_zero_7520_7539 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 7520)).length → fastA (i.val + 7520) ≠ 0 := by
  decide

private theorem fast_no_zero_7540_7559 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 7540)).length → fastA (i.val + 7540) ≠ 0 := by
  decide

private theorem fast_no_zero_7560_7579 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 7560)).length → fastA (i.val + 7560) ≠ 0 := by
  decide

private theorem fast_no_zero_7580_7599 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 7580)).length → fastA (i.val + 7580) ≠ 0 := by
  decide

private theorem fast_no_zero_7600_7619 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 7600)).length → fastA (i.val + 7600) ≠ 0 := by
  decide

private theorem fast_no_zero_7620_7639 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 7620)).length → fastA (i.val + 7620) ≠ 0 := by
  decide

private theorem fast_no_zero_7640_7659 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 7640)).length → fastA (i.val + 7640) ≠ 0 := by
  decide

private theorem fast_no_zero_7660_7679 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 7660)).length → fastA (i.val + 7660) ≠ 0 := by
  decide

private theorem fast_no_zero_7680_7699 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 7680)).length → fastA (i.val + 7680) ≠ 0 := by
  decide

private theorem fast_no_zero_7700_7719 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 7700)).length → fastA (i.val + 7700) ≠ 0 := by
  decide

private theorem fast_no_zero_7720_7739 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 7720)).length → fastA (i.val + 7720) ≠ 0 := by
  decide

private theorem fast_no_zero_7740_7759 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 7740)).length → fastA (i.val + 7740) ≠ 0 := by
  decide

private theorem fast_no_zero_7760_7779 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 7760)).length → fastA (i.val + 7760) ≠ 0 := by
  decide

private theorem fast_no_zero_7780_7799 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 7780)).length → fastA (i.val + 7780) ≠ 0 := by
  decide

private theorem fast_no_zero_7800_7819 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 7800)).length → fastA (i.val + 7800) ≠ 0 := by
  decide

private theorem fast_no_zero_7820_7839 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 7820)).length → fastA (i.val + 7820) ≠ 0 := by
  decide

private theorem fast_no_zero_7840_7859 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 7840)).length → fastA (i.val + 7840) ≠ 0 := by
  decide

private theorem fast_no_zero_7860_7879 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 7860)).length → fastA (i.val + 7860) ≠ 0 := by
  decide

private theorem fast_no_zero_7880_7899 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 7880)).length → fastA (i.val + 7880) ≠ 0 := by
  decide

private theorem fast_no_zero_7900_7919 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 7900)).length → fastA (i.val + 7900) ≠ 0 := by
  decide

private theorem fast_no_zero_7920_7939 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 7920)).length → fastA (i.val + 7920) ≠ 0 := by
  decide

private theorem fast_no_zero_7940_7959 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 7940)).length → fastA (i.val + 7940) ≠ 0 := by
  decide

private theorem fast_no_zero_7960_7979 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 7960)).length → fastA (i.val + 7960) ≠ 0 := by
  decide

private theorem fast_no_zero_7980_7999 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 7980)).length → fastA (i.val + 7980) ≠ 0 := by
  decide

private theorem fast_no_zero_8000_8019 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 8000)).length → fastA (i.val + 8000) ≠ 0 := by
  decide

private theorem fast_no_zero_8020_8039 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 8020)).length → fastA (i.val + 8020) ≠ 0 := by
  decide

private theorem fast_no_zero_8040_8059 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 8040)).length → fastA (i.val + 8040) ≠ 0 := by
  decide

private theorem fast_no_zero_8060_8079 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 8060)).length → fastA (i.val + 8060) ≠ 0 := by
  decide

private theorem fast_no_zero_8080_8099 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 8080)).length → fastA (i.val + 8080) ≠ 0 := by
  decide

private theorem fast_no_zero_8100_8119 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 8100)).length → fastA (i.val + 8100) ≠ 0 := by
  decide

private theorem fast_no_zero_8120_8139 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 8120)).length → fastA (i.val + 8120) ≠ 0 := by
  decide

private theorem fast_no_zero_8140_8159 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 8140)).length → fastA (i.val + 8140) ≠ 0 := by
  decide

private theorem fast_no_zero_8160_8179 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 8160)).length → fastA (i.val + 8160) ≠ 0 := by
  decide

private theorem fast_no_zero_8180_8199 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 8180)).length → fastA (i.val + 8180) ≠ 0 := by
  decide

private theorem fast_no_zero_8200_8219 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 8200)).length → fastA (i.val + 8200) ≠ 0 := by
  decide

private theorem fast_no_zero_8220_8239 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 8220)).length → fastA (i.val + 8220) ≠ 0 := by
  decide

private theorem fast_no_zero_8240_8259 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 8240)).length → fastA (i.val + 8240) ≠ 0 := by
  decide

private theorem fast_no_zero_8260_8279 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 8260)).length → fastA (i.val + 8260) ≠ 0 := by
  decide

private theorem fast_no_zero_8280_8299 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 8280)).length → fastA (i.val + 8280) ≠ 0 := by
  decide

private theorem fast_no_zero_8300_8319 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 8300)).length → fastA (i.val + 8300) ≠ 0 := by
  decide

private theorem fast_no_zero_8320_8339 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 8320)).length → fastA (i.val + 8320) ≠ 0 := by
  decide

private theorem fast_no_zero_8340_8359 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 8340)).length → fastA (i.val + 8340) ≠ 0 := by
  decide

private theorem fast_no_zero_8360_8379 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 8360)).length → fastA (i.val + 8360) ≠ 0 := by
  decide

private theorem fast_no_zero_8380_8399 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 8380)).length → fastA (i.val + 8380) ≠ 0 := by
  decide

private theorem fast_no_zero_8400_8419 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 8400)).length → fastA (i.val + 8400) ≠ 0 := by
  decide

private theorem fast_no_zero_8420_8439 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 8420)).length → fastA (i.val + 8420) ≠ 0 := by
  decide

private theorem fast_no_zero_8440_8459 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 8440)).length → fastA (i.val + 8440) ≠ 0 := by
  decide

private theorem fast_no_zero_8460_8479 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 8460)).length → fastA (i.val + 8460) ≠ 0 := by
  decide

private theorem fast_no_zero_8480_8499 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 8480)).length → fastA (i.val + 8480) ≠ 0 := by
  decide

private theorem fast_no_zero_8500_8519 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 8500)).length → fastA (i.val + 8500) ≠ 0 := by
  decide

private theorem fast_no_zero_8520_8539 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 8520)).length → fastA (i.val + 8520) ≠ 0 := by
  decide

private theorem fast_no_zero_8540_8559 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 8540)).length → fastA (i.val + 8540) ≠ 0 := by
  decide

private theorem fast_no_zero_8560_8579 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 8560)).length → fastA (i.val + 8560) ≠ 0 := by
  decide

private theorem fast_no_zero_8580_8599 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 8580)).length → fastA (i.val + 8580) ≠ 0 := by
  decide

private theorem fast_no_zero_8600_8619 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 8600)).length → fastA (i.val + 8600) ≠ 0 := by
  decide

private theorem fast_no_zero_8620_8639 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 8620)).length → fastA (i.val + 8620) ≠ 0 := by
  decide

private theorem fast_no_zero_8640_8659 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 8640)).length → fastA (i.val + 8640) ≠ 0 := by
  decide

private theorem fast_no_zero_8660_8679 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 8660)).length → fastA (i.val + 8660) ≠ 0 := by
  decide

private theorem fast_no_zero_8680_8699 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 8680)).length → fastA (i.val + 8680) ≠ 0 := by
  decide

private theorem fast_no_zero_8700_8719 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 8700)).length → fastA (i.val + 8700) ≠ 0 := by
  decide

private theorem fast_no_zero_8720_8739 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 8720)).length → fastA (i.val + 8720) ≠ 0 := by
  decide

private theorem fast_no_zero_8740_8759 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 8740)).length → fastA (i.val + 8740) ≠ 0 := by
  decide

private theorem fast_no_zero_8760_8779 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 8760)).length → fastA (i.val + 8760) ≠ 0 := by
  decide

private theorem fast_no_zero_8780_8799 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 8780)).length → fastA (i.val + 8780) ≠ 0 := by
  decide

private theorem fast_no_zero_8800_8819 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 8800)).length → fastA (i.val + 8800) ≠ 0 := by
  decide

private theorem fast_no_zero_8820_8839 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 8820)).length → fastA (i.val + 8820) ≠ 0 := by
  decide

private theorem fast_no_zero_8840_8859 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 8840)).length → fastA (i.val + 8840) ≠ 0 := by
  decide

private theorem fast_no_zero_8860_8879 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 8860)).length → fastA (i.val + 8860) ≠ 0 := by
  decide

private theorem fast_no_zero_8880_8899 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 8880)).length → fastA (i.val + 8880) ≠ 0 := by
  decide

private theorem fast_no_zero_8900_8919 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 8900)).length → fastA (i.val + 8900) ≠ 0 := by
  decide

private theorem fast_no_zero_8920_8939 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 8920)).length → fastA (i.val + 8920) ≠ 0 := by
  decide

private theorem fast_no_zero_8940_8959 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 8940)).length → fastA (i.val + 8940) ≠ 0 := by
  decide

private theorem fast_no_zero_8960_8979 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 8960)).length → fastA (i.val + 8960) ≠ 0 := by
  decide

private theorem fast_no_zero_8980_8999 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 8980)).length → fastA (i.val + 8980) ≠ 0 := by
  decide

private theorem fast_no_zero_9000_9019 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 9000)).length → fastA (i.val + 9000) ≠ 0 := by
  decide

private theorem fast_no_zero_9020_9039 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 9020)).length → fastA (i.val + 9020) ≠ 0 := by
  decide

private theorem fast_no_zero_9040_9059 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 9040)).length → fastA (i.val + 9040) ≠ 0 := by
  decide

private theorem fast_no_zero_9060_9079 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 9060)).length → fastA (i.val + 9060) ≠ 0 := by
  decide

private theorem fast_no_zero_9080_9099 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 9080)).length → fastA (i.val + 9080) ≠ 0 := by
  decide

private theorem fast_no_zero_9100_9119 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 9100)).length → fastA (i.val + 9100) ≠ 0 := by
  decide

private theorem fast_no_zero_9120_9139 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 9120)).length → fastA (i.val + 9120) ≠ 0 := by
  decide

private theorem fast_no_zero_9140_9159 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 9140)).length → fastA (i.val + 9140) ≠ 0 := by
  decide

private theorem fast_no_zero_9160_9179 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 9160)).length → fastA (i.val + 9160) ≠ 0 := by
  decide

private theorem fast_no_zero_9180_9199 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 9180)).length → fastA (i.val + 9180) ≠ 0 := by
  decide

private theorem fast_no_zero_9200_9219 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 9200)).length → fastA (i.val + 9200) ≠ 0 := by
  decide

private theorem fast_no_zero_9220_9239 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 9220)).length → fastA (i.val + 9220) ≠ 0 := by
  decide

private theorem fast_no_zero_9240_9259 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 9240)).length → fastA (i.val + 9240) ≠ 0 := by
  decide

private theorem fast_no_zero_9260_9279 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 9260)).length → fastA (i.val + 9260) ≠ 0 := by
  decide

private theorem fast_no_zero_9280_9299 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 9280)).length → fastA (i.val + 9280) ≠ 0 := by
  decide

private theorem fast_no_zero_9300_9319 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 9300)).length → fastA (i.val + 9300) ≠ 0 := by
  decide

private theorem fast_no_zero_9320_9339 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 9320)).length → fastA (i.val + 9320) ≠ 0 := by
  decide

private theorem fast_no_zero_9340_9359 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 9340)).length → fastA (i.val + 9340) ≠ 0 := by
  decide

private theorem fast_no_zero_9360_9379 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 9360)).length → fastA (i.val + 9360) ≠ 0 := by
  decide

private theorem fast_no_zero_9380_9399 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 9380)).length → fastA (i.val + 9380) ≠ 0 := by
  decide

private theorem fast_no_zero_9400_9419 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 9400)).length → fastA (i.val + 9400) ≠ 0 := by
  decide

private theorem fast_no_zero_9420_9439 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 9420)).length → fastA (i.val + 9420) ≠ 0 := by
  decide

private theorem fast_no_zero_9440_9459 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 9440)).length → fastA (i.val + 9440) ≠ 0 := by
  decide

private theorem fast_no_zero_9460_9479 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 9460)).length → fastA (i.val + 9460) ≠ 0 := by
  decide

private theorem fast_no_zero_9480_9499 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 9480)).length → fastA (i.val + 9480) ≠ 0 := by
  decide

private theorem fast_no_zero_9500_9519 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 9500)).length → fastA (i.val + 9500) ≠ 0 := by
  decide

private theorem fast_no_zero_9520_9539 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 9520)).length → fastA (i.val + 9520) ≠ 0 := by
  decide

private theorem fast_no_zero_9540_9559 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 9540)).length → fastA (i.val + 9540) ≠ 0 := by
  decide

private theorem fast_no_zero_9560_9579 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 9560)).length → fastA (i.val + 9560) ≠ 0 := by
  decide

private theorem fast_no_zero_9580_9599 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 9580)).length → fastA (i.val + 9580) ≠ 0 := by
  decide

private theorem fast_no_zero_9600_9619 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 9600)).length → fastA (i.val + 9600) ≠ 0 := by
  decide

private theorem fast_no_zero_9620_9639 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 9620)).length → fastA (i.val + 9620) ≠ 0 := by
  decide

private theorem fast_no_zero_9640_9659 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 9640)).length → fastA (i.val + 9640) ≠ 0 := by
  decide

private theorem fast_no_zero_9660_9679 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 9660)).length → fastA (i.val + 9660) ≠ 0 := by
  decide

private theorem fast_no_zero_9680_9699 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 9680)).length → fastA (i.val + 9680) ≠ 0 := by
  decide

private theorem fast_no_zero_9700_9719 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 9700)).length → fastA (i.val + 9700) ≠ 0 := by
  decide

private theorem fast_no_zero_9720_9739 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 9720)).length → fastA (i.val + 9720) ≠ 0 := by
  decide

private theorem fast_no_zero_9740_9759 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 9740)).length → fastA (i.val + 9740) ≠ 0 := by
  decide

private theorem fast_no_zero_9760_9779 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 9760)).length → fastA (i.val + 9760) ≠ 0 := by
  decide

private theorem fast_no_zero_9780_9799 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 9780)).length → fastA (i.val + 9780) ≠ 0 := by
  decide

private theorem fast_no_zero_9800_9819 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 9800)).length → fastA (i.val + 9800) ≠ 0 := by
  decide

private theorem fast_no_zero_9820_9839 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 9820)).length → fastA (i.val + 9820) ≠ 0 := by
  decide

private theorem fast_no_zero_9840_9859 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 9840)).length → fastA (i.val + 9840) ≠ 0 := by
  decide

private theorem fast_no_zero_9860_9879 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 9860)).length → fastA (i.val + 9860) ≠ 0 := by
  decide

private theorem fast_no_zero_9880_9899 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 9880)).length → fastA (i.val + 9880) ≠ 0 := by
  decide

private theorem fast_no_zero_9900_9919 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 9900)).length → fastA (i.val + 9900) ≠ 0 := by
  decide

private theorem fast_no_zero_9920_9939 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 9920)).length → fastA (i.val + 9920) ≠ 0 := by
  decide

private theorem fast_no_zero_9940_9959 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 9940)).length → fastA (i.val + 9940) ≠ 0 := by
  decide

private theorem fast_no_zero_9960_9979 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 9960)).length → fastA (i.val + 9960) ≠ 0 := by
  decide

private theorem fast_no_zero_9980_9999 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 9980)).length → fastA (i.val + 9980) ≠ 0 := by
  decide

private theorem fast_no_zero_10000_10019 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 10000)).length → fastA (i.val + 10000) ≠ 0 := by
  decide

private theorem fast_no_zero_10020_10039 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 10020)).length → fastA (i.val + 10020) ≠ 0 := by
  decide

private theorem fast_no_zero_10040_10059 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 10040)).length → fastA (i.val + 10040) ≠ 0 := by
  decide

private theorem fast_no_zero_10060_10079 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 10060)).length → fastA (i.val + 10060) ≠ 0 := by
  decide

private theorem fast_no_zero_10080_10099 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 10080)).length → fastA (i.val + 10080) ≠ 0 := by
  decide

private theorem fast_no_zero_10100_10119 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 10100)).length → fastA (i.val + 10100) ≠ 0 := by
  decide

private theorem fast_no_zero_10120_10139 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 10120)).length → fastA (i.val + 10120) ≠ 0 := by
  decide

private theorem fast_no_zero_10140_10159 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 10140)).length → fastA (i.val + 10140) ≠ 0 := by
  decide

private theorem fast_no_zero_10160_10179 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 10160)).length → fastA (i.val + 10160) ≠ 0 := by
  decide

private theorem fast_no_zero_10180_10199 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 10180)).length → fastA (i.val + 10180) ≠ 0 := by
  decide

private theorem fast_no_zero_10200_10219 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 10200)).length → fastA (i.val + 10200) ≠ 0 := by
  decide

private theorem fast_no_zero_10220_10239 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 10220)).length → fastA (i.val + 10220) ≠ 0 := by
  decide

private theorem fast_no_zero_10240_10259 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 10240)).length → fastA (i.val + 10240) ≠ 0 := by
  decide

private theorem fast_no_zero_10260_10279 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 10260)).length → fastA (i.val + 10260) ≠ 0 := by
  decide

private theorem fast_no_zero_10280_10299 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 10280)).length → fastA (i.val + 10280) ≠ 0 := by
  decide

private theorem fast_no_zero_10300_10319 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 10300)).length → fastA (i.val + 10300) ≠ 0 := by
  decide

private theorem fast_no_zero_10320_10339 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 10320)).length → fastA (i.val + 10320) ≠ 0 := by
  decide

private theorem fast_no_zero_10340_10359 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 10340)).length → fastA (i.val + 10340) ≠ 0 := by
  decide

private theorem fast_no_zero_10360_10379 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 10360)).length → fastA (i.val + 10360) ≠ 0 := by
  decide

private theorem fast_no_zero_10380_10399 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 10380)).length → fastA (i.val + 10380) ≠ 0 := by
  decide

private theorem fast_no_zero_10400_10419 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 10400)).length → fastA (i.val + 10400) ≠ 0 := by
  decide

private theorem fast_no_zero_10420_10439 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 10420)).length → fastA (i.val + 10420) ≠ 0 := by
  decide

private theorem fast_no_zero_10440_10459 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 10440)).length → fastA (i.val + 10440) ≠ 0 := by
  decide

private theorem fast_no_zero_10460_10479 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 10460)).length → fastA (i.val + 10460) ≠ 0 := by
  decide

private theorem fast_no_zero_10480_10499 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 10480)).length → fastA (i.val + 10480) ≠ 0 := by
  decide

private theorem fast_no_zero_10500_10519 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 10500)).length → fastA (i.val + 10500) ≠ 0 := by
  decide

private theorem fast_no_zero_10520_10539 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 10520)).length → fastA (i.val + 10520) ≠ 0 := by
  decide

private theorem fast_no_zero_10540_10559 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 10540)).length → fastA (i.val + 10540) ≠ 0 := by
  decide

private theorem fast_no_zero_10560_10579 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 10560)).length → fastA (i.val + 10560) ≠ 0 := by
  decide

private theorem fast_no_zero_10580_10599 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 10580)).length → fastA (i.val + 10580) ≠ 0 := by
  decide

private theorem fast_no_zero_10600_10619 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 10600)).length → fastA (i.val + 10600) ≠ 0 := by
  decide

private theorem fast_no_zero_10620_10639 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 10620)).length → fastA (i.val + 10620) ≠ 0 := by
  decide

private theorem fast_no_zero_10640_10659 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 10640)).length → fastA (i.val + 10640) ≠ 0 := by
  decide

private theorem fast_no_zero_10660_10679 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 10660)).length → fastA (i.val + 10660) ≠ 0 := by
  decide

private theorem fast_no_zero_10680_10699 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 10680)).length → fastA (i.val + 10680) ≠ 0 := by
  decide

private theorem fast_no_zero_10700_10719 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 10700)).length → fastA (i.val + 10700) ≠ 0 := by
  decide

private theorem fast_no_zero_10720_10739 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 10720)).length → fastA (i.val + 10720) ≠ 0 := by
  decide

private theorem fast_no_zero_10740_10759 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 10740)).length → fastA (i.val + 10740) ≠ 0 := by
  decide

private theorem fast_no_zero_10760_10779 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 10760)).length → fastA (i.val + 10760) ≠ 0 := by
  decide

private theorem fast_no_zero_10780_10799 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 10780)).length → fastA (i.val + 10780) ≠ 0 := by
  decide

private theorem fast_no_zero_10800_10819 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 10800)).length → fastA (i.val + 10800) ≠ 0 := by
  decide

private theorem fast_no_zero_10820_10839 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 10820)).length → fastA (i.val + 10820) ≠ 0 := by
  decide

private theorem fast_no_zero_10840_10859 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 10840)).length → fastA (i.val + 10840) ≠ 0 := by
  decide

private theorem fast_no_zero_10860_10879 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 10860)).length → fastA (i.val + 10860) ≠ 0 := by
  decide

private theorem fast_no_zero_10880_10899 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 10880)).length → fastA (i.val + 10880) ≠ 0 := by
  decide

private theorem fast_no_zero_10900_10919 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 10900)).length → fastA (i.val + 10900) ≠ 0 := by
  decide

private theorem fast_no_zero_10920_10939 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 10920)).length → fastA (i.val + 10920) ≠ 0 := by
  decide

private theorem fast_no_zero_10940_10959 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 10940)).length → fastA (i.val + 10940) ≠ 0 := by
  decide

private theorem fast_no_zero_10960_10979 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 10960)).length → fastA (i.val + 10960) ≠ 0 := by
  decide

private theorem fast_no_zero_10980_10999 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 10980)).length → fastA (i.val + 10980) ≠ 0 := by
  decide

private theorem fast_no_zero_11000_11019 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 11000)).length → fastA (i.val + 11000) ≠ 0 := by
  decide

private theorem fast_no_zero_11020_11039 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 11020)).length → fastA (i.val + 11020) ≠ 0 := by
  decide

private theorem fast_no_zero_11040_11059 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 11040)).length → fastA (i.val + 11040) ≠ 0 := by
  decide

private theorem fast_no_zero_11060_11079 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 11060)).length → fastA (i.val + 11060) ≠ 0 := by
  decide

private theorem fast_no_zero_11080_11099 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 11080)).length → fastA (i.val + 11080) ≠ 0 := by
  decide

private theorem fast_no_zero_11100_11119 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 11100)).length → fastA (i.val + 11100) ≠ 0 := by
  decide

private theorem fast_no_zero_11120_11139 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 11120)).length → fastA (i.val + 11120) ≠ 0 := by
  decide

private theorem fast_no_zero_11140_11159 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 11140)).length → fastA (i.val + 11140) ≠ 0 := by
  decide

private theorem fast_no_zero_11160_11179 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 11160)).length → fastA (i.val + 11160) ≠ 0 := by
  decide

private theorem fast_no_zero_11180_11199 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 11180)).length → fastA (i.val + 11180) ≠ 0 := by
  decide

private theorem fast_no_zero_11200_11219 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 11200)).length → fastA (i.val + 11200) ≠ 0 := by
  decide

private theorem fast_no_zero_11220_11239 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 11220)).length → fastA (i.val + 11220) ≠ 0 := by
  decide

private theorem fast_no_zero_11240_11259 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 11240)).length → fastA (i.val + 11240) ≠ 0 := by
  decide

private theorem fast_no_zero_11260_11279 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 11260)).length → fastA (i.val + 11260) ≠ 0 := by
  decide

private theorem fast_no_zero_11280_11299 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 11280)).length → fastA (i.val + 11280) ≠ 0 := by
  decide

private theorem fast_no_zero_11300_11319 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 11300)).length → fastA (i.val + 11300) ≠ 0 := by
  decide

private theorem fast_no_zero_11320_11339 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 11320)).length → fastA (i.val + 11320) ≠ 0 := by
  decide

private theorem fast_no_zero_11340_11359 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 11340)).length → fastA (i.val + 11340) ≠ 0 := by
  decide

private theorem fast_no_zero_11360_11379 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 11360)).length → fastA (i.val + 11360) ≠ 0 := by
  decide

private theorem fast_no_zero_11380_11399 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 11380)).length → fastA (i.val + 11380) ≠ 0 := by
  decide

private theorem fast_no_zero_11400_11419 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 11400)).length → fastA (i.val + 11400) ≠ 0 := by
  decide

private theorem fast_no_zero_11420_11439 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 11420)).length → fastA (i.val + 11420) ≠ 0 := by
  decide

private theorem fast_no_zero_11440_11459 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 11440)).length → fastA (i.val + 11440) ≠ 0 := by
  decide

private theorem fast_no_zero_11460_11479 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 11460)).length → fastA (i.val + 11460) ≠ 0 := by
  decide

private theorem fast_no_zero_11480_11499 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 11480)).length → fastA (i.val + 11480) ≠ 0 := by
  decide

private theorem fast_no_zero_11500_11519 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 11500)).length → fastA (i.val + 11500) ≠ 0 := by
  decide

private theorem fast_no_zero_11520_11539 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 11520)).length → fastA (i.val + 11520) ≠ 0 := by
  decide

private theorem fast_no_zero_11540_11559 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 11540)).length → fastA (i.val + 11540) ≠ 0 := by
  decide

private theorem fast_no_zero_11560_11579 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 11560)).length → fastA (i.val + 11560) ≠ 0 := by
  decide

private theorem fast_no_zero_11580_11599 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 11580)).length → fastA (i.val + 11580) ≠ 0 := by
  decide

private theorem fast_no_zero_11600_11619 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 11600)).length → fastA (i.val + 11600) ≠ 0 := by
  decide

private theorem fast_no_zero_11620_11639 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 11620)).length → fastA (i.val + 11620) ≠ 0 := by
  decide

private theorem fast_no_zero_11640_11659 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 11640)).length → fastA (i.val + 11640) ≠ 0 := by
  decide

private theorem fast_no_zero_11660_11679 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 11660)).length → fastA (i.val + 11660) ≠ 0 := by
  decide

private theorem fast_no_zero_11680_11699 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 11680)).length → fastA (i.val + 11680) ≠ 0 := by
  decide

private theorem fast_no_zero_11700_11719 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 11700)).length → fastA (i.val + 11700) ≠ 0 := by
  decide

private theorem fast_no_zero_11720_11739 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 11720)).length → fastA (i.val + 11720) ≠ 0 := by
  decide

private theorem fast_no_zero_11740_11759 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 11740)).length → fastA (i.val + 11740) ≠ 0 := by
  decide

private theorem fast_no_zero_11760_11779 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 11760)).length → fastA (i.val + 11760) ≠ 0 := by
  decide

private theorem fast_no_zero_11780_11799 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 11780)).length → fastA (i.val + 11780) ≠ 0 := by
  decide

private theorem fast_no_zero_11800_11819 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 11800)).length → fastA (i.val + 11800) ≠ 0 := by
  decide

private theorem fast_no_zero_11820_11839 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 11820)).length → fastA (i.val + 11820) ≠ 0 := by
  decide

private theorem fast_no_zero_11840_11859 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 11840)).length → fastA (i.val + 11840) ≠ 0 := by
  decide

private theorem fast_no_zero_11860_11879 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 11860)).length → fastA (i.val + 11860) ≠ 0 := by
  decide

private theorem fast_no_zero_11880_11899 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 11880)).length → fastA (i.val + 11880) ≠ 0 := by
  decide

private theorem fast_no_zero_11900_11919 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 11900)).length → fastA (i.val + 11900) ≠ 0 := by
  decide

private theorem fast_no_zero_11920_11939 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 11920)).length → fastA (i.val + 11920) ≠ 0 := by
  decide

private theorem fast_no_zero_11940_11959 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 11940)).length → fastA (i.val + 11940) ≠ 0 := by
  decide

private theorem fast_no_zero_11960_11979 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 11960)).length → fastA (i.val + 11960) ≠ 0 := by
  decide

private theorem fast_no_zero_11980_11999 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 11980)).length → fastA (i.val + 11980) ≠ 0 := by
  decide

private theorem fast_no_zero_12000_12019 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 12000)).length → fastA (i.val + 12000) ≠ 0 := by
  decide

private theorem fast_no_zero_12020_12039 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 12020)).length → fastA (i.val + 12020) ≠ 0 := by
  decide

private theorem fast_no_zero_12040_12059 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 12040)).length → fastA (i.val + 12040) ≠ 0 := by
  decide

private theorem fast_no_zero_12060_12079 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 12060)).length → fastA (i.val + 12060) ≠ 0 := by
  decide

private theorem fast_no_zero_12080_12099 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 12080)).length → fastA (i.val + 12080) ≠ 0 := by
  decide

private theorem fast_no_zero_12100_12119 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 12100)).length → fastA (i.val + 12100) ≠ 0 := by
  decide

private theorem fast_no_zero_12120_12139 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 12120)).length → fastA (i.val + 12120) ≠ 0 := by
  decide

private theorem fast_no_zero_12140_12159 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 12140)).length → fastA (i.val + 12140) ≠ 0 := by
  decide

private theorem fast_no_zero_12160_12179 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 12160)).length → fastA (i.val + 12160) ≠ 0 := by
  decide

private theorem fast_no_zero_12180_12199 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 12180)).length → fastA (i.val + 12180) ≠ 0 := by
  decide

private theorem fast_no_zero_12200_12219 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 12200)).length → fastA (i.val + 12200) ≠ 0 := by
  decide

private theorem fast_no_zero_12220_12239 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 12220)).length → fastA (i.val + 12220) ≠ 0 := by
  decide

private theorem fast_no_zero_12240_12259 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 12240)).length → fastA (i.val + 12240) ≠ 0 := by
  decide

private theorem fast_no_zero_12260_12279 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 12260)).length → fastA (i.val + 12260) ≠ 0 := by
  decide

private theorem fast_no_zero_12280_12299 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 12280)).length → fastA (i.val + 12280) ≠ 0 := by
  decide

private theorem fast_no_zero_12300_12319 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 12300)).length → fastA (i.val + 12300) ≠ 0 := by
  decide

private theorem fast_no_zero_12320_12339 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 12320)).length → fastA (i.val + 12320) ≠ 0 := by
  decide

private theorem fast_no_zero_12340_12359 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 12340)).length → fastA (i.val + 12340) ≠ 0 := by
  decide

private theorem fast_no_zero_12360_12379 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 12360)).length → fastA (i.val + 12360) ≠ 0 := by
  decide

private theorem fast_no_zero_12380_12399 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 12380)).length → fastA (i.val + 12380) ≠ 0 := by
  decide

private theorem fast_no_zero_12400_12419 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 12400)).length → fastA (i.val + 12400) ≠ 0 := by
  decide

private theorem fast_no_zero_12420_12439 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 12420)).length → fastA (i.val + 12420) ≠ 0 := by
  decide

private theorem fast_no_zero_12440_12459 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 12440)).length → fastA (i.val + 12440) ≠ 0 := by
  decide

private theorem fast_no_zero_12460_12479 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 12460)).length → fastA (i.val + 12460) ≠ 0 := by
  decide

private theorem fast_no_zero_12480_12499 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 12480)).length → fastA (i.val + 12480) ≠ 0 := by
  decide

private theorem fast_no_zero_12500_12519 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 12500)).length → fastA (i.val + 12500) ≠ 0 := by
  decide

private theorem fast_no_zero_12520_12539 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 12520)).length → fastA (i.val + 12520) ≠ 0 := by
  decide

private theorem fast_no_zero_12540_12559 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 12540)).length → fastA (i.val + 12540) ≠ 0 := by
  decide

private theorem fast_no_zero_12560_12579 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 12560)).length → fastA (i.val + 12560) ≠ 0 := by
  decide

private theorem fast_no_zero_12580_12599 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 12580)).length → fastA (i.val + 12580) ≠ 0 := by
  decide

private theorem fast_no_zero_12600_12619 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 12600)).length → fastA (i.val + 12600) ≠ 0 := by
  decide

private theorem fast_no_zero_12620_12639 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 12620)).length → fastA (i.val + 12620) ≠ 0 := by
  decide

private theorem fast_no_zero_12640_12659 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 12640)).length → fastA (i.val + 12640) ≠ 0 := by
  decide

private theorem fast_no_zero_12660_12679 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 12660)).length → fastA (i.val + 12660) ≠ 0 := by
  decide

private theorem fast_no_zero_12680_12699 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 12680)).length → fastA (i.val + 12680) ≠ 0 := by
  decide

private theorem fast_no_zero_12700_12719 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 12700)).length → fastA (i.val + 12700) ≠ 0 := by
  decide

private theorem fast_no_zero_12720_12739 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 12720)).length → fastA (i.val + 12720) ≠ 0 := by
  decide

private theorem fast_no_zero_12740_12759 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 12740)).length → fastA (i.val + 12740) ≠ 0 := by
  decide

private theorem fast_no_zero_12760_12779 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 12760)).length → fastA (i.val + 12760) ≠ 0 := by
  decide

private theorem fast_no_zero_12780_12799 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 12780)).length → fastA (i.val + 12780) ≠ 0 := by
  decide

private theorem fast_no_zero_12800_12819 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 12800)).length → fastA (i.val + 12800) ≠ 0 := by
  decide

private theorem fast_no_zero_12820_12839 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 12820)).length → fastA (i.val + 12820) ≠ 0 := by
  decide

private theorem fast_no_zero_12840_12859 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 12840)).length → fastA (i.val + 12840) ≠ 0 := by
  decide

private theorem fast_no_zero_12860_12879 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 12860)).length → fastA (i.val + 12860) ≠ 0 := by
  decide

private theorem fast_no_zero_12880_12899 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 12880)).length → fastA (i.val + 12880) ≠ 0 := by
  decide

private theorem fast_no_zero_12900_12919 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 12900)).length → fastA (i.val + 12900) ≠ 0 := by
  decide

private theorem fast_no_zero_12920_12939 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 12920)).length → fastA (i.val + 12920) ≠ 0 := by
  decide

private theorem fast_no_zero_12940_12959 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 12940)).length → fastA (i.val + 12940) ≠ 0 := by
  decide

private theorem fast_no_zero_12960_12979 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 12960)).length → fastA (i.val + 12960) ≠ 0 := by
  decide

private theorem fast_no_zero_12980_12999 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 12980)).length → fastA (i.val + 12980) ≠ 0 := by
  decide

private theorem fast_no_zero_13000_13019 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 13000)).length → fastA (i.val + 13000) ≠ 0 := by
  decide

private theorem fast_no_zero_13020_13039 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 13020)).length → fastA (i.val + 13020) ≠ 0 := by
  decide

private theorem fast_no_zero_13040_13059 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 13040)).length → fastA (i.val + 13040) ≠ 0 := by
  decide

private theorem fast_no_zero_13060_13079 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 13060)).length → fastA (i.val + 13060) ≠ 0 := by
  decide

private theorem fast_no_zero_13080_13099 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 13080)).length → fastA (i.val + 13080) ≠ 0 := by
  decide

private theorem fast_no_zero_13100_13119 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 13100)).length → fastA (i.val + 13100) ≠ 0 := by
  decide

private theorem fast_no_zero_13120_13139 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 13120)).length → fastA (i.val + 13120) ≠ 0 := by
  decide

private theorem fast_no_zero_13140_13159 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 13140)).length → fastA (i.val + 13140) ≠ 0 := by
  decide

private theorem fast_no_zero_13160_13179 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 13160)).length → fastA (i.val + 13160) ≠ 0 := by
  decide

private theorem fast_no_zero_13180_13199 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 13180)).length → fastA (i.val + 13180) ≠ 0 := by
  decide

private theorem fast_no_zero_13200_13219 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 13200)).length → fastA (i.val + 13200) ≠ 0 := by
  decide

private theorem fast_no_zero_13220_13239 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 13220)).length → fastA (i.val + 13220) ≠ 0 := by
  decide

private theorem fast_no_zero_13240_13259 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 13240)).length → fastA (i.val + 13240) ≠ 0 := by
  decide

private theorem fast_no_zero_13260_13279 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 13260)).length → fastA (i.val + 13260) ≠ 0 := by
  decide

private theorem fast_no_zero_13280_13299 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 13280)).length → fastA (i.val + 13280) ≠ 0 := by
  decide

private theorem fast_no_zero_13300_13319 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 13300)).length → fastA (i.val + 13300) ≠ 0 := by
  decide

private theorem fast_no_zero_13320_13339 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 13320)).length → fastA (i.val + 13320) ≠ 0 := by
  decide

private theorem fast_no_zero_13340_13359 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 13340)).length → fastA (i.val + 13340) ≠ 0 := by
  decide

private theorem fast_no_zero_13360_13379 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 13360)).length → fastA (i.val + 13360) ≠ 0 := by
  decide

private theorem fast_no_zero_13380_13399 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 13380)).length → fastA (i.val + 13380) ≠ 0 := by
  decide

private theorem fast_no_zero_13400_13419 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 13400)).length → fastA (i.val + 13400) ≠ 0 := by
  decide

private theorem fast_no_zero_13420_13439 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 13420)).length → fastA (i.val + 13420) ≠ 0 := by
  decide

private theorem fast_no_zero_13440_13459 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 13440)).length → fastA (i.val + 13440) ≠ 0 := by
  decide

private theorem fast_no_zero_13460_13479 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 13460)).length → fastA (i.val + 13460) ≠ 0 := by
  decide

private theorem fast_no_zero_13480_13499 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 13480)).length → fastA (i.val + 13480) ≠ 0 := by
  decide

private theorem fast_no_zero_13500_13519 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 13500)).length → fastA (i.val + 13500) ≠ 0 := by
  decide

private theorem fast_no_zero_13520_13539 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 13520)).length → fastA (i.val + 13520) ≠ 0 := by
  decide

private theorem fast_no_zero_13540_13559 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 13540)).length → fastA (i.val + 13540) ≠ 0 := by
  decide

private theorem fast_no_zero_13560_13579 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 13560)).length → fastA (i.val + 13560) ≠ 0 := by
  decide

private theorem fast_no_zero_13580_13599 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 13580)).length → fastA (i.val + 13580) ≠ 0 := by
  decide

private theorem fast_no_zero_13600_13619 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 13600)).length → fastA (i.val + 13600) ≠ 0 := by
  decide

private theorem fast_no_zero_13620_13639 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 13620)).length → fastA (i.val + 13620) ≠ 0 := by
  decide

private theorem fast_no_zero_13640_13659 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 13640)).length → fastA (i.val + 13640) ≠ 0 := by
  decide

private theorem fast_no_zero_13660_13679 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 13660)).length → fastA (i.val + 13660) ≠ 0 := by
  decide

private theorem fast_no_zero_13680_13699 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 13680)).length → fastA (i.val + 13680) ≠ 0 := by
  decide

private theorem fast_no_zero_13700_13719 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 13700)).length → fastA (i.val + 13700) ≠ 0 := by
  decide

private theorem fast_no_zero_13720_13739 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 13720)).length → fastA (i.val + 13720) ≠ 0 := by
  decide

private theorem fast_no_zero_13740_13759 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 13740)).length → fastA (i.val + 13740) ≠ 0 := by
  decide

private theorem fast_no_zero_13760_13779 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 13760)).length → fastA (i.val + 13760) ≠ 0 := by
  decide

private theorem fast_no_zero_13780_13799 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 13780)).length → fastA (i.val + 13780) ≠ 0 := by
  decide

private theorem fast_no_zero_13800_13819 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 13800)).length → fastA (i.val + 13800) ≠ 0 := by
  decide

private theorem fast_no_zero_13820_13839 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 13820)).length → fastA (i.val + 13820) ≠ 0 := by
  decide

private theorem fast_no_zero_13840_13859 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 13840)).length → fastA (i.val + 13840) ≠ 0 := by
  decide

private theorem fast_no_zero_13860_13879 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 13860)).length → fastA (i.val + 13860) ≠ 0 := by
  decide

private theorem fast_no_zero_13880_13899 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 13880)).length → fastA (i.val + 13880) ≠ 0 := by
  decide

private theorem fast_no_zero_13900_13919 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 13900)).length → fastA (i.val + 13900) ≠ 0 := by
  decide

private theorem fast_no_zero_13920_13939 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 13920)).length → fastA (i.val + 13920) ≠ 0 := by
  decide

private theorem fast_no_zero_13940_13959 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 13940)).length → fastA (i.val + 13940) ≠ 0 := by
  decide

private theorem fast_no_zero_13960_13979 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 13960)).length → fastA (i.val + 13960) ≠ 0 := by
  decide

private theorem fast_no_zero_13980_13999 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 13980)).length → fastA (i.val + 13980) ≠ 0 := by
  decide

private theorem fast_no_zero_14000_14019 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 14000)).length → fastA (i.val + 14000) ≠ 0 := by
  decide

private theorem fast_no_zero_14020_14039 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 14020)).length → fastA (i.val + 14020) ≠ 0 := by
  decide

private theorem fast_no_zero_14040_14059 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 14040)).length → fastA (i.val + 14040) ≠ 0 := by
  decide

private theorem fast_no_zero_14060_14079 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 14060)).length → fastA (i.val + 14060) ≠ 0 := by
  decide

private theorem fast_no_zero_14080_14099 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 14080)).length → fastA (i.val + 14080) ≠ 0 := by
  decide

private theorem fast_no_zero_14100_14119 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 14100)).length → fastA (i.val + 14100) ≠ 0 := by
  decide

private theorem fast_no_zero_14120_14139 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 14120)).length → fastA (i.val + 14120) ≠ 0 := by
  decide

private theorem fast_no_zero_14140_14159 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 14140)).length → fastA (i.val + 14140) ≠ 0 := by
  decide

private theorem fast_no_zero_14160_14179 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 14160)).length → fastA (i.val + 14160) ≠ 0 := by
  decide

private theorem fast_no_zero_14180_14199 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 14180)).length → fastA (i.val + 14180) ≠ 0 := by
  decide

private theorem fast_no_zero_14200_14219 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 14200)).length → fastA (i.val + 14200) ≠ 0 := by
  decide

private theorem fast_no_zero_14220_14239 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 14220)).length → fastA (i.val + 14220) ≠ 0 := by
  decide

private theorem fast_no_zero_14240_14259 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 14240)).length → fastA (i.val + 14240) ≠ 0 := by
  decide

private theorem fast_no_zero_14260_14279 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 14260)).length → fastA (i.val + 14260) ≠ 0 := by
  decide

private theorem fast_no_zero_14280_14299 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 14280)).length → fastA (i.val + 14280) ≠ 0 := by
  decide

private theorem fast_no_zero_14300_14319 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 14300)).length → fastA (i.val + 14300) ≠ 0 := by
  decide

private theorem fast_no_zero_14320_14339 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 14320)).length → fastA (i.val + 14320) ≠ 0 := by
  decide

private theorem fast_no_zero_14340_14359 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 14340)).length → fastA (i.val + 14340) ≠ 0 := by
  decide

private theorem fast_no_zero_14360_14379 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 14360)).length → fastA (i.val + 14360) ≠ 0 := by
  decide

private theorem fast_no_zero_14380_14399 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 14380)).length → fastA (i.val + 14380) ≠ 0 := by
  decide

private theorem fast_no_zero_14400_14419 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 14400)).length → fastA (i.val + 14400) ≠ 0 := by
  decide

private theorem fast_no_zero_14420_14439 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 14420)).length → fastA (i.val + 14420) ≠ 0 := by
  decide

private theorem fast_no_zero_14440_14459 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 14440)).length → fastA (i.val + 14440) ≠ 0 := by
  decide

private theorem fast_no_zero_14460_14479 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 14460)).length → fastA (i.val + 14460) ≠ 0 := by
  decide

private theorem fast_no_zero_14480_14499 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 14480)).length → fastA (i.val + 14480) ≠ 0 := by
  decide

private theorem fast_no_zero_14500_14519 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 14500)).length → fastA (i.val + 14500) ≠ 0 := by
  decide

private theorem fast_no_zero_14520_14539 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 14520)).length → fastA (i.val + 14520) ≠ 0 := by
  decide

private theorem fast_no_zero_14540_14559 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 14540)).length → fastA (i.val + 14540) ≠ 0 := by
  decide

private theorem fast_no_zero_14560_14579 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 14560)).length → fastA (i.val + 14560) ≠ 0 := by
  decide

private theorem fast_no_zero_14580_14599 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 14580)).length → fastA (i.val + 14580) ≠ 0 := by
  decide

private theorem fast_no_zero_14600_14619 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 14600)).length → fastA (i.val + 14600) ≠ 0 := by
  decide

private theorem fast_no_zero_14620_14639 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 14620)).length → fastA (i.val + 14620) ≠ 0 := by
  decide

private theorem fast_no_zero_14640_14659 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 14640)).length → fastA (i.val + 14640) ≠ 0 := by
  decide

private theorem fast_no_zero_14660_14679 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 14660)).length → fastA (i.val + 14660) ≠ 0 := by
  decide

private theorem fast_no_zero_14680_14699 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 14680)).length → fastA (i.val + 14680) ≠ 0 := by
  decide

private theorem fast_no_zero_14700_14719 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 14700)).length → fastA (i.val + 14700) ≠ 0 := by
  decide

private theorem fast_no_zero_14720_14739 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 14720)).length → fastA (i.val + 14720) ≠ 0 := by
  decide

private theorem fast_no_zero_14740_14759 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 14740)).length → fastA (i.val + 14740) ≠ 0 := by
  decide

private theorem fast_no_zero_14760_14779 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 14760)).length → fastA (i.val + 14760) ≠ 0 := by
  decide

private theorem fast_no_zero_14780_14799 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 14780)).length → fastA (i.val + 14780) ≠ 0 := by
  decide

private theorem fast_no_zero_14800_14819 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 14800)).length → fastA (i.val + 14800) ≠ 0 := by
  decide

private theorem fast_no_zero_14820_14839 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 14820)).length → fastA (i.val + 14820) ≠ 0 := by
  decide

private theorem fast_no_zero_14840_14859 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 14840)).length → fastA (i.val + 14840) ≠ 0 := by
  decide

private theorem fast_no_zero_14860_14879 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 14860)).length → fastA (i.val + 14860) ≠ 0 := by
  decide

private theorem fast_no_zero_14880_14899 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 14880)).length → fastA (i.val + 14880) ≠ 0 := by
  decide

private theorem fast_no_zero_14900_14919 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 14900)).length → fastA (i.val + 14900) ≠ 0 := by
  decide

private theorem fast_no_zero_14920_14939 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 14920)).length → fastA (i.val + 14920) ≠ 0 := by
  decide

private theorem fast_no_zero_14940_14959 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 14940)).length → fastA (i.val + 14940) ≠ 0 := by
  decide

private theorem fast_no_zero_14960_14979 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 14960)).length → fastA (i.val + 14960) ≠ 0 := by
  decide

private theorem fast_no_zero_14980_14999 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 14980)).length → fastA (i.val + 14980) ≠ 0 := by
  decide

private theorem fast_no_zero_15000_15019 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 15000)).length → fastA (i.val + 15000) ≠ 0 := by
  decide

private theorem fast_no_zero_15020_15039 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 15020)).length → fastA (i.val + 15020) ≠ 0 := by
  decide

private theorem fast_no_zero_15040_15059 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 15040)).length → fastA (i.val + 15040) ≠ 0 := by
  decide

private theorem fast_no_zero_15060_15079 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 15060)).length → fastA (i.val + 15060) ≠ 0 := by
  decide

private theorem fast_no_zero_15080_15099 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 15080)).length → fastA (i.val + 15080) ≠ 0 := by
  decide

private theorem fast_no_zero_15100_15119 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 15100)).length → fastA (i.val + 15100) ≠ 0 := by
  decide

private theorem fast_no_zero_15120_15139 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 15120)).length → fastA (i.val + 15120) ≠ 0 := by
  decide

private theorem fast_no_zero_15140_15159 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 15140)).length → fastA (i.val + 15140) ≠ 0 := by
  decide

private theorem fast_no_zero_15160_15179 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 15160)).length → fastA (i.val + 15160) ≠ 0 := by
  decide

private theorem fast_no_zero_15180_15199 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 15180)).length → fastA (i.val + 15180) ≠ 0 := by
  decide

private theorem fast_no_zero_15200_15219 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 15200)).length → fastA (i.val + 15200) ≠ 0 := by
  decide

private theorem fast_no_zero_15220_15239 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 15220)).length → fastA (i.val + 15220) ≠ 0 := by
  decide

private theorem fast_no_zero_15240_15259 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 15240)).length → fastA (i.val + 15240) ≠ 0 := by
  decide

private theorem fast_no_zero_15260_15279 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 15260)).length → fastA (i.val + 15260) ≠ 0 := by
  decide

private theorem fast_no_zero_15280_15299 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 15280)).length → fastA (i.val + 15280) ≠ 0 := by
  decide

private theorem fast_no_zero_15300_15319 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 15300)).length → fastA (i.val + 15300) ≠ 0 := by
  decide

private theorem fast_no_zero_15320_15339 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 15320)).length → fastA (i.val + 15320) ≠ 0 := by
  decide

private theorem fast_no_zero_15340_15359 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 15340)).length → fastA (i.val + 15340) ≠ 0 := by
  decide

private theorem fast_no_zero_15360_15379 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 15360)).length → fastA (i.val + 15360) ≠ 0 := by
  decide

private theorem fast_no_zero_15380_15399 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 15380)).length → fastA (i.val + 15380) ≠ 0 := by
  decide

private theorem fast_no_zero_15400_15419 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 15400)).length → fastA (i.val + 15400) ≠ 0 := by
  decide

private theorem fast_no_zero_15420_15439 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 15420)).length → fastA (i.val + 15420) ≠ 0 := by
  decide

private theorem fast_no_zero_15440_15459 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 15440)).length → fastA (i.val + 15440) ≠ 0 := by
  decide

private theorem fast_no_zero_15460_15479 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 15460)).length → fastA (i.val + 15460) ≠ 0 := by
  decide

private theorem fast_no_zero_15480_15499 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 15480)).length → fastA (i.val + 15480) ≠ 0 := by
  decide

private theorem fast_no_zero_15500_15519 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 15500)).length → fastA (i.val + 15500) ≠ 0 := by
  decide

private theorem fast_no_zero_15520_15539 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 15520)).length → fastA (i.val + 15520) ≠ 0 := by
  decide

private theorem fast_no_zero_15540_15559 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 15540)).length → fastA (i.val + 15540) ≠ 0 := by
  decide

private theorem fast_no_zero_15560_15579 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 15560)).length → fastA (i.val + 15560) ≠ 0 := by
  decide

private theorem fast_no_zero_15580_15599 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 15580)).length → fastA (i.val + 15580) ≠ 0 := by
  decide

private theorem fast_no_zero_15600_15619 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 15600)).length → fastA (i.val + 15600) ≠ 0 := by
  decide

private theorem fast_no_zero_15620_15639 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 15620)).length → fastA (i.val + 15620) ≠ 0 := by
  decide

private theorem fast_no_zero_15640_15659 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 15640)).length → fastA (i.val + 15640) ≠ 0 := by
  decide

private theorem fast_no_zero_15660_15679 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 15660)).length → fastA (i.val + 15660) ≠ 0 := by
  decide

private theorem fast_no_zero_15680_15699 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 15680)).length → fastA (i.val + 15680) ≠ 0 := by
  decide

private theorem fast_no_zero_15700_15719 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 15700)).length → fastA (i.val + 15700) ≠ 0 := by
  decide

private theorem fast_no_zero_15720_15739 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 15720)).length → fastA (i.val + 15720) ≠ 0 := by
  decide

private theorem fast_no_zero_15740_15759 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 15740)).length → fastA (i.val + 15740) ≠ 0 := by
  decide

private theorem fast_no_zero_15760_15779 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 15760)).length → fastA (i.val + 15760) ≠ 0 := by
  decide

private theorem fast_no_zero_15780_15799 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 15780)).length → fastA (i.val + 15780) ≠ 0 := by
  decide

private theorem fast_no_zero_15800_15819 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 15800)).length → fastA (i.val + 15800) ≠ 0 := by
  decide

private theorem fast_no_zero_15820_15839 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 15820)).length → fastA (i.val + 15820) ≠ 0 := by
  decide

private theorem fast_no_zero_15840_15859 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 15840)).length → fastA (i.val + 15840) ≠ 0 := by
  decide

private theorem fast_no_zero_15860_15879 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 15860)).length → fastA (i.val + 15860) ≠ 0 := by
  decide

private theorem fast_no_zero_15880_15899 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 15880)).length → fastA (i.val + 15880) ≠ 0 := by
  decide

private theorem fast_no_zero_15900_15919 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 15900)).length → fastA (i.val + 15900) ≠ 0 := by
  decide

private theorem fast_no_zero_15920_15939 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 15920)).length → fastA (i.val + 15920) ≠ 0 := by
  decide

private theorem fast_no_zero_15940_15959 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 15940)).length → fastA (i.val + 15940) ≠ 0 := by
  decide

private theorem fast_no_zero_15960_15979 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 15960)).length → fastA (i.val + 15960) ≠ 0 := by
  decide

private theorem fast_no_zero_15980_15999 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 15980)).length → fastA (i.val + 15980) ≠ 0 := by
  decide

private theorem fast_no_zero_16000_16019 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 16000)).length → fastA (i.val + 16000) ≠ 0 := by
  decide

private theorem fast_no_zero_16020_16039 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 16020)).length → fastA (i.val + 16020) ≠ 0 := by
  decide

private theorem fast_no_zero_16040_16059 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 16040)).length → fastA (i.val + 16040) ≠ 0 := by
  decide

private theorem fast_no_zero_16060_16079 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 16060)).length → fastA (i.val + 16060) ≠ 0 := by
  decide

private theorem fast_no_zero_16080_16099 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 16080)).length → fastA (i.val + 16080) ≠ 0 := by
  decide

private theorem fast_no_zero_16100_16119 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 16100)).length → fastA (i.val + 16100) ≠ 0 := by
  decide

private theorem fast_no_zero_16120_16139 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 16120)).length → fastA (i.val + 16120) ≠ 0 := by
  decide

private theorem fast_no_zero_16140_16159 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 16140)).length → fastA (i.val + 16140) ≠ 0 := by
  decide

private theorem fast_no_zero_16160_16179 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 16160)).length → fastA (i.val + 16160) ≠ 0 := by
  decide

private theorem fast_no_zero_16180_16199 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 16180)).length → fastA (i.val + 16180) ≠ 0 := by
  decide

private theorem fast_no_zero_16200_16219 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 16200)).length → fastA (i.val + 16200) ≠ 0 := by
  decide

private theorem fast_no_zero_16220_16239 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 16220)).length → fastA (i.val + 16220) ≠ 0 := by
  decide

private theorem fast_no_zero_16240_16259 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 16240)).length → fastA (i.val + 16240) ≠ 0 := by
  decide

private theorem fast_no_zero_16260_16279 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 16260)).length → fastA (i.val + 16260) ≠ 0 := by
  decide

private theorem fast_no_zero_16280_16299 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 16280)).length → fastA (i.val + 16280) ≠ 0 := by
  decide

private theorem fast_no_zero_16300_16319 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 16300)).length → fastA (i.val + 16300) ≠ 0 := by
  decide

private theorem fast_no_zero_16320_16339 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 16320)).length → fastA (i.val + 16320) ≠ 0 := by
  decide

private theorem fast_no_zero_16340_16359 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 16340)).length → fastA (i.val + 16340) ≠ 0 := by
  decide

private theorem fast_no_zero_16360_16379 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 16360)).length → fastA (i.val + 16360) ≠ 0 := by
  decide

private theorem fast_no_zero_16380_16399 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 16380)).length → fastA (i.val + 16380) ≠ 0 := by
  decide

private theorem fast_no_zero_16400_16419 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 16400)).length → fastA (i.val + 16400) ≠ 0 := by
  decide

private theorem fast_no_zero_16420_16439 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 16420)).length → fastA (i.val + 16420) ≠ 0 := by
  decide

private theorem fast_no_zero_16440_16459 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 16440)).length → fastA (i.val + 16440) ≠ 0 := by
  decide

private theorem fast_no_zero_16460_16479 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 16460)).length → fastA (i.val + 16460) ≠ 0 := by
  decide

private theorem fast_no_zero_16480_16499 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 16480)).length → fastA (i.val + 16480) ≠ 0 := by
  decide

private theorem fast_no_zero_16500_16519 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 16500)).length → fastA (i.val + 16500) ≠ 0 := by
  decide

private theorem fast_no_zero_16520_16539 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 16520)).length → fastA (i.val + 16520) ≠ 0 := by
  decide

private theorem fast_no_zero_16540_16559 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 16540)).length → fastA (i.val + 16540) ≠ 0 := by
  decide

private theorem fast_no_zero_16560_16579 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 16560)).length → fastA (i.val + 16560) ≠ 0 := by
  decide

private theorem fast_no_zero_16580_16599 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 16580)).length → fastA (i.val + 16580) ≠ 0 := by
  decide

private theorem fast_no_zero_16600_16619 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 16600)).length → fastA (i.val + 16600) ≠ 0 := by
  decide

private theorem fast_no_zero_16620_16639 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 16620)).length → fastA (i.val + 16620) ≠ 0 := by
  decide

private theorem fast_no_zero_16640_16659 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 16640)).length → fastA (i.val + 16640) ≠ 0 := by
  decide

private theorem fast_no_zero_16660_16679 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 16660)).length → fastA (i.val + 16660) ≠ 0 := by
  decide

private theorem fast_no_zero_16680_16699 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 16680)).length → fastA (i.val + 16680) ≠ 0 := by
  decide

private theorem fast_no_zero_16700_16719 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 16700)).length → fastA (i.val + 16700) ≠ 0 := by
  decide

private theorem fast_no_zero_16720_16739 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 16720)).length → fastA (i.val + 16720) ≠ 0 := by
  decide

private theorem fast_no_zero_16740_16759 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 16740)).length → fastA (i.val + 16740) ≠ 0 := by
  decide

private theorem fast_no_zero_16760_16779 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 16760)).length → fastA (i.val + 16760) ≠ 0 := by
  decide

private theorem fast_no_zero_16780_16799 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 16780)).length → fastA (i.val + 16780) ≠ 0 := by
  decide

private theorem fast_no_zero_16800_16819 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 16800)).length → fastA (i.val + 16800) ≠ 0 := by
  decide

private theorem fast_no_zero_16820_16839 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 16820)).length → fastA (i.val + 16820) ≠ 0 := by
  decide

private theorem fast_no_zero_16840_16859 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 16840)).length → fastA (i.val + 16840) ≠ 0 := by
  decide

private theorem fast_no_zero_16860_16879 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 16860)).length → fastA (i.val + 16860) ≠ 0 := by
  decide

private theorem fast_no_zero_16880_16899 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 16880)).length → fastA (i.val + 16880) ≠ 0 := by
  decide

private theorem fast_no_zero_16900_16919 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 16900)).length → fastA (i.val + 16900) ≠ 0 := by
  decide

private theorem fast_no_zero_16920_16939 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 16920)).length → fastA (i.val + 16920) ≠ 0 := by
  decide

private theorem fast_no_zero_16940_16959 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 16940)).length → fastA (i.val + 16940) ≠ 0 := by
  decide

private theorem fast_no_zero_16960_16979 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 16960)).length → fastA (i.val + 16960) ≠ 0 := by
  decide

private theorem fast_no_zero_16980_16999 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 16980)).length → fastA (i.val + 16980) ≠ 0 := by
  decide

private theorem fast_no_zero_17000_17019 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 17000)).length → fastA (i.val + 17000) ≠ 0 := by
  decide

private theorem fast_no_zero_17020_17039 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 17020)).length → fastA (i.val + 17020) ≠ 0 := by
  decide

private theorem fast_no_zero_17040_17059 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 17040)).length → fastA (i.val + 17040) ≠ 0 := by
  decide

private theorem fast_no_zero_17060_17079 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 17060)).length → fastA (i.val + 17060) ≠ 0 := by
  decide

private theorem fast_no_zero_17080_17099 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 17080)).length → fastA (i.val + 17080) ≠ 0 := by
  decide

private theorem fast_no_zero_17100_17119 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 17100)).length → fastA (i.val + 17100) ≠ 0 := by
  decide

private theorem fast_no_zero_17120_17139 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 17120)).length → fastA (i.val + 17120) ≠ 0 := by
  decide

private theorem fast_no_zero_17140_17159 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 17140)).length → fastA (i.val + 17140) ≠ 0 := by
  decide

private theorem fast_no_zero_17160_17179 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 17160)).length → fastA (i.val + 17160) ≠ 0 := by
  decide

private theorem fast_no_zero_17180_17199 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 17180)).length → fastA (i.val + 17180) ≠ 0 := by
  decide

private theorem fast_no_zero_17200_17219 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 17200)).length → fastA (i.val + 17200) ≠ 0 := by
  decide

private theorem fast_no_zero_17220_17239 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 17220)).length → fastA (i.val + 17220) ≠ 0 := by
  decide

private theorem fast_no_zero_17240_17259 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 17240)).length → fastA (i.val + 17240) ≠ 0 := by
  decide

private theorem fast_no_zero_17260_17279 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 17260)).length → fastA (i.val + 17260) ≠ 0 := by
  decide

private theorem fast_no_zero_17280_17299 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 17280)).length → fastA (i.val + 17280) ≠ 0 := by
  decide

private theorem fast_no_zero_17300_17319 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 17300)).length → fastA (i.val + 17300) ≠ 0 := by
  decide

private theorem fast_no_zero_17320_17339 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 17320)).length → fastA (i.val + 17320) ≠ 0 := by
  decide

private theorem fast_no_zero_17340_17359 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 17340)).length → fastA (i.val + 17340) ≠ 0 := by
  decide

private theorem fast_no_zero_17360_17379 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 17360)).length → fastA (i.val + 17360) ≠ 0 := by
  decide

private theorem fast_no_zero_17380_17399 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 17380)).length → fastA (i.val + 17380) ≠ 0 := by
  decide

private theorem fast_no_zero_17400_17419 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 17400)).length → fastA (i.val + 17400) ≠ 0 := by
  decide

private theorem fast_no_zero_17420_17439 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 17420)).length → fastA (i.val + 17420) ≠ 0 := by
  decide

private theorem fast_no_zero_17440_17459 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 17440)).length → fastA (i.val + 17440) ≠ 0 := by
  decide

private theorem fast_no_zero_17460_17479 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 17460)).length → fastA (i.val + 17460) ≠ 0 := by
  decide

private theorem fast_no_zero_17480_17499 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 17480)).length → fastA (i.val + 17480) ≠ 0 := by
  decide

private theorem fast_no_zero_17500_17519 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 17500)).length → fastA (i.val + 17500) ≠ 0 := by
  decide

private theorem fast_no_zero_17520_17539 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 17520)).length → fastA (i.val + 17520) ≠ 0 := by
  decide

private theorem fast_no_zero_17540_17559 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 17540)).length → fastA (i.val + 17540) ≠ 0 := by
  decide

private theorem fast_no_zero_17560_17579 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 17560)).length → fastA (i.val + 17560) ≠ 0 := by
  decide

private theorem fast_no_zero_17580_17599 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 17580)).length → fastA (i.val + 17580) ≠ 0 := by
  decide

private theorem fast_no_zero_17600_17619 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 17600)).length → fastA (i.val + 17600) ≠ 0 := by
  decide

private theorem fast_no_zero_17620_17639 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 17620)).length → fastA (i.val + 17620) ≠ 0 := by
  decide

private theorem fast_no_zero_17640_17659 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 17640)).length → fastA (i.val + 17640) ≠ 0 := by
  decide

private theorem fast_no_zero_17660_17679 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 17660)).length → fastA (i.val + 17660) ≠ 0 := by
  decide

private theorem fast_no_zero_17680_17699 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 17680)).length → fastA (i.val + 17680) ≠ 0 := by
  decide

private theorem fast_no_zero_17700_17719 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 17700)).length → fastA (i.val + 17700) ≠ 0 := by
  decide

private theorem fast_no_zero_17720_17739 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 17720)).length → fastA (i.val + 17720) ≠ 0 := by
  decide

private theorem fast_no_zero_17740_17759 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 17740)).length → fastA (i.val + 17740) ≠ 0 := by
  decide

private theorem fast_no_zero_17760_17779 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 17760)).length → fastA (i.val + 17760) ≠ 0 := by
  decide

private theorem fast_no_zero_17780_17799 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 17780)).length → fastA (i.val + 17780) ≠ 0 := by
  decide

private theorem fast_no_zero_17800_17819 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 17800)).length → fastA (i.val + 17800) ≠ 0 := by
  decide

private theorem fast_no_zero_17820_17839 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 17820)).length → fastA (i.val + 17820) ≠ 0 := by
  decide

private theorem fast_no_zero_17840_17859 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 17840)).length → fastA (i.val + 17840) ≠ 0 := by
  decide

private theorem fast_no_zero_17860_17879 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 17860)).length → fastA (i.val + 17860) ≠ 0 := by
  decide

private theorem fast_no_zero_17880_17899 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 17880)).length → fastA (i.val + 17880) ≠ 0 := by
  decide

private theorem fast_no_zero_17900_17919 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 17900)).length → fastA (i.val + 17900) ≠ 0 := by
  decide

private theorem fast_no_zero_17920_17939 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 17920)).length → fastA (i.val + 17920) ≠ 0 := by
  decide

private theorem fast_no_zero_17940_17959 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 17940)).length → fastA (i.val + 17940) ≠ 0 := by
  decide

private theorem fast_no_zero_17960_17979 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 17960)).length → fastA (i.val + 17960) ≠ 0 := by
  decide

private theorem fast_no_zero_17980_17999 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 17980)).length → fastA (i.val + 17980) ≠ 0 := by
  decide

private theorem fast_no_zero_18000_18019 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 18000)).length → fastA (i.val + 18000) ≠ 0 := by
  decide

private theorem fast_no_zero_18020_18039 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 18020)).length → fastA (i.val + 18020) ≠ 0 := by
  decide

private theorem fast_no_zero_18040_18059 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 18040)).length → fastA (i.val + 18040) ≠ 0 := by
  decide

private theorem fast_no_zero_18060_18079 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 18060)).length → fastA (i.val + 18060) ≠ 0 := by
  decide

private theorem fast_no_zero_18080_18099 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 18080)).length → fastA (i.val + 18080) ≠ 0 := by
  decide

private theorem fast_no_zero_18100_18119 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 18100)).length → fastA (i.val + 18100) ≠ 0 := by
  decide

private theorem fast_no_zero_18120_18139 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 18120)).length → fastA (i.val + 18120) ≠ 0 := by
  decide

private theorem fast_no_zero_18140_18159 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 18140)).length → fastA (i.val + 18140) ≠ 0 := by
  decide

private theorem fast_no_zero_18160_18179 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 18160)).length → fastA (i.val + 18160) ≠ 0 := by
  decide

private theorem fast_no_zero_18180_18199 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 18180)).length → fastA (i.val + 18180) ≠ 0 := by
  decide

private theorem fast_no_zero_18200_18219 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 18200)).length → fastA (i.val + 18200) ≠ 0 := by
  decide

private theorem fast_no_zero_18220_18239 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 18220)).length → fastA (i.val + 18220) ≠ 0 := by
  decide

private theorem fast_no_zero_18240_18259 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 18240)).length → fastA (i.val + 18240) ≠ 0 := by
  decide

private theorem fast_no_zero_18260_18279 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 18260)).length → fastA (i.val + 18260) ≠ 0 := by
  decide

private theorem fast_no_zero_18280_18299 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 18280)).length → fastA (i.val + 18280) ≠ 0 := by
  decide

private theorem fast_no_zero_18300_18319 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 18300)).length → fastA (i.val + 18300) ≠ 0 := by
  decide

private theorem fast_no_zero_18320_18339 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 18320)).length → fastA (i.val + 18320) ≠ 0 := by
  decide

private theorem fast_no_zero_18340_18359 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 18340)).length → fastA (i.val + 18340) ≠ 0 := by
  decide

private theorem fast_no_zero_18360_18379 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 18360)).length → fastA (i.val + 18360) ≠ 0 := by
  decide

private theorem fast_no_zero_18380_18399 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 18380)).length → fastA (i.val + 18380) ≠ 0 := by
  decide

private theorem fast_no_zero_18400_18419 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 18400)).length → fastA (i.val + 18400) ≠ 0 := by
  decide

private theorem fast_no_zero_18420_18439 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 18420)).length → fastA (i.val + 18420) ≠ 0 := by
  decide

private theorem fast_no_zero_18440_18459 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 18440)).length → fastA (i.val + 18440) ≠ 0 := by
  decide

private theorem fast_no_zero_18460_18479 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 18460)).length → fastA (i.val + 18460) ≠ 0 := by
  decide

private theorem fast_no_zero_18480_18499 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 18480)).length → fastA (i.val + 18480) ≠ 0 := by
  decide

private theorem fast_no_zero_18500_18519 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 18500)).length → fastA (i.val + 18500) ≠ 0 := by
  decide

private theorem fast_no_zero_18520_18539 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 18520)).length → fastA (i.val + 18520) ≠ 0 := by
  decide

private theorem fast_no_zero_18540_18559 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 18540)).length → fastA (i.val + 18540) ≠ 0 := by
  decide

private theorem fast_no_zero_18560_18579 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 18560)).length → fastA (i.val + 18560) ≠ 0 := by
  decide

private theorem fast_no_zero_18580_18599 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 18580)).length → fastA (i.val + 18580) ≠ 0 := by
  decide

private theorem fast_no_zero_18600_18619 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 18600)).length → fastA (i.val + 18600) ≠ 0 := by
  decide

private theorem fast_no_zero_18620_18639 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 18620)).length → fastA (i.val + 18620) ≠ 0 := by
  decide

private theorem fast_no_zero_18640_18659 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 18640)).length → fastA (i.val + 18640) ≠ 0 := by
  decide

private theorem fast_no_zero_18660_18679 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 18660)).length → fastA (i.val + 18660) ≠ 0 := by
  decide

private theorem fast_no_zero_18680_18699 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 18680)).length → fastA (i.val + 18680) ≠ 0 := by
  decide

private theorem fast_no_zero_18700_18719 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 18700)).length → fastA (i.val + 18700) ≠ 0 := by
  decide

private theorem fast_no_zero_18720_18739 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 18720)).length → fastA (i.val + 18720) ≠ 0 := by
  decide

private theorem fast_no_zero_18740_18759 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 18740)).length → fastA (i.val + 18740) ≠ 0 := by
  decide

private theorem fast_no_zero_18760_18779 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 18760)).length → fastA (i.val + 18760) ≠ 0 := by
  decide

private theorem fast_no_zero_18780_18799 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 18780)).length → fastA (i.val + 18780) ≠ 0 := by
  decide

private theorem fast_no_zero_18800_18819 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 18800)).length → fastA (i.val + 18800) ≠ 0 := by
  decide

private theorem fast_no_zero_18820_18839 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 18820)).length → fastA (i.val + 18820) ≠ 0 := by
  decide

private theorem fast_no_zero_18840_18859 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 18840)).length → fastA (i.val + 18840) ≠ 0 := by
  decide

private theorem fast_no_zero_18860_18879 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 18860)).length → fastA (i.val + 18860) ≠ 0 := by
  decide

private theorem fast_no_zero_18880_18899 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 18880)).length → fastA (i.val + 18880) ≠ 0 := by
  decide

private theorem fast_no_zero_18900_18919 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 18900)).length → fastA (i.val + 18900) ≠ 0 := by
  decide

private theorem fast_no_zero_18920_18939 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 18920)).length → fastA (i.val + 18920) ≠ 0 := by
  decide

private theorem fast_no_zero_18940_18959 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 18940)).length → fastA (i.val + 18940) ≠ 0 := by
  decide

private theorem fast_no_zero_18960_18979 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 18960)).length → fastA (i.val + 18960) ≠ 0 := by
  decide

private theorem fast_no_zero_18980_18999 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 18980)).length → fastA (i.val + 18980) ≠ 0 := by
  decide

private theorem fast_no_zero_19000_19019 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 19000)).length → fastA (i.val + 19000) ≠ 0 := by
  decide

private theorem fast_no_zero_19020_19039 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 19020)).length → fastA (i.val + 19020) ≠ 0 := by
  decide

private theorem fast_no_zero_19040_19059 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 19040)).length → fastA (i.val + 19040) ≠ 0 := by
  decide

private theorem fast_no_zero_19060_19079 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 19060)).length → fastA (i.val + 19060) ≠ 0 := by
  decide

private theorem fast_no_zero_19080_19099 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 19080)).length → fastA (i.val + 19080) ≠ 0 := by
  decide

private theorem fast_no_zero_19100_19119 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 19100)).length → fastA (i.val + 19100) ≠ 0 := by
  decide

private theorem fast_no_zero_19120_19139 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 19120)).length → fastA (i.val + 19120) ≠ 0 := by
  decide

private theorem fast_no_zero_19140_19159 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 19140)).length → fastA (i.val + 19140) ≠ 0 := by
  decide

private theorem fast_no_zero_19160_19179 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 19160)).length → fastA (i.val + 19160) ≠ 0 := by
  decide

private theorem fast_no_zero_19180_19199 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 19180)).length → fastA (i.val + 19180) ≠ 0 := by
  decide

private theorem fast_no_zero_19200_19219 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 19200)).length → fastA (i.val + 19200) ≠ 0 := by
  decide

private theorem fast_no_zero_19220_19239 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 19220)).length → fastA (i.val + 19220) ≠ 0 := by
  decide

private theorem fast_no_zero_19240_19259 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 19240)).length → fastA (i.val + 19240) ≠ 0 := by
  decide

private theorem fast_no_zero_19260_19279 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 19260)).length → fastA (i.val + 19260) ≠ 0 := by
  decide

private theorem fast_no_zero_19280_19299 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 19280)).length → fastA (i.val + 19280) ≠ 0 := by
  decide

private theorem fast_no_zero_19300_19319 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 19300)).length → fastA (i.val + 19300) ≠ 0 := by
  decide

private theorem fast_no_zero_19320_19339 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 19320)).length → fastA (i.val + 19320) ≠ 0 := by
  decide

private theorem fast_no_zero_19340_19359 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 19340)).length → fastA (i.val + 19340) ≠ 0 := by
  decide

private theorem fast_no_zero_19360_19379 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 19360)).length → fastA (i.val + 19360) ≠ 0 := by
  decide

private theorem fast_no_zero_19380_19399 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 19380)).length → fastA (i.val + 19380) ≠ 0 := by
  decide

private theorem fast_no_zero_19400_19419 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 19400)).length → fastA (i.val + 19400) ≠ 0 := by
  decide

private theorem fast_no_zero_19420_19439 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 19420)).length → fastA (i.val + 19420) ≠ 0 := by
  decide

private theorem fast_no_zero_19440_19459 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 19440)).length → fastA (i.val + 19440) ≠ 0 := by
  decide

private theorem fast_no_zero_19460_19479 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 19460)).length → fastA (i.val + 19460) ≠ 0 := by
  decide

private theorem fast_no_zero_19480_19499 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 19480)).length → fastA (i.val + 19480) ≠ 0 := by
  decide

private theorem fast_no_zero_19500_19519 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 19500)).length → fastA (i.val + 19500) ≠ 0 := by
  decide

private theorem fast_no_zero_19520_19539 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 19520)).length → fastA (i.val + 19520) ≠ 0 := by
  decide

private theorem fast_no_zero_19540_19559 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 19540)).length → fastA (i.val + 19540) ≠ 0 := by
  decide

private theorem fast_no_zero_19560_19579 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 19560)).length → fastA (i.val + 19560) ≠ 0 := by
  decide

private theorem fast_no_zero_19580_19599 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 19580)).length → fastA (i.val + 19580) ≠ 0 := by
  decide

private theorem fast_no_zero_19600_19619 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 19600)).length → fastA (i.val + 19600) ≠ 0 := by
  decide

private theorem fast_no_zero_19620_19639 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 19620)).length → fastA (i.val + 19620) ≠ 0 := by
  decide

private theorem fast_no_zero_19640_19659 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 19640)).length → fastA (i.val + 19640) ≠ 0 := by
  decide

private theorem fast_no_zero_19660_19679 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 19660)).length → fastA (i.val + 19660) ≠ 0 := by
  decide

private theorem fast_no_zero_19680_19699 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 19680)).length → fastA (i.val + 19680) ≠ 0 := by
  decide

private theorem fast_no_zero_19700_19719 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 19700)).length → fastA (i.val + 19700) ≠ 0 := by
  decide

private theorem fast_no_zero_19720_19739 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 19720)).length → fastA (i.val + 19720) ≠ 0 := by
  decide

private theorem fast_no_zero_19740_19759 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 19740)).length → fastA (i.val + 19740) ≠ 0 := by
  decide

private theorem fast_no_zero_19760_19779 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 19760)).length → fastA (i.val + 19760) ≠ 0 := by
  decide

private theorem fast_no_zero_19780_19799 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 19780)).length → fastA (i.val + 19780) ≠ 0 := by
  decide

private theorem fast_no_zero_19800_19819 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 19800)).length → fastA (i.val + 19800) ≠ 0 := by
  decide

private theorem fast_no_zero_19820_19839 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 19820)).length → fastA (i.val + 19820) ≠ 0 := by
  decide

private theorem fast_no_zero_19840_19859 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 19840)).length → fastA (i.val + 19840) ≠ 0 := by
  decide

private theorem fast_no_zero_19860_19879 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 19860)).length → fastA (i.val + 19860) ≠ 0 := by
  decide

private theorem fast_no_zero_19880_19899 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 19880)).length → fastA (i.val + 19880) ≠ 0 := by
  decide

private theorem fast_no_zero_19900_19919 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 19900)).length → fastA (i.val + 19900) ≠ 0 := by
  decide

private theorem fast_no_zero_19920_19939 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 19920)).length → fastA (i.val + 19920) ≠ 0 := by
  decide

private theorem fast_no_zero_19940_19959 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 19940)).length → fastA (i.val + 19940) ≠ 0 := by
  decide

private theorem fast_no_zero_19960_19979 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 19960)).length → fastA (i.val + 19960) ≠ 0 := by
  decide

private theorem fast_no_zero_19980_19999 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 19980)).length → fastA (i.val + 19980) ≠ 0 := by
  decide

private theorem fast_no_zero_20000_20019 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 20000)).length → fastA (i.val + 20000) ≠ 0 := by
  decide

private theorem fast_no_zero_20020_20039 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 20020)).length → fastA (i.val + 20020) ≠ 0 := by
  decide

private theorem fast_no_zero_20040_20059 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 20040)).length → fastA (i.val + 20040) ≠ 0 := by
  decide

private theorem fast_no_zero_20060_20079 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 20060)).length → fastA (i.val + 20060) ≠ 0 := by
  decide

private theorem fast_no_zero_20080_20099 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 20080)).length → fastA (i.val + 20080) ≠ 0 := by
  decide

private theorem fast_no_zero_20100_20119 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 20100)).length → fastA (i.val + 20100) ≠ 0 := by
  decide

private theorem fast_no_zero_20120_20139 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 20120)).length → fastA (i.val + 20120) ≠ 0 := by
  decide

private theorem fast_no_zero_20140_20159 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 20140)).length → fastA (i.val + 20140) ≠ 0 := by
  decide

private theorem fast_no_zero_20160_20179 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 20160)).length → fastA (i.val + 20160) ≠ 0 := by
  decide

private theorem fast_no_zero_20180_20199 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 20180)).length → fastA (i.val + 20180) ≠ 0 := by
  decide

private theorem fast_no_zero_20200_20219 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 20200)).length → fastA (i.val + 20200) ≠ 0 := by
  decide

private theorem fast_no_zero_20220_20239 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 20220)).length → fastA (i.val + 20220) ≠ 0 := by
  decide

private theorem fast_no_zero_20240_20259 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 20240)).length → fastA (i.val + 20240) ≠ 0 := by
  decide

private theorem fast_no_zero_20260_20279 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 20260)).length → fastA (i.val + 20260) ≠ 0 := by
  decide

private theorem fast_no_zero_20280_20299 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 20280)).length → fastA (i.val + 20280) ≠ 0 := by
  decide

private theorem fast_no_zero_20300_20319 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 20300)).length → fastA (i.val + 20300) ≠ 0 := by
  decide

private theorem fast_no_zero_20320_20339 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 20320)).length → fastA (i.val + 20320) ≠ 0 := by
  decide

private theorem fast_no_zero_20340_20359 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 20340)).length → fastA (i.val + 20340) ≠ 0 := by
  decide

private theorem fast_no_zero_20360_20379 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 20360)).length → fastA (i.val + 20360) ≠ 0 := by
  decide

private theorem fast_no_zero_20380_20399 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 20380)).length → fastA (i.val + 20380) ≠ 0 := by
  decide

private theorem fast_no_zero_20400_20419 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 20400)).length → fastA (i.val + 20400) ≠ 0 := by
  decide

private theorem fast_no_zero_20420_20439 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 20420)).length → fastA (i.val + 20420) ≠ 0 := by
  decide

private theorem fast_no_zero_20440_20459 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 20440)).length → fastA (i.val + 20440) ≠ 0 := by
  decide

private theorem fast_no_zero_20460_20479 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 20460)).length → fastA (i.val + 20460) ≠ 0 := by
  decide

private theorem fast_no_zero_20480_20499 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 20480)).length → fastA (i.val + 20480) ≠ 0 := by
  decide

private theorem fast_no_zero_20500_20519 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 20500)).length → fastA (i.val + 20500) ≠ 0 := by
  decide

private theorem fast_no_zero_20520_20539 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 20520)).length → fastA (i.val + 20520) ≠ 0 := by
  decide

private theorem fast_no_zero_20540_20559 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 20540)).length → fastA (i.val + 20540) ≠ 0 := by
  decide

private theorem fast_no_zero_20560_20579 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 20560)).length → fastA (i.val + 20560) ≠ 0 := by
  decide

private theorem fast_no_zero_20580_20599 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 20580)).length → fastA (i.val + 20580) ≠ 0 := by
  decide

private theorem fast_no_zero_20600_20619 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 20600)).length → fastA (i.val + 20600) ≠ 0 := by
  decide

private theorem fast_no_zero_20620_20639 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 20620)).length → fastA (i.val + 20620) ≠ 0 := by
  decide

private theorem fast_no_zero_20640_20659 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 20640)).length → fastA (i.val + 20640) ≠ 0 := by
  decide

private theorem fast_no_zero_20660_20679 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 20660)).length → fastA (i.val + 20660) ≠ 0 := by
  decide

private theorem fast_no_zero_20680_20699 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 20680)).length → fastA (i.val + 20680) ≠ 0 := by
  decide

private theorem fast_no_zero_20700_20719 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 20700)).length → fastA (i.val + 20700) ≠ 0 := by
  decide

private theorem fast_no_zero_20720_20739 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 20720)).length → fastA (i.val + 20720) ≠ 0 := by
  decide

private theorem fast_no_zero_20740_20759 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 20740)).length → fastA (i.val + 20740) ≠ 0 := by
  decide

private theorem fast_no_zero_20760_20779 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 20760)).length → fastA (i.val + 20760) ≠ 0 := by
  decide

private theorem fast_no_zero_20780_20799 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 20780)).length → fastA (i.val + 20780) ≠ 0 := by
  decide

private theorem fast_no_zero_20800_20819 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 20800)).length → fastA (i.val + 20800) ≠ 0 := by
  decide

private theorem fast_no_zero_20820_20839 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 20820)).length → fastA (i.val + 20820) ≠ 0 := by
  decide

private theorem fast_no_zero_20840_20859 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 20840)).length → fastA (i.val + 20840) ≠ 0 := by
  decide

private theorem fast_no_zero_20860_20879 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 20860)).length → fastA (i.val + 20860) ≠ 0 := by
  decide

private theorem fast_no_zero_20880_20899 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 20880)).length → fastA (i.val + 20880) ≠ 0 := by
  decide

private theorem fast_no_zero_20900_20919 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 20900)).length → fastA (i.val + 20900) ≠ 0 := by
  decide

private theorem fast_no_zero_20920_20939 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 20920)).length → fastA (i.val + 20920) ≠ 0 := by
  decide

private theorem fast_no_zero_20940_20959 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 20940)).length → fastA (i.val + 20940) ≠ 0 := by
  decide

private theorem fast_no_zero_20960_20979 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 20960)).length → fastA (i.val + 20960) ≠ 0 := by
  decide

private theorem fast_no_zero_20980_20999 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 20980)).length → fastA (i.val + 20980) ≠ 0 := by
  decide

private theorem fast_no_zero_21000_21019 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 21000)).length → fastA (i.val + 21000) ≠ 0 := by
  decide

private theorem fast_no_zero_21020_21039 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 21020)).length → fastA (i.val + 21020) ≠ 0 := by
  decide

private theorem fast_no_zero_21040_21059 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 21040)).length → fastA (i.val + 21040) ≠ 0 := by
  decide

private theorem fast_no_zero_21060_21079 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 21060)).length → fastA (i.val + 21060) ≠ 0 := by
  decide

private theorem fast_no_zero_21080_21099 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 21080)).length → fastA (i.val + 21080) ≠ 0 := by
  decide

private theorem fast_no_zero_21100_21119 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 21100)).length → fastA (i.val + 21100) ≠ 0 := by
  decide

private theorem fast_no_zero_21120_21139 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 21120)).length → fastA (i.val + 21120) ≠ 0 := by
  decide

private theorem fast_no_zero_21140_21159 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 21140)).length → fastA (i.val + 21140) ≠ 0 := by
  decide

private theorem fast_no_zero_21160_21179 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 21160)).length → fastA (i.val + 21160) ≠ 0 := by
  decide

private theorem fast_no_zero_21180_21199 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 21180)).length → fastA (i.val + 21180) ≠ 0 := by
  decide

private theorem fast_no_zero_21200_21219 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 21200)).length → fastA (i.val + 21200) ≠ 0 := by
  decide

private theorem fast_no_zero_21220_21239 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 21220)).length → fastA (i.val + 21220) ≠ 0 := by
  decide

private theorem fast_no_zero_21240_21259 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 21240)).length → fastA (i.val + 21240) ≠ 0 := by
  decide

private theorem fast_no_zero_21260_21279 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 21260)).length → fastA (i.val + 21260) ≠ 0 := by
  decide

private theorem fast_no_zero_21280_21299 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 21280)).length → fastA (i.val + 21280) ≠ 0 := by
  decide

private theorem fast_no_zero_21300_21319 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 21300)).length → fastA (i.val + 21300) ≠ 0 := by
  decide

private theorem fast_no_zero_21320_21339 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 21320)).length → fastA (i.val + 21320) ≠ 0 := by
  decide

private theorem fast_no_zero_21340_21359 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 21340)).length → fastA (i.val + 21340) ≠ 0 := by
  decide

private theorem fast_no_zero_21360_21379 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 21360)).length → fastA (i.val + 21360) ≠ 0 := by
  decide

private theorem fast_no_zero_21380_21399 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 21380)).length → fastA (i.val + 21380) ≠ 0 := by
  decide

private theorem fast_no_zero_21400_21419 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 21400)).length → fastA (i.val + 21400) ≠ 0 := by
  decide

private theorem fast_no_zero_21420_21439 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 21420)).length → fastA (i.val + 21420) ≠ 0 := by
  decide

private theorem fast_no_zero_21440_21459 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 21440)).length → fastA (i.val + 21440) ≠ 0 := by
  decide

private theorem fast_no_zero_21460_21479 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 21460)).length → fastA (i.val + 21460) ≠ 0 := by
  decide

private theorem fast_no_zero_21480_21499 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 21480)).length → fastA (i.val + 21480) ≠ 0 := by
  decide

private theorem fast_no_zero_21500_21519 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 21500)).length → fastA (i.val + 21500) ≠ 0 := by
  decide

private theorem fast_no_zero_21520_21539 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 21520)).length → fastA (i.val + 21520) ≠ 0 := by
  decide

private theorem fast_no_zero_21540_21559 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 21540)).length → fastA (i.val + 21540) ≠ 0 := by
  decide

private theorem fast_no_zero_21560_21579 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 21560)).length → fastA (i.val + 21560) ≠ 0 := by
  decide

private theorem fast_no_zero_21580_21599 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 21580)).length → fastA (i.val + 21580) ≠ 0 := by
  decide

private theorem fast_no_zero_21600_21619 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 21600)).length → fastA (i.val + 21600) ≠ 0 := by
  decide

private theorem fast_no_zero_21620_21639 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 21620)).length → fastA (i.val + 21620) ≠ 0 := by
  decide

private theorem fast_no_zero_21640_21659 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 21640)).length → fastA (i.val + 21640) ≠ 0 := by
  decide

private theorem fast_no_zero_21660_21679 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 21660)).length → fastA (i.val + 21660) ≠ 0 := by
  decide

private theorem fast_no_zero_21680_21699 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 21680)).length → fastA (i.val + 21680) ≠ 0 := by
  decide

private theorem fast_no_zero_21700_21719 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 21700)).length → fastA (i.val + 21700) ≠ 0 := by
  decide

private theorem fast_no_zero_21720_21739 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 21720)).length → fastA (i.val + 21720) ≠ 0 := by
  decide

private theorem fast_no_zero_21740_21759 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 21740)).length → fastA (i.val + 21740) ≠ 0 := by
  decide

private theorem fast_no_zero_21760_21779 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 21760)).length → fastA (i.val + 21760) ≠ 0 := by
  decide

private theorem fast_no_zero_21780_21799 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 21780)).length → fastA (i.val + 21780) ≠ 0 := by
  decide

private theorem fast_no_zero_21800_21819 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 21800)).length → fastA (i.val + 21800) ≠ 0 := by
  decide

private theorem fast_no_zero_21820_21839 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 21820)).length → fastA (i.val + 21820) ≠ 0 := by
  decide

private theorem fast_no_zero_21840_21859 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 21840)).length → fastA (i.val + 21840) ≠ 0 := by
  decide

private theorem fast_no_zero_21860_21879 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 21860)).length → fastA (i.val + 21860) ≠ 0 := by
  decide

private theorem fast_no_zero_21880_21899 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 21880)).length → fastA (i.val + 21880) ≠ 0 := by
  decide

private theorem fast_no_zero_21900_21919 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 21900)).length → fastA (i.val + 21900) ≠ 0 := by
  decide

private theorem fast_no_zero_21920_21939 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 21920)).length → fastA (i.val + 21920) ≠ 0 := by
  decide

private theorem fast_no_zero_21940_21959 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 21940)).length → fastA (i.val + 21940) ≠ 0 := by
  decide

private theorem fast_no_zero_21960_21979 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 21960)).length → fastA (i.val + 21960) ≠ 0 := by
  decide

private theorem fast_no_zero_21980_21999 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 21980)).length → fastA (i.val + 21980) ≠ 0 := by
  decide

private theorem fast_no_zero_22000_22019 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 22000)).length → fastA (i.val + 22000) ≠ 0 := by
  decide

private theorem fast_no_zero_22020_22039 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 22020)).length → fastA (i.val + 22020) ≠ 0 := by
  decide

private theorem fast_no_zero_22040_22059 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 22040)).length → fastA (i.val + 22040) ≠ 0 := by
  decide

private theorem fast_no_zero_22060_22079 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 22060)).length → fastA (i.val + 22060) ≠ 0 := by
  decide

private theorem fast_no_zero_22080_22099 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 22080)).length → fastA (i.val + 22080) ≠ 0 := by
  decide

private theorem fast_no_zero_22100_22119 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 22100)).length → fastA (i.val + 22100) ≠ 0 := by
  decide

private theorem fast_no_zero_22120_22139 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 22120)).length → fastA (i.val + 22120) ≠ 0 := by
  decide

private theorem fast_no_zero_22140_22159 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 22140)).length → fastA (i.val + 22140) ≠ 0 := by
  decide

private theorem fast_no_zero_22160_22179 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 22160)).length → fastA (i.val + 22160) ≠ 0 := by
  decide

private theorem fast_no_zero_22180_22199 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 22180)).length → fastA (i.val + 22180) ≠ 0 := by
  decide

private theorem fast_no_zero_22200_22219 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 22200)).length → fastA (i.val + 22200) ≠ 0 := by
  decide

private theorem fast_no_zero_22220_22239 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 22220)).length → fastA (i.val + 22220) ≠ 0 := by
  decide

private theorem fast_no_zero_22240_22259 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 22240)).length → fastA (i.val + 22240) ≠ 0 := by
  decide

private theorem fast_no_zero_22260_22279 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 22260)).length → fastA (i.val + 22260) ≠ 0 := by
  decide

private theorem fast_no_zero_22280_22299 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 22280)).length → fastA (i.val + 22280) ≠ 0 := by
  decide

private theorem fast_no_zero_22300_22319 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 22300)).length → fastA (i.val + 22300) ≠ 0 := by
  decide

private theorem fast_no_zero_22320_22339 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 22320)).length → fastA (i.val + 22320) ≠ 0 := by
  decide

private theorem fast_no_zero_22340_22359 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 22340)).length → fastA (i.val + 22340) ≠ 0 := by
  decide

private theorem fast_no_zero_22360_22379 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 22360)).length → fastA (i.val + 22360) ≠ 0 := by
  decide

private theorem fast_no_zero_22380_22399 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 22380)).length → fastA (i.val + 22380) ≠ 0 := by
  decide

private theorem fast_no_zero_22400_22419 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 22400)).length → fastA (i.val + 22400) ≠ 0 := by
  decide

private theorem fast_no_zero_22420_22439 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 22420)).length → fastA (i.val + 22420) ≠ 0 := by
  decide

private theorem fast_no_zero_22440_22459 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 22440)).length → fastA (i.val + 22440) ≠ 0 := by
  decide

private theorem fast_no_zero_22460_22479 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 22460)).length → fastA (i.val + 22460) ≠ 0 := by
  decide

private theorem fast_no_zero_22480_22499 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 22480)).length → fastA (i.val + 22480) ≠ 0 := by
  decide

private theorem fast_no_zero_22500_22519 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 22500)).length → fastA (i.val + 22500) ≠ 0 := by
  decide

private theorem fast_no_zero_22520_22539 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 22520)).length → fastA (i.val + 22520) ≠ 0 := by
  decide

private theorem fast_no_zero_22540_22559 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 22540)).length → fastA (i.val + 22540) ≠ 0 := by
  decide

private theorem fast_no_zero_22560_22579 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 22560)).length → fastA (i.val + 22560) ≠ 0 := by
  decide

private theorem fast_no_zero_22580_22599 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 22580)).length → fastA (i.val + 22580) ≠ 0 := by
  decide

private theorem fast_no_zero_22600_22619 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 22600)).length → fastA (i.val + 22600) ≠ 0 := by
  decide

private theorem fast_no_zero_22620_22639 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 22620)).length → fastA (i.val + 22620) ≠ 0 := by
  decide

private theorem fast_no_zero_22640_22659 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 22640)).length → fastA (i.val + 22640) ≠ 0 := by
  decide

private theorem fast_no_zero_22660_22679 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 22660)).length → fastA (i.val + 22660) ≠ 0 := by
  decide

private theorem fast_no_zero_22680_22699 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 22680)).length → fastA (i.val + 22680) ≠ 0 := by
  decide

private theorem fast_no_zero_22700_22719 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 22700)).length → fastA (i.val + 22700) ≠ 0 := by
  decide

private theorem fast_no_zero_22720_22739 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 22720)).length → fastA (i.val + 22720) ≠ 0 := by
  decide

private theorem fast_no_zero_22740_22759 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 22740)).length → fastA (i.val + 22740) ≠ 0 := by
  decide

private theorem fast_no_zero_22760_22779 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 22760)).length → fastA (i.val + 22760) ≠ 0 := by
  decide

private theorem fast_no_zero_22780_22799 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 22780)).length → fastA (i.val + 22780) ≠ 0 := by
  decide

private theorem fast_no_zero_22800_22819 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 22800)).length → fastA (i.val + 22800) ≠ 0 := by
  decide

private theorem fast_no_zero_22820_22839 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 22820)).length → fastA (i.val + 22820) ≠ 0 := by
  decide

private theorem fast_no_zero_22840_22859 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 22840)).length → fastA (i.val + 22840) ≠ 0 := by
  decide

private theorem fast_no_zero_22860_22879 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 22860)).length → fastA (i.val + 22860) ≠ 0 := by
  decide

private theorem fast_no_zero_22880_22899 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 22880)).length → fastA (i.val + 22880) ≠ 0 := by
  decide

private theorem fast_no_zero_22900_22919 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 22900)).length → fastA (i.val + 22900) ≠ 0 := by
  decide

private theorem fast_no_zero_22920_22939 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 22920)).length → fastA (i.val + 22920) ≠ 0 := by
  decide

private theorem fast_no_zero_22940_22959 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 22940)).length → fastA (i.val + 22940) ≠ 0 := by
  decide

private theorem fast_no_zero_22960_22979 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 22960)).length → fastA (i.val + 22960) ≠ 0 := by
  decide

private theorem fast_no_zero_22980_22999 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 22980)).length → fastA (i.val + 22980) ≠ 0 := by
  decide

private theorem fast_no_zero_23000_23019 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 23000)).length → fastA (i.val + 23000) ≠ 0 := by
  decide

private theorem fast_no_zero_23020_23039 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 23020)).length → fastA (i.val + 23020) ≠ 0 := by
  decide

private theorem fast_no_zero_23040_23059 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 23040)).length → fastA (i.val + 23040) ≠ 0 := by
  decide

private theorem fast_no_zero_23060_23079 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 23060)).length → fastA (i.val + 23060) ≠ 0 := by
  decide

private theorem fast_no_zero_23080_23099 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 23080)).length → fastA (i.val + 23080) ≠ 0 := by
  decide

private theorem fast_no_zero_23100_23119 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 23100)).length → fastA (i.val + 23100) ≠ 0 := by
  decide

private theorem fast_no_zero_23120_23139 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 23120)).length → fastA (i.val + 23120) ≠ 0 := by
  decide

private theorem fast_no_zero_23140_23159 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 23140)).length → fastA (i.val + 23140) ≠ 0 := by
  decide

private theorem fast_no_zero_23160_23179 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 23160)).length → fastA (i.val + 23160) ≠ 0 := by
  decide

private theorem fast_no_zero_23180_23199 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 23180)).length → fastA (i.val + 23180) ≠ 0 := by
  decide

private theorem fast_no_zero_23200_23219 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 23200)).length → fastA (i.val + 23200) ≠ 0 := by
  decide

private theorem fast_no_zero_23220_23239 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 23220)).length → fastA (i.val + 23220) ≠ 0 := by
  decide

private theorem fast_no_zero_23240_23259 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 23240)).length → fastA (i.val + 23240) ≠ 0 := by
  decide

private theorem fast_no_zero_23260_23279 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 23260)).length → fastA (i.val + 23260) ≠ 0 := by
  decide

private theorem fast_no_zero_23280_23299 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 23280)).length → fastA (i.val + 23280) ≠ 0 := by
  decide

private theorem fast_no_zero_23300_23319 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 23300)).length → fastA (i.val + 23300) ≠ 0 := by
  decide

private theorem fast_no_zero_23320_23339 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 23320)).length → fastA (i.val + 23320) ≠ 0 := by
  decide

private theorem fast_no_zero_23340_23359 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 23340)).length → fastA (i.val + 23340) ≠ 0 := by
  decide

private theorem fast_no_zero_23360_23379 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 23360)).length → fastA (i.val + 23360) ≠ 0 := by
  decide

private theorem fast_no_zero_23380_23399 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 23380)).length → fastA (i.val + 23380) ≠ 0 := by
  decide

private theorem fast_no_zero_23400_23419 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 23400)).length → fastA (i.val + 23400) ≠ 0 := by
  decide

private theorem fast_no_zero_23420_23439 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 23420)).length → fastA (i.val + 23420) ≠ 0 := by
  decide

private theorem fast_no_zero_23440_23459 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 23440)).length → fastA (i.val + 23440) ≠ 0 := by
  decide

private theorem fast_no_zero_23460_23479 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 23460)).length → fastA (i.val + 23460) ≠ 0 := by
  decide

private theorem fast_no_zero_23480_23499 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 23480)).length → fastA (i.val + 23480) ≠ 0 := by
  decide

private theorem fast_no_zero_23500_23519 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 23500)).length → fastA (i.val + 23500) ≠ 0 := by
  decide

private theorem fast_no_zero_23520_23539 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 23520)).length → fastA (i.val + 23520) ≠ 0 := by
  decide

private theorem fast_no_zero_23540_23559 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 23540)).length → fastA (i.val + 23540) ≠ 0 := by
  decide

private theorem fast_no_zero_23560_23579 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 23560)).length → fastA (i.val + 23560) ≠ 0 := by
  decide

private theorem fast_no_zero_23580_23599 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 23580)).length → fastA (i.val + 23580) ≠ 0 := by
  decide

private theorem fast_no_zero_23600_23619 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 23600)).length → fastA (i.val + 23600) ≠ 0 := by
  decide

private theorem fast_no_zero_23620_23639 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 23620)).length → fastA (i.val + 23620) ≠ 0 := by
  decide

private theorem fast_no_zero_23640_23659 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 23640)).length → fastA (i.val + 23640) ≠ 0 := by
  decide

private theorem fast_no_zero_23660_23679 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 23660)).length → fastA (i.val + 23660) ≠ 0 := by
  decide

private theorem fast_no_zero_23680_23699 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 23680)).length → fastA (i.val + 23680) ≠ 0 := by
  decide

private theorem fast_no_zero_23700_23719 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 23700)).length → fastA (i.val + 23700) ≠ 0 := by
  decide

private theorem fast_no_zero_23720_23739 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 23720)).length → fastA (i.val + 23720) ≠ 0 := by
  decide

private theorem fast_no_zero_23740_23759 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 23740)).length → fastA (i.val + 23740) ≠ 0 := by
  decide

private theorem fast_no_zero_23760_23779 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 23760)).length → fastA (i.val + 23760) ≠ 0 := by
  decide

private theorem fast_no_zero_23780_23799 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 23780)).length → fastA (i.val + 23780) ≠ 0 := by
  decide

private theorem fast_no_zero_23800_23819 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 23800)).length → fastA (i.val + 23800) ≠ 0 := by
  decide

private theorem fast_no_zero_23820_23839 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 23820)).length → fastA (i.val + 23820) ≠ 0 := by
  decide

private theorem fast_no_zero_23840_23859 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 23840)).length → fastA (i.val + 23840) ≠ 0 := by
  decide

private theorem fast_no_zero_23860_23879 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 23860)).length → fastA (i.val + 23860) ≠ 0 := by
  decide

private theorem fast_no_zero_23880_23899 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 23880)).length → fastA (i.val + 23880) ≠ 0 := by
  decide

private theorem fast_no_zero_23900_23919 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 23900)).length → fastA (i.val + 23900) ≠ 0 := by
  decide

private theorem fast_no_zero_23920_23939 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 23920)).length → fastA (i.val + 23920) ≠ 0 := by
  decide

private theorem fast_no_zero_23940_23959 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 23940)).length → fastA (i.val + 23940) ≠ 0 := by
  decide

private theorem fast_no_zero_23960_23979 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 23960)).length → fastA (i.val + 23960) ≠ 0 := by
  decide

private theorem fast_no_zero_23980_23999 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 23980)).length → fastA (i.val + 23980) ≠ 0 := by
  decide

private theorem fast_no_zero_24000_24019 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 24000)).length → fastA (i.val + 24000) ≠ 0 := by
  decide

private theorem fast_no_zero_24020_24039 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 24020)).length → fastA (i.val + 24020) ≠ 0 := by
  decide

private theorem fast_no_zero_24040_24059 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 24040)).length → fastA (i.val + 24040) ≠ 0 := by
  decide

private theorem fast_no_zero_24060_24079 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 24060)).length → fastA (i.val + 24060) ≠ 0 := by
  decide

private theorem fast_no_zero_24080_24099 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 24080)).length → fastA (i.val + 24080) ≠ 0 := by
  decide

private theorem fast_no_zero_24100_24119 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 24100)).length → fastA (i.val + 24100) ≠ 0 := by
  decide

private theorem fast_no_zero_24120_24139 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 24120)).length → fastA (i.val + 24120) ≠ 0 := by
  decide

private theorem fast_no_zero_24140_24159 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 24140)).length → fastA (i.val + 24140) ≠ 0 := by
  decide

private theorem fast_no_zero_24160_24179 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 24160)).length → fastA (i.val + 24160) ≠ 0 := by
  decide

private theorem fast_no_zero_24180_24199 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 24180)).length → fastA (i.val + 24180) ≠ 0 := by
  decide

private theorem fast_no_zero_24200_24219 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 24200)).length → fastA (i.val + 24200) ≠ 0 := by
  decide

private theorem fast_no_zero_24220_24239 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 24220)).length → fastA (i.val + 24220) ≠ 0 := by
  decide

private theorem fast_no_zero_24240_24259 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 24240)).length → fastA (i.val + 24240) ≠ 0 := by
  decide

private theorem fast_no_zero_24260_24279 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 24260)).length → fastA (i.val + 24260) ≠ 0 := by
  decide

private theorem fast_no_zero_24280_24299 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 24280)).length → fastA (i.val + 24280) ≠ 0 := by
  decide

private theorem fast_no_zero_24300_24319 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 24300)).length → fastA (i.val + 24300) ≠ 0 := by
  decide

private theorem fast_no_zero_24320_24339 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 24320)).length → fastA (i.val + 24320) ≠ 0 := by
  decide

private theorem fast_no_zero_24340_24359 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 24340)).length → fastA (i.val + 24340) ≠ 0 := by
  decide

private theorem fast_no_zero_24360_24379 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 24360)).length → fastA (i.val + 24360) ≠ 0 := by
  decide

private theorem fast_no_zero_24380_24399 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 24380)).length → fastA (i.val + 24380) ≠ 0 := by
  decide

private theorem fast_no_zero_24400_24419 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 24400)).length → fastA (i.val + 24400) ≠ 0 := by
  decide

private theorem fast_no_zero_24420_24439 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 24420)).length → fastA (i.val + 24420) ≠ 0 := by
  decide

private theorem fast_no_zero_24440_24459 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 24440)).length → fastA (i.val + 24440) ≠ 0 := by
  decide

private theorem fast_no_zero_24460_24479 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 24460)).length → fastA (i.val + 24460) ≠ 0 := by
  decide

private theorem fast_no_zero_24480_24499 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 24480)).length → fastA (i.val + 24480) ≠ 0 := by
  decide

private theorem fast_no_zero_24500_24519 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 24500)).length → fastA (i.val + 24500) ≠ 0 := by
  decide

private theorem fast_no_zero_24520_24539 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 24520)).length → fastA (i.val + 24520) ≠ 0 := by
  decide

private theorem fast_no_zero_24540_24559 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 24540)).length → fastA (i.val + 24540) ≠ 0 := by
  decide

private theorem fast_no_zero_24560_24579 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 24560)).length → fastA (i.val + 24560) ≠ 0 := by
  decide

private theorem fast_no_zero_24580_24599 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 24580)).length → fastA (i.val + 24580) ≠ 0 := by
  decide

private theorem fast_no_zero_24600_24619 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 24600)).length → fastA (i.val + 24600) ≠ 0 := by
  decide

private theorem fast_no_zero_24620_24639 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 24620)).length → fastA (i.val + 24620) ≠ 0 := by
  decide

private theorem fast_no_zero_24640_24659 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 24640)).length → fastA (i.val + 24640) ≠ 0 := by
  decide

private theorem fast_no_zero_24660_24679 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 24660)).length → fastA (i.val + 24660) ≠ 0 := by
  decide

private theorem fast_no_zero_24680_24699 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 24680)).length → fastA (i.val + 24680) ≠ 0 := by
  decide

private theorem fast_no_zero_24700_24719 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 24700)).length → fastA (i.val + 24700) ≠ 0 := by
  decide

private theorem fast_no_zero_24720_24739 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 24720)).length → fastA (i.val + 24720) ≠ 0 := by
  decide

private theorem fast_no_zero_24740_24759 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 24740)).length → fastA (i.val + 24740) ≠ 0 := by
  decide

private theorem fast_no_zero_24760_24779 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 24760)).length → fastA (i.val + 24760) ≠ 0 := by
  decide

private theorem fast_no_zero_24780_24799 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 24780)).length → fastA (i.val + 24780) ≠ 0 := by
  decide

private theorem fast_no_zero_24800_24819 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 24800)).length → fastA (i.val + 24800) ≠ 0 := by
  decide

private theorem fast_no_zero_24820_24839 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 24820)).length → fastA (i.val + 24820) ≠ 0 := by
  decide

private theorem fast_no_zero_24840_24859 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 24840)).length → fastA (i.val + 24840) ≠ 0 := by
  decide

private theorem fast_no_zero_24860_24879 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 24860)).length → fastA (i.val + 24860) ≠ 0 := by
  decide

private theorem fast_no_zero_24880_24899 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 24880)).length → fastA (i.val + 24880) ≠ 0 := by
  decide

private theorem fast_no_zero_24900_24919 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 24900)).length → fastA (i.val + 24900) ≠ 0 := by
  decide

private theorem fast_no_zero_24920_24939 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 24920)).length → fastA (i.val + 24920) ≠ 0 := by
  decide

private theorem fast_no_zero_24940_24959 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 24940)).length → fastA (i.val + 24940) ≠ 0 := by
  decide

private theorem fast_no_zero_24960_24979 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 24960)).length → fastA (i.val + 24960) ≠ 0 := by
  decide

private theorem fast_no_zero_24980_24999 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 24980)).length → fastA (i.val + 24980) ≠ 0 := by
  decide

private theorem fast_no_zero_25000_25019 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 25000)).length → fastA (i.val + 25000) ≠ 0 := by
  decide

private theorem fast_no_zero_25020_25039 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 25020)).length → fastA (i.val + 25020) ≠ 0 := by
  decide

private theorem fast_no_zero_25040_25059 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 25040)).length → fastA (i.val + 25040) ≠ 0 := by
  decide

private theorem fast_no_zero_25060_25079 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 25060)).length → fastA (i.val + 25060) ≠ 0 := by
  decide

private theorem fast_no_zero_25080_25099 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 25080)).length → fastA (i.val + 25080) ≠ 0 := by
  decide

private theorem fast_no_zero_25100_25119 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 25100)).length → fastA (i.val + 25100) ≠ 0 := by
  decide

private theorem fast_no_zero_25120_25139 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 25120)).length → fastA (i.val + 25120) ≠ 0 := by
  decide

private theorem fast_no_zero_25140_25159 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 25140)).length → fastA (i.val + 25140) ≠ 0 := by
  decide

private theorem fast_no_zero_25160_25179 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 25160)).length → fastA (i.val + 25160) ≠ 0 := by
  decide

private theorem fast_no_zero_25180_25199 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 25180)).length → fastA (i.val + 25180) ≠ 0 := by
  decide

private theorem fast_no_zero_25200_25219 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 25200)).length → fastA (i.val + 25200) ≠ 0 := by
  decide

private theorem fast_no_zero_25220_25239 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 25220)).length → fastA (i.val + 25220) ≠ 0 := by
  decide

private theorem fast_no_zero_25240_25259 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 25240)).length → fastA (i.val + 25240) ≠ 0 := by
  decide

private theorem fast_no_zero_25260_25279 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 25260)).length → fastA (i.val + 25260) ≠ 0 := by
  decide

private theorem fast_no_zero_25280_25299 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 25280)).length → fastA (i.val + 25280) ≠ 0 := by
  decide

private theorem fast_no_zero_25300_25319 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 25300)).length → fastA (i.val + 25300) ≠ 0 := by
  decide

private theorem fast_no_zero_25320_25339 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 25320)).length → fastA (i.val + 25320) ≠ 0 := by
  decide

private theorem fast_no_zero_25340_25359 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 25340)).length → fastA (i.val + 25340) ≠ 0 := by
  decide

private theorem fast_no_zero_25360_25379 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 25360)).length → fastA (i.val + 25360) ≠ 0 := by
  decide

private theorem fast_no_zero_25380_25399 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 25380)).length → fastA (i.val + 25380) ≠ 0 := by
  decide

private theorem fast_no_zero_25400_25419 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 25400)).length → fastA (i.val + 25400) ≠ 0 := by
  decide

private theorem fast_no_zero_25420_25439 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 25420)).length → fastA (i.val + 25420) ≠ 0 := by
  decide

private theorem fast_no_zero_25440_25459 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 25440)).length → fastA (i.val + 25440) ≠ 0 := by
  decide

private theorem fast_no_zero_25460_25479 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 25460)).length → fastA (i.val + 25460) ≠ 0 := by
  decide

private theorem fast_no_zero_25480_25499 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 25480)).length → fastA (i.val + 25480) ≠ 0 := by
  decide

private theorem fast_no_zero_25500_25519 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 25500)).length → fastA (i.val + 25500) ≠ 0 := by
  decide

private theorem fast_no_zero_25520_25539 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 25520)).length → fastA (i.val + 25520) ≠ 0 := by
  decide

private theorem fast_no_zero_25540_25559 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 25540)).length → fastA (i.val + 25540) ≠ 0 := by
  decide

private theorem fast_no_zero_25560_25579 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 25560)).length → fastA (i.val + 25560) ≠ 0 := by
  decide

private theorem fast_no_zero_25580_25599 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 25580)).length → fastA (i.val + 25580) ≠ 0 := by
  decide

private theorem fast_no_zero_25600_25619 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 25600)).length → fastA (i.val + 25600) ≠ 0 := by
  decide

private theorem fast_no_zero_25620_25639 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 25620)).length → fastA (i.val + 25620) ≠ 0 := by
  decide

private theorem fast_no_zero_25640_25659 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 25640)).length → fastA (i.val + 25640) ≠ 0 := by
  decide

private theorem fast_no_zero_25660_25679 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 25660)).length → fastA (i.val + 25660) ≠ 0 := by
  decide

private theorem fast_no_zero_25680_25699 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 25680)).length → fastA (i.val + 25680) ≠ 0 := by
  decide

private theorem fast_no_zero_25700_25719 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 25700)).length → fastA (i.val + 25700) ≠ 0 := by
  decide

private theorem fast_no_zero_25720_25739 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 25720)).length → fastA (i.val + 25720) ≠ 0 := by
  decide

private theorem fast_no_zero_25740_25759 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 25740)).length → fastA (i.val + 25740) ≠ 0 := by
  decide

private theorem fast_no_zero_25760_25779 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 25760)).length → fastA (i.val + 25760) ≠ 0 := by
  decide

private theorem fast_no_zero_25780_25799 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 25780)).length → fastA (i.val + 25780) ≠ 0 := by
  decide

private theorem fast_no_zero_25800_25819 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 25800)).length → fastA (i.val + 25800) ≠ 0 := by
  decide

private theorem fast_no_zero_25820_25839 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 25820)).length → fastA (i.val + 25820) ≠ 0 := by
  decide

private theorem fast_no_zero_25840_25859 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 25840)).length → fastA (i.val + 25840) ≠ 0 := by
  decide

private theorem fast_no_zero_25860_25879 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 25860)).length → fastA (i.val + 25860) ≠ 0 := by
  decide

private theorem fast_no_zero_25880_25899 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 25880)).length → fastA (i.val + 25880) ≠ 0 := by
  decide

private theorem fast_no_zero_25900_25919 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 25900)).length → fastA (i.val + 25900) ≠ 0 := by
  decide

private theorem fast_no_zero_25920_25939 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 25920)).length → fastA (i.val + 25920) ≠ 0 := by
  decide

private theorem fast_no_zero_25940_25959 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 25940)).length → fastA (i.val + 25940) ≠ 0 := by
  decide

private theorem fast_no_zero_25960_25979 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 25960)).length → fastA (i.val + 25960) ≠ 0 := by
  decide

private theorem fast_no_zero_25980_25999 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 25980)).length → fastA (i.val + 25980) ≠ 0 := by
  decide

private theorem fast_no_zero_26000_26019 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 26000)).length → fastA (i.val + 26000) ≠ 0 := by
  decide

private theorem fast_no_zero_26020_26039 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 26020)).length → fastA (i.val + 26020) ≠ 0 := by
  decide

private theorem fast_no_zero_26040_26059 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 26040)).length → fastA (i.val + 26040) ≠ 0 := by
  decide

private theorem fast_no_zero_26060_26079 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 26060)).length → fastA (i.val + 26060) ≠ 0 := by
  decide

private theorem fast_no_zero_26080_26099 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 26080)).length → fastA (i.val + 26080) ≠ 0 := by
  decide

private theorem fast_no_zero_26100_26119 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 26100)).length → fastA (i.val + 26100) ≠ 0 := by
  decide

private theorem fast_no_zero_26120_26139 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 26120)).length → fastA (i.val + 26120) ≠ 0 := by
  decide

private theorem fast_no_zero_26140_26159 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 26140)).length → fastA (i.val + 26140) ≠ 0 := by
  decide

private theorem fast_no_zero_26160_26179 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 26160)).length → fastA (i.val + 26160) ≠ 0 := by
  decide

private theorem fast_no_zero_26180_26199 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 26180)).length → fastA (i.val + 26180) ≠ 0 := by
  decide

private theorem fast_no_zero_26200_26219 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 26200)).length → fastA (i.val + 26200) ≠ 0 := by
  decide

private theorem fast_no_zero_26220_26239 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 26220)).length → fastA (i.val + 26220) ≠ 0 := by
  decide

private theorem fast_no_zero_26240_26259 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 26240)).length → fastA (i.val + 26240) ≠ 0 := by
  decide

private theorem fast_no_zero_26260_26279 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 26260)).length → fastA (i.val + 26260) ≠ 0 := by
  decide

private theorem fast_no_zero_26280_26299 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 26280)).length → fastA (i.val + 26280) ≠ 0 := by
  decide

private theorem fast_no_zero_26300_26319 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 26300)).length → fastA (i.val + 26300) ≠ 0 := by
  decide

private theorem fast_no_zero_26320_26339 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 26320)).length → fastA (i.val + 26320) ≠ 0 := by
  decide

private theorem fast_no_zero_26340_26359 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 26340)).length → fastA (i.val + 26340) ≠ 0 := by
  decide

private theorem fast_no_zero_26360_26379 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 26360)).length → fastA (i.val + 26360) ≠ 0 := by
  decide

private theorem fast_no_zero_26380_26399 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 26380)).length → fastA (i.val + 26380) ≠ 0 := by
  decide

private theorem fast_no_zero_26400_26419 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 26400)).length → fastA (i.val + 26400) ≠ 0 := by
  decide

private theorem fast_no_zero_26420_26439 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 26420)).length → fastA (i.val + 26420) ≠ 0 := by
  decide

private theorem fast_no_zero_26440_26459 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 26440)).length → fastA (i.val + 26440) ≠ 0 := by
  decide

private theorem fast_no_zero_26460_26479 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 26460)).length → fastA (i.val + 26460) ≠ 0 := by
  decide

private theorem fast_no_zero_26480_26499 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 26480)).length → fastA (i.val + 26480) ≠ 0 := by
  decide

private theorem fast_no_zero_26500_26519 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 26500)).length → fastA (i.val + 26500) ≠ 0 := by
  decide

private theorem fast_no_zero_26520_26539 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 26520)).length → fastA (i.val + 26520) ≠ 0 := by
  decide

private theorem fast_no_zero_26540_26559 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 26540)).length → fastA (i.val + 26540) ≠ 0 := by
  decide

private theorem fast_no_zero_26560_26579 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 26560)).length → fastA (i.val + 26560) ≠ 0 := by
  decide

private theorem fast_no_zero_26580_26599 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 26580)).length → fastA (i.val + 26580) ≠ 0 := by
  decide

private theorem fast_no_zero_26600_26619 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 26600)).length → fastA (i.val + 26600) ≠ 0 := by
  decide

private theorem fast_no_zero_26620_26639 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 26620)).length → fastA (i.val + 26620) ≠ 0 := by
  decide

private theorem fast_no_zero_26640_26659 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 26640)).length → fastA (i.val + 26640) ≠ 0 := by
  decide

private theorem fast_no_zero_26660_26679 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 26660)).length → fastA (i.val + 26660) ≠ 0 := by
  decide

private theorem fast_no_zero_26680_26699 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 26680)).length → fastA (i.val + 26680) ≠ 0 := by
  decide

private theorem fast_no_zero_26700_26719 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 26700)).length → fastA (i.val + 26700) ≠ 0 := by
  decide

private theorem fast_no_zero_26720_26739 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 26720)).length → fastA (i.val + 26720) ≠ 0 := by
  decide

private theorem fast_no_zero_26740_26759 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 26740)).length → fastA (i.val + 26740) ≠ 0 := by
  decide

private theorem fast_no_zero_26760_26779 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 26760)).length → fastA (i.val + 26760) ≠ 0 := by
  decide

private theorem fast_no_zero_26780_26799 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 26780)).length → fastA (i.val + 26780) ≠ 0 := by
  decide

private theorem fast_no_zero_26800_26819 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 26800)).length → fastA (i.val + 26800) ≠ 0 := by
  decide

private theorem fast_no_zero_26820_26839 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 26820)).length → fastA (i.val + 26820) ≠ 0 := by
  decide

private theorem fast_no_zero_26840_26859 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 26840)).length → fastA (i.val + 26840) ≠ 0 := by
  decide

private theorem fast_no_zero_26860_26879 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 26860)).length → fastA (i.val + 26860) ≠ 0 := by
  decide

private theorem fast_no_zero_26880_26899 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 26880)).length → fastA (i.val + 26880) ≠ 0 := by
  decide

private theorem fast_no_zero_26900_26919 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 26900)).length → fastA (i.val + 26900) ≠ 0 := by
  decide

private theorem fast_no_zero_26920_26939 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 26920)).length → fastA (i.val + 26920) ≠ 0 := by
  decide

private theorem fast_no_zero_26940_26959 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 26940)).length → fastA (i.val + 26940) ≠ 0 := by
  decide

private theorem fast_no_zero_26960_26979 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 26960)).length → fastA (i.val + 26960) ≠ 0 := by
  decide

private theorem fast_no_zero_26980_26999 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 26980)).length → fastA (i.val + 26980) ≠ 0 := by
  decide

private theorem fast_no_zero_27000_27019 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 27000)).length → fastA (i.val + 27000) ≠ 0 := by
  decide

private theorem fast_no_zero_27020_27039 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 27020)).length → fastA (i.val + 27020) ≠ 0 := by
  decide

private theorem fast_no_zero_27040_27059 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 27040)).length → fastA (i.val + 27040) ≠ 0 := by
  decide

private theorem fast_no_zero_27060_27079 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 27060)).length → fastA (i.val + 27060) ≠ 0 := by
  decide

private theorem fast_no_zero_27080_27099 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 27080)).length → fastA (i.val + 27080) ≠ 0 := by
  decide

private theorem fast_no_zero_27100_27119 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 27100)).length → fastA (i.val + 27100) ≠ 0 := by
  decide

private theorem fast_no_zero_27120_27139 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 27120)).length → fastA (i.val + 27120) ≠ 0 := by
  decide

private theorem fast_no_zero_27140_27159 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 27140)).length → fastA (i.val + 27140) ≠ 0 := by
  decide

private theorem fast_no_zero_27160_27179 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 27160)).length → fastA (i.val + 27160) ≠ 0 := by
  decide

private theorem fast_no_zero_27180_27199 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 27180)).length → fastA (i.val + 27180) ≠ 0 := by
  decide

private theorem fast_no_zero_27200_27219 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 27200)).length → fastA (i.val + 27200) ≠ 0 := by
  decide

private theorem fast_no_zero_27220_27239 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 27220)).length → fastA (i.val + 27220) ≠ 0 := by
  decide

private theorem fast_no_zero_27240_27259 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 27240)).length → fastA (i.val + 27240) ≠ 0 := by
  decide

private theorem fast_no_zero_27260_27279 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 27260)).length → fastA (i.val + 27260) ≠ 0 := by
  decide

private theorem fast_no_zero_27280_27299 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 27280)).length → fastA (i.val + 27280) ≠ 0 := by
  decide

private theorem fast_no_zero_27300_27319 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 27300)).length → fastA (i.val + 27300) ≠ 0 := by
  decide

private theorem fast_no_zero_27320_27339 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 27320)).length → fastA (i.val + 27320) ≠ 0 := by
  decide

private theorem fast_no_zero_27340_27359 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 27340)).length → fastA (i.val + 27340) ≠ 0 := by
  decide

private theorem fast_no_zero_27360_27379 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 27360)).length → fastA (i.val + 27360) ≠ 0 := by
  decide

private theorem fast_no_zero_27380_27399 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 27380)).length → fastA (i.val + 27380) ≠ 0 := by
  decide

private theorem fast_no_zero_27400_27419 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 27400)).length → fastA (i.val + 27400) ≠ 0 := by
  decide

private theorem fast_no_zero_27420_27439 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 27420)).length → fastA (i.val + 27420) ≠ 0 := by
  decide

private theorem fast_no_zero_27440_27459 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 27440)).length → fastA (i.val + 27440) ≠ 0 := by
  decide

private theorem fast_no_zero_27460_27479 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 27460)).length → fastA (i.val + 27460) ≠ 0 := by
  decide

private theorem fast_no_zero_27480_27499 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 27480)).length → fastA (i.val + 27480) ≠ 0 := by
  decide

private theorem fast_no_zero_27500_27519 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 27500)).length → fastA (i.val + 27500) ≠ 0 := by
  decide

private theorem fast_no_zero_27520_27539 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 27520)).length → fastA (i.val + 27520) ≠ 0 := by
  decide

private theorem fast_no_zero_27540_27559 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 27540)).length → fastA (i.val + 27540) ≠ 0 := by
  decide

private theorem fast_no_zero_27560_27579 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 27560)).length → fastA (i.val + 27560) ≠ 0 := by
  decide

private theorem fast_no_zero_27580_27599 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 27580)).length → fastA (i.val + 27580) ≠ 0 := by
  decide

private theorem fast_no_zero_27600_27619 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 27600)).length → fastA (i.val + 27600) ≠ 0 := by
  decide

private theorem fast_no_zero_27620_27639 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 27620)).length → fastA (i.val + 27620) ≠ 0 := by
  decide

private theorem fast_no_zero_27640_27659 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 27640)).length → fastA (i.val + 27640) ≠ 0 := by
  decide

private theorem fast_no_zero_27660_27679 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 27660)).length → fastA (i.val + 27660) ≠ 0 := by
  decide

private theorem fast_no_zero_27680_27699 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 27680)).length → fastA (i.val + 27680) ≠ 0 := by
  decide

private theorem fast_no_zero_27700_27719 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 27700)).length → fastA (i.val + 27700) ≠ 0 := by
  decide

private theorem fast_no_zero_27720_27739 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 27720)).length → fastA (i.val + 27720) ≠ 0 := by
  decide

private theorem fast_no_zero_27740_27759 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 27740)).length → fastA (i.val + 27740) ≠ 0 := by
  decide

private theorem fast_no_zero_27760_27779 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 27760)).length → fastA (i.val + 27760) ≠ 0 := by
  decide

private theorem fast_no_zero_27780_27799 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 27780)).length → fastA (i.val + 27780) ≠ 0 := by
  decide

private theorem fast_no_zero_27800_27819 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 27800)).length → fastA (i.val + 27800) ≠ 0 := by
  decide

private theorem fast_no_zero_27820_27839 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 27820)).length → fastA (i.val + 27820) ≠ 0 := by
  decide

private theorem fast_no_zero_27840_27859 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 27840)).length → fastA (i.val + 27840) ≠ 0 := by
  decide

private theorem fast_no_zero_27860_27879 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 27860)).length → fastA (i.val + 27860) ≠ 0 := by
  decide

private theorem fast_no_zero_27880_27899 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 27880)).length → fastA (i.val + 27880) ≠ 0 := by
  decide

private theorem fast_no_zero_27900_27919 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 27900)).length → fastA (i.val + 27900) ≠ 0 := by
  decide

private theorem fast_no_zero_27920_27939 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 27920)).length → fastA (i.val + 27920) ≠ 0 := by
  decide

private theorem fast_no_zero_27940_27959 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 27940)).length → fastA (i.val + 27940) ≠ 0 := by
  decide

private theorem fast_no_zero_27960_27979 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 27960)).length → fastA (i.val + 27960) ≠ 0 := by
  decide

private theorem fast_no_zero_27980_27999 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 27980)).length → fastA (i.val + 27980) ≠ 0 := by
  decide

private theorem fast_no_zero_28000_28019 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 28000)).length → fastA (i.val + 28000) ≠ 0 := by
  decide

private theorem fast_no_zero_28020_28039 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 28020)).length → fastA (i.val + 28020) ≠ 0 := by
  decide

private theorem fast_no_zero_28040_28059 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 28040)).length → fastA (i.val + 28040) ≠ 0 := by
  decide

private theorem fast_no_zero_28060_28079 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 28060)).length → fastA (i.val + 28060) ≠ 0 := by
  decide

private theorem fast_no_zero_28080_28099 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 28080)).length → fastA (i.val + 28080) ≠ 0 := by
  decide

private theorem fast_no_zero_28100_28119 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 28100)).length → fastA (i.val + 28100) ≠ 0 := by
  decide

private theorem fast_no_zero_28120_28139 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 28120)).length → fastA (i.val + 28120) ≠ 0 := by
  decide

private theorem fast_no_zero_28140_28159 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 28140)).length → fastA (i.val + 28140) ≠ 0 := by
  decide

private theorem fast_no_zero_28160_28179 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 28160)).length → fastA (i.val + 28160) ≠ 0 := by
  decide

private theorem fast_no_zero_28180_28199 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 28180)).length → fastA (i.val + 28180) ≠ 0 := by
  decide

private theorem fast_no_zero_28200_28219 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 28200)).length → fastA (i.val + 28200) ≠ 0 := by
  decide

private theorem fast_no_zero_28220_28239 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 28220)).length → fastA (i.val + 28220) ≠ 0 := by
  decide

private theorem fast_no_zero_28240_28259 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 28240)).length → fastA (i.val + 28240) ≠ 0 := by
  decide

private theorem fast_no_zero_28260_28279 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 28260)).length → fastA (i.val + 28260) ≠ 0 := by
  decide

private theorem fast_no_zero_28280_28299 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 28280)).length → fastA (i.val + 28280) ≠ 0 := by
  decide

private theorem fast_no_zero_28300_28319 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 28300)).length → fastA (i.val + 28300) ≠ 0 := by
  decide

private theorem fast_no_zero_28320_28339 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 28320)).length → fastA (i.val + 28320) ≠ 0 := by
  decide

private theorem fast_no_zero_28340_28359 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 28340)).length → fastA (i.val + 28340) ≠ 0 := by
  decide

private theorem fast_no_zero_28360_28379 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 28360)).length → fastA (i.val + 28360) ≠ 0 := by
  decide

private theorem fast_no_zero_28380_28399 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 28380)).length → fastA (i.val + 28380) ≠ 0 := by
  decide

private theorem fast_no_zero_28400_28419 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 28400)).length → fastA (i.val + 28400) ≠ 0 := by
  decide

private theorem fast_no_zero_28420_28439 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 28420)).length → fastA (i.val + 28420) ≠ 0 := by
  decide

private theorem fast_no_zero_28440_28459 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 28440)).length → fastA (i.val + 28440) ≠ 0 := by
  decide

private theorem fast_no_zero_28460_28479 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 28460)).length → fastA (i.val + 28460) ≠ 0 := by
  decide

private theorem fast_no_zero_28480_28499 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 28480)).length → fastA (i.val + 28480) ≠ 0 := by
  decide

private theorem fast_no_zero_28500_28519 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 28500)).length → fastA (i.val + 28500) ≠ 0 := by
  decide

private theorem fast_no_zero_28520_28539 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 28520)).length → fastA (i.val + 28520) ≠ 0 := by
  decide

private theorem fast_no_zero_28540_28559 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 28540)).length → fastA (i.val + 28540) ≠ 0 := by
  decide

private theorem fast_no_zero_28560_28579 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 28560)).length → fastA (i.val + 28560) ≠ 0 := by
  decide

private theorem fast_no_zero_28580_28599 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 28580)).length → fastA (i.val + 28580) ≠ 0 := by
  decide

private theorem fast_no_zero_28600_28619 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 28600)).length → fastA (i.val + 28600) ≠ 0 := by
  decide

private theorem fast_no_zero_28620_28639 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 28620)).length → fastA (i.val + 28620) ≠ 0 := by
  decide

private theorem fast_no_zero_28640_28659 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 28640)).length → fastA (i.val + 28640) ≠ 0 := by
  decide

private theorem fast_no_zero_28660_28679 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 28660)).length → fastA (i.val + 28660) ≠ 0 := by
  decide

private theorem fast_no_zero_28680_28699 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 28680)).length → fastA (i.val + 28680) ≠ 0 := by
  decide

private theorem fast_no_zero_28700_28719 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 28700)).length → fastA (i.val + 28700) ≠ 0 := by
  decide

private theorem fast_no_zero_28720_28739 : ∀ i : Fin 20, 1 < (fastFactors (i.val + 28720)).length → fastA (i.val + 28720) ≠ 0 := by
  decide

private theorem fast_no_zero_28740_28748 : ∀ i : Fin 9, 1 < (fastFactors (i.val + 28740)).length → fastA (i.val + 28740) ≠ 0 := by
  decide

/--
The first composite n for which a(n)=0 is 28749. Are there others?
-/
theorem oeis_340592_conjecture_0 :
  (Nat.composite 28749 ∧ a 28749 = 0) ∧
  (∀ n : ℕ, Nat.composite n ∧ n < 28749 → a n ≠ 0) :=
by
  constructor
  · constructor
    · norm_num [Nat.composite]
    · rw [a_eq_fastA]
      decide
  · intro n hn
    rw [a_eq_fastA]
    have hc : ¬ Nat.Prime n ∧ 1 < n := by simpa [Nat.composite] using hn.1
    have hlen : 1 < (fastFactors n).length := fastFactors_length_gt_one_of_composite hc
    have hlt : n < 28749 := hn.2
    by_cases hcut : n < 14380
    ·
      by_cases hcut : n < 7180
      ·
        by_cases hcut : n < 3580
        ·
          by_cases hcut : n < 1780
          ·
            by_cases hcut : n < 880
            ·
              by_cases hcut : n < 440
              ·
                by_cases hcut : n < 220
                ·
                  by_cases hcut : n < 100
                  ·
                    by_cases hcut : n < 40
                    ·
                      by_cases hcut : n < 20
                      ·
                        let i : Fin 20 := ⟨n - 0, by omega⟩
                        have hval : i.val + 0 = n := by change n - 0 + 0 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 0)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_0_19 i hlen'
                      ·
                        let i : Fin 20 := ⟨n - 20, by omega⟩
                        have hval : i.val + 20 = n := by change n - 20 + 20 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 20)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_20_39 i hlen'
                    ·
                      by_cases hcut : n < 60
                      ·
                        let i : Fin 20 := ⟨n - 40, by omega⟩
                        have hval : i.val + 40 = n := by change n - 40 + 40 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 40)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_40_59 i hlen'
                      ·
                        by_cases hcut : n < 80
                        ·
                          let i : Fin 20 := ⟨n - 60, by omega⟩
                          have hval : i.val + 60 = n := by change n - 60 + 60 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 60)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_60_79 i hlen'
                        ·
                          let i : Fin 20 := ⟨n - 80, by omega⟩
                          have hval : i.val + 80 = n := by change n - 80 + 80 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 80)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_80_99 i hlen'
                  ·
                    by_cases hcut : n < 160
                    ·
                      by_cases hcut : n < 120
                      ·
                        let i : Fin 20 := ⟨n - 100, by omega⟩
                        have hval : i.val + 100 = n := by change n - 100 + 100 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 100)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_100_119 i hlen'
                      ·
                        by_cases hcut : n < 140
                        ·
                          let i : Fin 20 := ⟨n - 120, by omega⟩
                          have hval : i.val + 120 = n := by change n - 120 + 120 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 120)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_120_139 i hlen'
                        ·
                          let i : Fin 20 := ⟨n - 140, by omega⟩
                          have hval : i.val + 140 = n := by change n - 140 + 140 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 140)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_140_159 i hlen'
                    ·
                      by_cases hcut : n < 180
                      ·
                        let i : Fin 20 := ⟨n - 160, by omega⟩
                        have hval : i.val + 160 = n := by change n - 160 + 160 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 160)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_160_179 i hlen'
                      ·
                        by_cases hcut : n < 200
                        ·
                          let i : Fin 20 := ⟨n - 180, by omega⟩
                          have hval : i.val + 180 = n := by change n - 180 + 180 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 180)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_180_199 i hlen'
                        ·
                          let i : Fin 20 := ⟨n - 200, by omega⟩
                          have hval : i.val + 200 = n := by change n - 200 + 200 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 200)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_200_219 i hlen'
                ·
                  by_cases hcut : n < 320
                  ·
                    by_cases hcut : n < 260
                    ·
                      by_cases hcut : n < 240
                      ·
                        let i : Fin 20 := ⟨n - 220, by omega⟩
                        have hval : i.val + 220 = n := by change n - 220 + 220 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 220)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_220_239 i hlen'
                      ·
                        let i : Fin 20 := ⟨n - 240, by omega⟩
                        have hval : i.val + 240 = n := by change n - 240 + 240 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 240)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_240_259 i hlen'
                    ·
                      by_cases hcut : n < 280
                      ·
                        let i : Fin 20 := ⟨n - 260, by omega⟩
                        have hval : i.val + 260 = n := by change n - 260 + 260 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 260)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_260_279 i hlen'
                      ·
                        by_cases hcut : n < 300
                        ·
                          let i : Fin 20 := ⟨n - 280, by omega⟩
                          have hval : i.val + 280 = n := by change n - 280 + 280 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 280)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_280_299 i hlen'
                        ·
                          let i : Fin 20 := ⟨n - 300, by omega⟩
                          have hval : i.val + 300 = n := by change n - 300 + 300 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 300)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_300_319 i hlen'
                  ·
                    by_cases hcut : n < 380
                    ·
                      by_cases hcut : n < 340
                      ·
                        let i : Fin 20 := ⟨n - 320, by omega⟩
                        have hval : i.val + 320 = n := by change n - 320 + 320 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 320)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_320_339 i hlen'
                      ·
                        by_cases hcut : n < 360
                        ·
                          let i : Fin 20 := ⟨n - 340, by omega⟩
                          have hval : i.val + 340 = n := by change n - 340 + 340 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 340)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_340_359 i hlen'
                        ·
                          let i : Fin 20 := ⟨n - 360, by omega⟩
                          have hval : i.val + 360 = n := by change n - 360 + 360 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 360)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_360_379 i hlen'
                    ·
                      by_cases hcut : n < 400
                      ·
                        let i : Fin 20 := ⟨n - 380, by omega⟩
                        have hval : i.val + 380 = n := by change n - 380 + 380 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 380)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_380_399 i hlen'
                      ·
                        by_cases hcut : n < 420
                        ·
                          let i : Fin 20 := ⟨n - 400, by omega⟩
                          have hval : i.val + 400 = n := by change n - 400 + 400 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 400)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_400_419 i hlen'
                        ·
                          let i : Fin 20 := ⟨n - 420, by omega⟩
                          have hval : i.val + 420 = n := by change n - 420 + 420 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 420)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_420_439 i hlen'
              ·
                by_cases hcut : n < 660
                ·
                  by_cases hcut : n < 540
                  ·
                    by_cases hcut : n < 480
                    ·
                      by_cases hcut : n < 460
                      ·
                        let i : Fin 20 := ⟨n - 440, by omega⟩
                        have hval : i.val + 440 = n := by change n - 440 + 440 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 440)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_440_459 i hlen'
                      ·
                        let i : Fin 20 := ⟨n - 460, by omega⟩
                        have hval : i.val + 460 = n := by change n - 460 + 460 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 460)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_460_479 i hlen'
                    ·
                      by_cases hcut : n < 500
                      ·
                        let i : Fin 20 := ⟨n - 480, by omega⟩
                        have hval : i.val + 480 = n := by change n - 480 + 480 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 480)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_480_499 i hlen'
                      ·
                        by_cases hcut : n < 520
                        ·
                          let i : Fin 20 := ⟨n - 500, by omega⟩
                          have hval : i.val + 500 = n := by change n - 500 + 500 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 500)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_500_519 i hlen'
                        ·
                          let i : Fin 20 := ⟨n - 520, by omega⟩
                          have hval : i.val + 520 = n := by change n - 520 + 520 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 520)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_520_539 i hlen'
                  ·
                    by_cases hcut : n < 600
                    ·
                      by_cases hcut : n < 560
                      ·
                        let i : Fin 20 := ⟨n - 540, by omega⟩
                        have hval : i.val + 540 = n := by change n - 540 + 540 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 540)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_540_559 i hlen'
                      ·
                        by_cases hcut : n < 580
                        ·
                          let i : Fin 20 := ⟨n - 560, by omega⟩
                          have hval : i.val + 560 = n := by change n - 560 + 560 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 560)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_560_579 i hlen'
                        ·
                          let i : Fin 20 := ⟨n - 580, by omega⟩
                          have hval : i.val + 580 = n := by change n - 580 + 580 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 580)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_580_599 i hlen'
                    ·
                      by_cases hcut : n < 620
                      ·
                        let i : Fin 20 := ⟨n - 600, by omega⟩
                        have hval : i.val + 600 = n := by change n - 600 + 600 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 600)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_600_619 i hlen'
                      ·
                        by_cases hcut : n < 640
                        ·
                          let i : Fin 20 := ⟨n - 620, by omega⟩
                          have hval : i.val + 620 = n := by change n - 620 + 620 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 620)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_620_639 i hlen'
                        ·
                          let i : Fin 20 := ⟨n - 640, by omega⟩
                          have hval : i.val + 640 = n := by change n - 640 + 640 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 640)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_640_659 i hlen'
                ·
                  by_cases hcut : n < 760
                  ·
                    by_cases hcut : n < 700
                    ·
                      by_cases hcut : n < 680
                      ·
                        let i : Fin 20 := ⟨n - 660, by omega⟩
                        have hval : i.val + 660 = n := by change n - 660 + 660 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 660)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_660_679 i hlen'
                      ·
                        let i : Fin 20 := ⟨n - 680, by omega⟩
                        have hval : i.val + 680 = n := by change n - 680 + 680 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 680)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_680_699 i hlen'
                    ·
                      by_cases hcut : n < 720
                      ·
                        let i : Fin 20 := ⟨n - 700, by omega⟩
                        have hval : i.val + 700 = n := by change n - 700 + 700 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 700)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_700_719 i hlen'
                      ·
                        by_cases hcut : n < 740
                        ·
                          let i : Fin 20 := ⟨n - 720, by omega⟩
                          have hval : i.val + 720 = n := by change n - 720 + 720 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 720)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_720_739 i hlen'
                        ·
                          let i : Fin 20 := ⟨n - 740, by omega⟩
                          have hval : i.val + 740 = n := by change n - 740 + 740 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 740)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_740_759 i hlen'
                  ·
                    by_cases hcut : n < 820
                    ·
                      by_cases hcut : n < 780
                      ·
                        let i : Fin 20 := ⟨n - 760, by omega⟩
                        have hval : i.val + 760 = n := by change n - 760 + 760 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 760)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_760_779 i hlen'
                      ·
                        by_cases hcut : n < 800
                        ·
                          let i : Fin 20 := ⟨n - 780, by omega⟩
                          have hval : i.val + 780 = n := by change n - 780 + 780 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 780)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_780_799 i hlen'
                        ·
                          let i : Fin 20 := ⟨n - 800, by omega⟩
                          have hval : i.val + 800 = n := by change n - 800 + 800 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 800)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_800_819 i hlen'
                    ·
                      by_cases hcut : n < 840
                      ·
                        let i : Fin 20 := ⟨n - 820, by omega⟩
                        have hval : i.val + 820 = n := by change n - 820 + 820 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 820)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_820_839 i hlen'
                      ·
                        by_cases hcut : n < 860
                        ·
                          let i : Fin 20 := ⟨n - 840, by omega⟩
                          have hval : i.val + 840 = n := by change n - 840 + 840 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 840)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_840_859 i hlen'
                        ·
                          let i : Fin 20 := ⟨n - 860, by omega⟩
                          have hval : i.val + 860 = n := by change n - 860 + 860 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 860)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_860_879 i hlen'
            ·
              by_cases hcut : n < 1320
              ·
                by_cases hcut : n < 1100
                ·
                  by_cases hcut : n < 980
                  ·
                    by_cases hcut : n < 920
                    ·
                      by_cases hcut : n < 900
                      ·
                        let i : Fin 20 := ⟨n - 880, by omega⟩
                        have hval : i.val + 880 = n := by change n - 880 + 880 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 880)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_880_899 i hlen'
                      ·
                        let i : Fin 20 := ⟨n - 900, by omega⟩
                        have hval : i.val + 900 = n := by change n - 900 + 900 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 900)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_900_919 i hlen'
                    ·
                      by_cases hcut : n < 940
                      ·
                        let i : Fin 20 := ⟨n - 920, by omega⟩
                        have hval : i.val + 920 = n := by change n - 920 + 920 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 920)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_920_939 i hlen'
                      ·
                        by_cases hcut : n < 960
                        ·
                          let i : Fin 20 := ⟨n - 940, by omega⟩
                          have hval : i.val + 940 = n := by change n - 940 + 940 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 940)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_940_959 i hlen'
                        ·
                          let i : Fin 20 := ⟨n - 960, by omega⟩
                          have hval : i.val + 960 = n := by change n - 960 + 960 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 960)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_960_979 i hlen'
                  ·
                    by_cases hcut : n < 1040
                    ·
                      by_cases hcut : n < 1000
                      ·
                        let i : Fin 20 := ⟨n - 980, by omega⟩
                        have hval : i.val + 980 = n := by change n - 980 + 980 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 980)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_980_999 i hlen'
                      ·
                        by_cases hcut : n < 1020
                        ·
                          let i : Fin 20 := ⟨n - 1000, by omega⟩
                          have hval : i.val + 1000 = n := by change n - 1000 + 1000 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 1000)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_1000_1019 i hlen'
                        ·
                          let i : Fin 20 := ⟨n - 1020, by omega⟩
                          have hval : i.val + 1020 = n := by change n - 1020 + 1020 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 1020)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_1020_1039 i hlen'
                    ·
                      by_cases hcut : n < 1060
                      ·
                        let i : Fin 20 := ⟨n - 1040, by omega⟩
                        have hval : i.val + 1040 = n := by change n - 1040 + 1040 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 1040)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_1040_1059 i hlen'
                      ·
                        by_cases hcut : n < 1080
                        ·
                          let i : Fin 20 := ⟨n - 1060, by omega⟩
                          have hval : i.val + 1060 = n := by change n - 1060 + 1060 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 1060)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_1060_1079 i hlen'
                        ·
                          let i : Fin 20 := ⟨n - 1080, by omega⟩
                          have hval : i.val + 1080 = n := by change n - 1080 + 1080 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 1080)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_1080_1099 i hlen'
                ·
                  by_cases hcut : n < 1200
                  ·
                    by_cases hcut : n < 1140
                    ·
                      by_cases hcut : n < 1120
                      ·
                        let i : Fin 20 := ⟨n - 1100, by omega⟩
                        have hval : i.val + 1100 = n := by change n - 1100 + 1100 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 1100)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_1100_1119 i hlen'
                      ·
                        let i : Fin 20 := ⟨n - 1120, by omega⟩
                        have hval : i.val + 1120 = n := by change n - 1120 + 1120 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 1120)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_1120_1139 i hlen'
                    ·
                      by_cases hcut : n < 1160
                      ·
                        let i : Fin 20 := ⟨n - 1140, by omega⟩
                        have hval : i.val + 1140 = n := by change n - 1140 + 1140 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 1140)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_1140_1159 i hlen'
                      ·
                        by_cases hcut : n < 1180
                        ·
                          let i : Fin 20 := ⟨n - 1160, by omega⟩
                          have hval : i.val + 1160 = n := by change n - 1160 + 1160 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 1160)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_1160_1179 i hlen'
                        ·
                          let i : Fin 20 := ⟨n - 1180, by omega⟩
                          have hval : i.val + 1180 = n := by change n - 1180 + 1180 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 1180)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_1180_1199 i hlen'
                  ·
                    by_cases hcut : n < 1260
                    ·
                      by_cases hcut : n < 1220
                      ·
                        let i : Fin 20 := ⟨n - 1200, by omega⟩
                        have hval : i.val + 1200 = n := by change n - 1200 + 1200 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 1200)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_1200_1219 i hlen'
                      ·
                        by_cases hcut : n < 1240
                        ·
                          let i : Fin 20 := ⟨n - 1220, by omega⟩
                          have hval : i.val + 1220 = n := by change n - 1220 + 1220 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 1220)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_1220_1239 i hlen'
                        ·
                          let i : Fin 20 := ⟨n - 1240, by omega⟩
                          have hval : i.val + 1240 = n := by change n - 1240 + 1240 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 1240)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_1240_1259 i hlen'
                    ·
                      by_cases hcut : n < 1280
                      ·
                        let i : Fin 20 := ⟨n - 1260, by omega⟩
                        have hval : i.val + 1260 = n := by change n - 1260 + 1260 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 1260)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_1260_1279 i hlen'
                      ·
                        by_cases hcut : n < 1300
                        ·
                          let i : Fin 20 := ⟨n - 1280, by omega⟩
                          have hval : i.val + 1280 = n := by change n - 1280 + 1280 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 1280)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_1280_1299 i hlen'
                        ·
                          let i : Fin 20 := ⟨n - 1300, by omega⟩
                          have hval : i.val + 1300 = n := by change n - 1300 + 1300 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 1300)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_1300_1319 i hlen'
              ·
                by_cases hcut : n < 1540
                ·
                  by_cases hcut : n < 1420
                  ·
                    by_cases hcut : n < 1360
                    ·
                      by_cases hcut : n < 1340
                      ·
                        let i : Fin 20 := ⟨n - 1320, by omega⟩
                        have hval : i.val + 1320 = n := by change n - 1320 + 1320 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 1320)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_1320_1339 i hlen'
                      ·
                        let i : Fin 20 := ⟨n - 1340, by omega⟩
                        have hval : i.val + 1340 = n := by change n - 1340 + 1340 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 1340)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_1340_1359 i hlen'
                    ·
                      by_cases hcut : n < 1380
                      ·
                        let i : Fin 20 := ⟨n - 1360, by omega⟩
                        have hval : i.val + 1360 = n := by change n - 1360 + 1360 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 1360)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_1360_1379 i hlen'
                      ·
                        by_cases hcut : n < 1400
                        ·
                          let i : Fin 20 := ⟨n - 1380, by omega⟩
                          have hval : i.val + 1380 = n := by change n - 1380 + 1380 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 1380)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_1380_1399 i hlen'
                        ·
                          let i : Fin 20 := ⟨n - 1400, by omega⟩
                          have hval : i.val + 1400 = n := by change n - 1400 + 1400 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 1400)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_1400_1419 i hlen'
                  ·
                    by_cases hcut : n < 1480
                    ·
                      by_cases hcut : n < 1440
                      ·
                        let i : Fin 20 := ⟨n - 1420, by omega⟩
                        have hval : i.val + 1420 = n := by change n - 1420 + 1420 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 1420)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_1420_1439 i hlen'
                      ·
                        by_cases hcut : n < 1460
                        ·
                          let i : Fin 20 := ⟨n - 1440, by omega⟩
                          have hval : i.val + 1440 = n := by change n - 1440 + 1440 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 1440)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_1440_1459 i hlen'
                        ·
                          let i : Fin 20 := ⟨n - 1460, by omega⟩
                          have hval : i.val + 1460 = n := by change n - 1460 + 1460 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 1460)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_1460_1479 i hlen'
                    ·
                      by_cases hcut : n < 1500
                      ·
                        let i : Fin 20 := ⟨n - 1480, by omega⟩
                        have hval : i.val + 1480 = n := by change n - 1480 + 1480 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 1480)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_1480_1499 i hlen'
                      ·
                        by_cases hcut : n < 1520
                        ·
                          let i : Fin 20 := ⟨n - 1500, by omega⟩
                          have hval : i.val + 1500 = n := by change n - 1500 + 1500 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 1500)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_1500_1519 i hlen'
                        ·
                          let i : Fin 20 := ⟨n - 1520, by omega⟩
                          have hval : i.val + 1520 = n := by change n - 1520 + 1520 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 1520)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_1520_1539 i hlen'
                ·
                  by_cases hcut : n < 1660
                  ·
                    by_cases hcut : n < 1600
                    ·
                      by_cases hcut : n < 1560
                      ·
                        let i : Fin 20 := ⟨n - 1540, by omega⟩
                        have hval : i.val + 1540 = n := by change n - 1540 + 1540 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 1540)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_1540_1559 i hlen'
                      ·
                        by_cases hcut : n < 1580
                        ·
                          let i : Fin 20 := ⟨n - 1560, by omega⟩
                          have hval : i.val + 1560 = n := by change n - 1560 + 1560 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 1560)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_1560_1579 i hlen'
                        ·
                          let i : Fin 20 := ⟨n - 1580, by omega⟩
                          have hval : i.val + 1580 = n := by change n - 1580 + 1580 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 1580)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_1580_1599 i hlen'
                    ·
                      by_cases hcut : n < 1620
                      ·
                        let i : Fin 20 := ⟨n - 1600, by omega⟩
                        have hval : i.val + 1600 = n := by change n - 1600 + 1600 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 1600)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_1600_1619 i hlen'
                      ·
                        by_cases hcut : n < 1640
                        ·
                          let i : Fin 20 := ⟨n - 1620, by omega⟩
                          have hval : i.val + 1620 = n := by change n - 1620 + 1620 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 1620)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_1620_1639 i hlen'
                        ·
                          let i : Fin 20 := ⟨n - 1640, by omega⟩
                          have hval : i.val + 1640 = n := by change n - 1640 + 1640 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 1640)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_1640_1659 i hlen'
                  ·
                    by_cases hcut : n < 1720
                    ·
                      by_cases hcut : n < 1680
                      ·
                        let i : Fin 20 := ⟨n - 1660, by omega⟩
                        have hval : i.val + 1660 = n := by change n - 1660 + 1660 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 1660)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_1660_1679 i hlen'
                      ·
                        by_cases hcut : n < 1700
                        ·
                          let i : Fin 20 := ⟨n - 1680, by omega⟩
                          have hval : i.val + 1680 = n := by change n - 1680 + 1680 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 1680)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_1680_1699 i hlen'
                        ·
                          let i : Fin 20 := ⟨n - 1700, by omega⟩
                          have hval : i.val + 1700 = n := by change n - 1700 + 1700 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 1700)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_1700_1719 i hlen'
                    ·
                      by_cases hcut : n < 1740
                      ·
                        let i : Fin 20 := ⟨n - 1720, by omega⟩
                        have hval : i.val + 1720 = n := by change n - 1720 + 1720 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 1720)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_1720_1739 i hlen'
                      ·
                        by_cases hcut : n < 1760
                        ·
                          let i : Fin 20 := ⟨n - 1740, by omega⟩
                          have hval : i.val + 1740 = n := by change n - 1740 + 1740 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 1740)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_1740_1759 i hlen'
                        ·
                          let i : Fin 20 := ⟨n - 1760, by omega⟩
                          have hval : i.val + 1760 = n := by change n - 1760 + 1760 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 1760)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_1760_1779 i hlen'
          ·
            by_cases hcut : n < 2680
            ·
              by_cases hcut : n < 2220
              ·
                by_cases hcut : n < 2000
                ·
                  by_cases hcut : n < 1880
                  ·
                    by_cases hcut : n < 1820
                    ·
                      by_cases hcut : n < 1800
                      ·
                        let i : Fin 20 := ⟨n - 1780, by omega⟩
                        have hval : i.val + 1780 = n := by change n - 1780 + 1780 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 1780)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_1780_1799 i hlen'
                      ·
                        let i : Fin 20 := ⟨n - 1800, by omega⟩
                        have hval : i.val + 1800 = n := by change n - 1800 + 1800 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 1800)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_1800_1819 i hlen'
                    ·
                      by_cases hcut : n < 1840
                      ·
                        let i : Fin 20 := ⟨n - 1820, by omega⟩
                        have hval : i.val + 1820 = n := by change n - 1820 + 1820 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 1820)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_1820_1839 i hlen'
                      ·
                        by_cases hcut : n < 1860
                        ·
                          let i : Fin 20 := ⟨n - 1840, by omega⟩
                          have hval : i.val + 1840 = n := by change n - 1840 + 1840 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 1840)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_1840_1859 i hlen'
                        ·
                          let i : Fin 20 := ⟨n - 1860, by omega⟩
                          have hval : i.val + 1860 = n := by change n - 1860 + 1860 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 1860)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_1860_1879 i hlen'
                  ·
                    by_cases hcut : n < 1940
                    ·
                      by_cases hcut : n < 1900
                      ·
                        let i : Fin 20 := ⟨n - 1880, by omega⟩
                        have hval : i.val + 1880 = n := by change n - 1880 + 1880 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 1880)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_1880_1899 i hlen'
                      ·
                        by_cases hcut : n < 1920
                        ·
                          let i : Fin 20 := ⟨n - 1900, by omega⟩
                          have hval : i.val + 1900 = n := by change n - 1900 + 1900 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 1900)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_1900_1919 i hlen'
                        ·
                          let i : Fin 20 := ⟨n - 1920, by omega⟩
                          have hval : i.val + 1920 = n := by change n - 1920 + 1920 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 1920)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_1920_1939 i hlen'
                    ·
                      by_cases hcut : n < 1960
                      ·
                        let i : Fin 20 := ⟨n - 1940, by omega⟩
                        have hval : i.val + 1940 = n := by change n - 1940 + 1940 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 1940)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_1940_1959 i hlen'
                      ·
                        by_cases hcut : n < 1980
                        ·
                          let i : Fin 20 := ⟨n - 1960, by omega⟩
                          have hval : i.val + 1960 = n := by change n - 1960 + 1960 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 1960)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_1960_1979 i hlen'
                        ·
                          let i : Fin 20 := ⟨n - 1980, by omega⟩
                          have hval : i.val + 1980 = n := by change n - 1980 + 1980 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 1980)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_1980_1999 i hlen'
                ·
                  by_cases hcut : n < 2100
                  ·
                    by_cases hcut : n < 2040
                    ·
                      by_cases hcut : n < 2020
                      ·
                        let i : Fin 20 := ⟨n - 2000, by omega⟩
                        have hval : i.val + 2000 = n := by change n - 2000 + 2000 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 2000)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_2000_2019 i hlen'
                      ·
                        let i : Fin 20 := ⟨n - 2020, by omega⟩
                        have hval : i.val + 2020 = n := by change n - 2020 + 2020 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 2020)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_2020_2039 i hlen'
                    ·
                      by_cases hcut : n < 2060
                      ·
                        let i : Fin 20 := ⟨n - 2040, by omega⟩
                        have hval : i.val + 2040 = n := by change n - 2040 + 2040 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 2040)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_2040_2059 i hlen'
                      ·
                        by_cases hcut : n < 2080
                        ·
                          let i : Fin 20 := ⟨n - 2060, by omega⟩
                          have hval : i.val + 2060 = n := by change n - 2060 + 2060 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 2060)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_2060_2079 i hlen'
                        ·
                          let i : Fin 20 := ⟨n - 2080, by omega⟩
                          have hval : i.val + 2080 = n := by change n - 2080 + 2080 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 2080)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_2080_2099 i hlen'
                  ·
                    by_cases hcut : n < 2160
                    ·
                      by_cases hcut : n < 2120
                      ·
                        let i : Fin 20 := ⟨n - 2100, by omega⟩
                        have hval : i.val + 2100 = n := by change n - 2100 + 2100 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 2100)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_2100_2119 i hlen'
                      ·
                        by_cases hcut : n < 2140
                        ·
                          let i : Fin 20 := ⟨n - 2120, by omega⟩
                          have hval : i.val + 2120 = n := by change n - 2120 + 2120 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 2120)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_2120_2139 i hlen'
                        ·
                          let i : Fin 20 := ⟨n - 2140, by omega⟩
                          have hval : i.val + 2140 = n := by change n - 2140 + 2140 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 2140)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_2140_2159 i hlen'
                    ·
                      by_cases hcut : n < 2180
                      ·
                        let i : Fin 20 := ⟨n - 2160, by omega⟩
                        have hval : i.val + 2160 = n := by change n - 2160 + 2160 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 2160)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_2160_2179 i hlen'
                      ·
                        by_cases hcut : n < 2200
                        ·
                          let i : Fin 20 := ⟨n - 2180, by omega⟩
                          have hval : i.val + 2180 = n := by change n - 2180 + 2180 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 2180)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_2180_2199 i hlen'
                        ·
                          let i : Fin 20 := ⟨n - 2200, by omega⟩
                          have hval : i.val + 2200 = n := by change n - 2200 + 2200 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 2200)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_2200_2219 i hlen'
              ·
                by_cases hcut : n < 2440
                ·
                  by_cases hcut : n < 2320
                  ·
                    by_cases hcut : n < 2260
                    ·
                      by_cases hcut : n < 2240
                      ·
                        let i : Fin 20 := ⟨n - 2220, by omega⟩
                        have hval : i.val + 2220 = n := by change n - 2220 + 2220 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 2220)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_2220_2239 i hlen'
                      ·
                        let i : Fin 20 := ⟨n - 2240, by omega⟩
                        have hval : i.val + 2240 = n := by change n - 2240 + 2240 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 2240)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_2240_2259 i hlen'
                    ·
                      by_cases hcut : n < 2280
                      ·
                        let i : Fin 20 := ⟨n - 2260, by omega⟩
                        have hval : i.val + 2260 = n := by change n - 2260 + 2260 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 2260)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_2260_2279 i hlen'
                      ·
                        by_cases hcut : n < 2300
                        ·
                          let i : Fin 20 := ⟨n - 2280, by omega⟩
                          have hval : i.val + 2280 = n := by change n - 2280 + 2280 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 2280)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_2280_2299 i hlen'
                        ·
                          let i : Fin 20 := ⟨n - 2300, by omega⟩
                          have hval : i.val + 2300 = n := by change n - 2300 + 2300 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 2300)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_2300_2319 i hlen'
                  ·
                    by_cases hcut : n < 2380
                    ·
                      by_cases hcut : n < 2340
                      ·
                        let i : Fin 20 := ⟨n - 2320, by omega⟩
                        have hval : i.val + 2320 = n := by change n - 2320 + 2320 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 2320)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_2320_2339 i hlen'
                      ·
                        by_cases hcut : n < 2360
                        ·
                          let i : Fin 20 := ⟨n - 2340, by omega⟩
                          have hval : i.val + 2340 = n := by change n - 2340 + 2340 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 2340)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_2340_2359 i hlen'
                        ·
                          let i : Fin 20 := ⟨n - 2360, by omega⟩
                          have hval : i.val + 2360 = n := by change n - 2360 + 2360 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 2360)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_2360_2379 i hlen'
                    ·
                      by_cases hcut : n < 2400
                      ·
                        let i : Fin 20 := ⟨n - 2380, by omega⟩
                        have hval : i.val + 2380 = n := by change n - 2380 + 2380 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 2380)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_2380_2399 i hlen'
                      ·
                        by_cases hcut : n < 2420
                        ·
                          let i : Fin 20 := ⟨n - 2400, by omega⟩
                          have hval : i.val + 2400 = n := by change n - 2400 + 2400 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 2400)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_2400_2419 i hlen'
                        ·
                          let i : Fin 20 := ⟨n - 2420, by omega⟩
                          have hval : i.val + 2420 = n := by change n - 2420 + 2420 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 2420)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_2420_2439 i hlen'
                ·
                  by_cases hcut : n < 2560
                  ·
                    by_cases hcut : n < 2500
                    ·
                      by_cases hcut : n < 2460
                      ·
                        let i : Fin 20 := ⟨n - 2440, by omega⟩
                        have hval : i.val + 2440 = n := by change n - 2440 + 2440 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 2440)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_2440_2459 i hlen'
                      ·
                        by_cases hcut : n < 2480
                        ·
                          let i : Fin 20 := ⟨n - 2460, by omega⟩
                          have hval : i.val + 2460 = n := by change n - 2460 + 2460 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 2460)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_2460_2479 i hlen'
                        ·
                          let i : Fin 20 := ⟨n - 2480, by omega⟩
                          have hval : i.val + 2480 = n := by change n - 2480 + 2480 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 2480)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_2480_2499 i hlen'
                    ·
                      by_cases hcut : n < 2520
                      ·
                        let i : Fin 20 := ⟨n - 2500, by omega⟩
                        have hval : i.val + 2500 = n := by change n - 2500 + 2500 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 2500)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_2500_2519 i hlen'
                      ·
                        by_cases hcut : n < 2540
                        ·
                          let i : Fin 20 := ⟨n - 2520, by omega⟩
                          have hval : i.val + 2520 = n := by change n - 2520 + 2520 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 2520)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_2520_2539 i hlen'
                        ·
                          let i : Fin 20 := ⟨n - 2540, by omega⟩
                          have hval : i.val + 2540 = n := by change n - 2540 + 2540 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 2540)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_2540_2559 i hlen'
                  ·
                    by_cases hcut : n < 2620
                    ·
                      by_cases hcut : n < 2580
                      ·
                        let i : Fin 20 := ⟨n - 2560, by omega⟩
                        have hval : i.val + 2560 = n := by change n - 2560 + 2560 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 2560)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_2560_2579 i hlen'
                      ·
                        by_cases hcut : n < 2600
                        ·
                          let i : Fin 20 := ⟨n - 2580, by omega⟩
                          have hval : i.val + 2580 = n := by change n - 2580 + 2580 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 2580)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_2580_2599 i hlen'
                        ·
                          let i : Fin 20 := ⟨n - 2600, by omega⟩
                          have hval : i.val + 2600 = n := by change n - 2600 + 2600 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 2600)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_2600_2619 i hlen'
                    ·
                      by_cases hcut : n < 2640
                      ·
                        let i : Fin 20 := ⟨n - 2620, by omega⟩
                        have hval : i.val + 2620 = n := by change n - 2620 + 2620 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 2620)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_2620_2639 i hlen'
                      ·
                        by_cases hcut : n < 2660
                        ·
                          let i : Fin 20 := ⟨n - 2640, by omega⟩
                          have hval : i.val + 2640 = n := by change n - 2640 + 2640 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 2640)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_2640_2659 i hlen'
                        ·
                          let i : Fin 20 := ⟨n - 2660, by omega⟩
                          have hval : i.val + 2660 = n := by change n - 2660 + 2660 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 2660)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_2660_2679 i hlen'
            ·
              by_cases hcut : n < 3120
              ·
                by_cases hcut : n < 2900
                ·
                  by_cases hcut : n < 2780
                  ·
                    by_cases hcut : n < 2720
                    ·
                      by_cases hcut : n < 2700
                      ·
                        let i : Fin 20 := ⟨n - 2680, by omega⟩
                        have hval : i.val + 2680 = n := by change n - 2680 + 2680 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 2680)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_2680_2699 i hlen'
                      ·
                        let i : Fin 20 := ⟨n - 2700, by omega⟩
                        have hval : i.val + 2700 = n := by change n - 2700 + 2700 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 2700)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_2700_2719 i hlen'
                    ·
                      by_cases hcut : n < 2740
                      ·
                        let i : Fin 20 := ⟨n - 2720, by omega⟩
                        have hval : i.val + 2720 = n := by change n - 2720 + 2720 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 2720)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_2720_2739 i hlen'
                      ·
                        by_cases hcut : n < 2760
                        ·
                          let i : Fin 20 := ⟨n - 2740, by omega⟩
                          have hval : i.val + 2740 = n := by change n - 2740 + 2740 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 2740)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_2740_2759 i hlen'
                        ·
                          let i : Fin 20 := ⟨n - 2760, by omega⟩
                          have hval : i.val + 2760 = n := by change n - 2760 + 2760 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 2760)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_2760_2779 i hlen'
                  ·
                    by_cases hcut : n < 2840
                    ·
                      by_cases hcut : n < 2800
                      ·
                        let i : Fin 20 := ⟨n - 2780, by omega⟩
                        have hval : i.val + 2780 = n := by change n - 2780 + 2780 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 2780)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_2780_2799 i hlen'
                      ·
                        by_cases hcut : n < 2820
                        ·
                          let i : Fin 20 := ⟨n - 2800, by omega⟩
                          have hval : i.val + 2800 = n := by change n - 2800 + 2800 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 2800)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_2800_2819 i hlen'
                        ·
                          let i : Fin 20 := ⟨n - 2820, by omega⟩
                          have hval : i.val + 2820 = n := by change n - 2820 + 2820 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 2820)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_2820_2839 i hlen'
                    ·
                      by_cases hcut : n < 2860
                      ·
                        let i : Fin 20 := ⟨n - 2840, by omega⟩
                        have hval : i.val + 2840 = n := by change n - 2840 + 2840 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 2840)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_2840_2859 i hlen'
                      ·
                        by_cases hcut : n < 2880
                        ·
                          let i : Fin 20 := ⟨n - 2860, by omega⟩
                          have hval : i.val + 2860 = n := by change n - 2860 + 2860 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 2860)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_2860_2879 i hlen'
                        ·
                          let i : Fin 20 := ⟨n - 2880, by omega⟩
                          have hval : i.val + 2880 = n := by change n - 2880 + 2880 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 2880)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_2880_2899 i hlen'
                ·
                  by_cases hcut : n < 3000
                  ·
                    by_cases hcut : n < 2940
                    ·
                      by_cases hcut : n < 2920
                      ·
                        let i : Fin 20 := ⟨n - 2900, by omega⟩
                        have hval : i.val + 2900 = n := by change n - 2900 + 2900 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 2900)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_2900_2919 i hlen'
                      ·
                        let i : Fin 20 := ⟨n - 2920, by omega⟩
                        have hval : i.val + 2920 = n := by change n - 2920 + 2920 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 2920)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_2920_2939 i hlen'
                    ·
                      by_cases hcut : n < 2960
                      ·
                        let i : Fin 20 := ⟨n - 2940, by omega⟩
                        have hval : i.val + 2940 = n := by change n - 2940 + 2940 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 2940)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_2940_2959 i hlen'
                      ·
                        by_cases hcut : n < 2980
                        ·
                          let i : Fin 20 := ⟨n - 2960, by omega⟩
                          have hval : i.val + 2960 = n := by change n - 2960 + 2960 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 2960)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_2960_2979 i hlen'
                        ·
                          let i : Fin 20 := ⟨n - 2980, by omega⟩
                          have hval : i.val + 2980 = n := by change n - 2980 + 2980 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 2980)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_2980_2999 i hlen'
                  ·
                    by_cases hcut : n < 3060
                    ·
                      by_cases hcut : n < 3020
                      ·
                        let i : Fin 20 := ⟨n - 3000, by omega⟩
                        have hval : i.val + 3000 = n := by change n - 3000 + 3000 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 3000)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_3000_3019 i hlen'
                      ·
                        by_cases hcut : n < 3040
                        ·
                          let i : Fin 20 := ⟨n - 3020, by omega⟩
                          have hval : i.val + 3020 = n := by change n - 3020 + 3020 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 3020)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_3020_3039 i hlen'
                        ·
                          let i : Fin 20 := ⟨n - 3040, by omega⟩
                          have hval : i.val + 3040 = n := by change n - 3040 + 3040 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 3040)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_3040_3059 i hlen'
                    ·
                      by_cases hcut : n < 3080
                      ·
                        let i : Fin 20 := ⟨n - 3060, by omega⟩
                        have hval : i.val + 3060 = n := by change n - 3060 + 3060 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 3060)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_3060_3079 i hlen'
                      ·
                        by_cases hcut : n < 3100
                        ·
                          let i : Fin 20 := ⟨n - 3080, by omega⟩
                          have hval : i.val + 3080 = n := by change n - 3080 + 3080 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 3080)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_3080_3099 i hlen'
                        ·
                          let i : Fin 20 := ⟨n - 3100, by omega⟩
                          have hval : i.val + 3100 = n := by change n - 3100 + 3100 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 3100)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_3100_3119 i hlen'
              ·
                by_cases hcut : n < 3340
                ·
                  by_cases hcut : n < 3220
                  ·
                    by_cases hcut : n < 3160
                    ·
                      by_cases hcut : n < 3140
                      ·
                        let i : Fin 20 := ⟨n - 3120, by omega⟩
                        have hval : i.val + 3120 = n := by change n - 3120 + 3120 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 3120)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_3120_3139 i hlen'
                      ·
                        let i : Fin 20 := ⟨n - 3140, by omega⟩
                        have hval : i.val + 3140 = n := by change n - 3140 + 3140 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 3140)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_3140_3159 i hlen'
                    ·
                      by_cases hcut : n < 3180
                      ·
                        let i : Fin 20 := ⟨n - 3160, by omega⟩
                        have hval : i.val + 3160 = n := by change n - 3160 + 3160 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 3160)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_3160_3179 i hlen'
                      ·
                        by_cases hcut : n < 3200
                        ·
                          let i : Fin 20 := ⟨n - 3180, by omega⟩
                          have hval : i.val + 3180 = n := by change n - 3180 + 3180 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 3180)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_3180_3199 i hlen'
                        ·
                          let i : Fin 20 := ⟨n - 3200, by omega⟩
                          have hval : i.val + 3200 = n := by change n - 3200 + 3200 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 3200)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_3200_3219 i hlen'
                  ·
                    by_cases hcut : n < 3280
                    ·
                      by_cases hcut : n < 3240
                      ·
                        let i : Fin 20 := ⟨n - 3220, by omega⟩
                        have hval : i.val + 3220 = n := by change n - 3220 + 3220 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 3220)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_3220_3239 i hlen'
                      ·
                        by_cases hcut : n < 3260
                        ·
                          let i : Fin 20 := ⟨n - 3240, by omega⟩
                          have hval : i.val + 3240 = n := by change n - 3240 + 3240 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 3240)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_3240_3259 i hlen'
                        ·
                          let i : Fin 20 := ⟨n - 3260, by omega⟩
                          have hval : i.val + 3260 = n := by change n - 3260 + 3260 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 3260)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_3260_3279 i hlen'
                    ·
                      by_cases hcut : n < 3300
                      ·
                        let i : Fin 20 := ⟨n - 3280, by omega⟩
                        have hval : i.val + 3280 = n := by change n - 3280 + 3280 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 3280)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_3280_3299 i hlen'
                      ·
                        by_cases hcut : n < 3320
                        ·
                          let i : Fin 20 := ⟨n - 3300, by omega⟩
                          have hval : i.val + 3300 = n := by change n - 3300 + 3300 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 3300)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_3300_3319 i hlen'
                        ·
                          let i : Fin 20 := ⟨n - 3320, by omega⟩
                          have hval : i.val + 3320 = n := by change n - 3320 + 3320 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 3320)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_3320_3339 i hlen'
                ·
                  by_cases hcut : n < 3460
                  ·
                    by_cases hcut : n < 3400
                    ·
                      by_cases hcut : n < 3360
                      ·
                        let i : Fin 20 := ⟨n - 3340, by omega⟩
                        have hval : i.val + 3340 = n := by change n - 3340 + 3340 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 3340)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_3340_3359 i hlen'
                      ·
                        by_cases hcut : n < 3380
                        ·
                          let i : Fin 20 := ⟨n - 3360, by omega⟩
                          have hval : i.val + 3360 = n := by change n - 3360 + 3360 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 3360)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_3360_3379 i hlen'
                        ·
                          let i : Fin 20 := ⟨n - 3380, by omega⟩
                          have hval : i.val + 3380 = n := by change n - 3380 + 3380 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 3380)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_3380_3399 i hlen'
                    ·
                      by_cases hcut : n < 3420
                      ·
                        let i : Fin 20 := ⟨n - 3400, by omega⟩
                        have hval : i.val + 3400 = n := by change n - 3400 + 3400 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 3400)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_3400_3419 i hlen'
                      ·
                        by_cases hcut : n < 3440
                        ·
                          let i : Fin 20 := ⟨n - 3420, by omega⟩
                          have hval : i.val + 3420 = n := by change n - 3420 + 3420 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 3420)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_3420_3439 i hlen'
                        ·
                          let i : Fin 20 := ⟨n - 3440, by omega⟩
                          have hval : i.val + 3440 = n := by change n - 3440 + 3440 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 3440)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_3440_3459 i hlen'
                  ·
                    by_cases hcut : n < 3520
                    ·
                      by_cases hcut : n < 3480
                      ·
                        let i : Fin 20 := ⟨n - 3460, by omega⟩
                        have hval : i.val + 3460 = n := by change n - 3460 + 3460 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 3460)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_3460_3479 i hlen'
                      ·
                        by_cases hcut : n < 3500
                        ·
                          let i : Fin 20 := ⟨n - 3480, by omega⟩
                          have hval : i.val + 3480 = n := by change n - 3480 + 3480 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 3480)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_3480_3499 i hlen'
                        ·
                          let i : Fin 20 := ⟨n - 3500, by omega⟩
                          have hval : i.val + 3500 = n := by change n - 3500 + 3500 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 3500)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_3500_3519 i hlen'
                    ·
                      by_cases hcut : n < 3540
                      ·
                        let i : Fin 20 := ⟨n - 3520, by omega⟩
                        have hval : i.val + 3520 = n := by change n - 3520 + 3520 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 3520)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_3520_3539 i hlen'
                      ·
                        by_cases hcut : n < 3560
                        ·
                          let i : Fin 20 := ⟨n - 3540, by omega⟩
                          have hval : i.val + 3540 = n := by change n - 3540 + 3540 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 3540)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_3540_3559 i hlen'
                        ·
                          let i : Fin 20 := ⟨n - 3560, by omega⟩
                          have hval : i.val + 3560 = n := by change n - 3560 + 3560 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 3560)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_3560_3579 i hlen'
        ·
          by_cases hcut : n < 5380
          ·
            by_cases hcut : n < 4480
            ·
              by_cases hcut : n < 4020
              ·
                by_cases hcut : n < 3800
                ·
                  by_cases hcut : n < 3680
                  ·
                    by_cases hcut : n < 3620
                    ·
                      by_cases hcut : n < 3600
                      ·
                        let i : Fin 20 := ⟨n - 3580, by omega⟩
                        have hval : i.val + 3580 = n := by change n - 3580 + 3580 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 3580)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_3580_3599 i hlen'
                      ·
                        let i : Fin 20 := ⟨n - 3600, by omega⟩
                        have hval : i.val + 3600 = n := by change n - 3600 + 3600 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 3600)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_3600_3619 i hlen'
                    ·
                      by_cases hcut : n < 3640
                      ·
                        let i : Fin 20 := ⟨n - 3620, by omega⟩
                        have hval : i.val + 3620 = n := by change n - 3620 + 3620 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 3620)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_3620_3639 i hlen'
                      ·
                        by_cases hcut : n < 3660
                        ·
                          let i : Fin 20 := ⟨n - 3640, by omega⟩
                          have hval : i.val + 3640 = n := by change n - 3640 + 3640 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 3640)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_3640_3659 i hlen'
                        ·
                          let i : Fin 20 := ⟨n - 3660, by omega⟩
                          have hval : i.val + 3660 = n := by change n - 3660 + 3660 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 3660)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_3660_3679 i hlen'
                  ·
                    by_cases hcut : n < 3740
                    ·
                      by_cases hcut : n < 3700
                      ·
                        let i : Fin 20 := ⟨n - 3680, by omega⟩
                        have hval : i.val + 3680 = n := by change n - 3680 + 3680 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 3680)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_3680_3699 i hlen'
                      ·
                        by_cases hcut : n < 3720
                        ·
                          let i : Fin 20 := ⟨n - 3700, by omega⟩
                          have hval : i.val + 3700 = n := by change n - 3700 + 3700 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 3700)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_3700_3719 i hlen'
                        ·
                          let i : Fin 20 := ⟨n - 3720, by omega⟩
                          have hval : i.val + 3720 = n := by change n - 3720 + 3720 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 3720)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_3720_3739 i hlen'
                    ·
                      by_cases hcut : n < 3760
                      ·
                        let i : Fin 20 := ⟨n - 3740, by omega⟩
                        have hval : i.val + 3740 = n := by change n - 3740 + 3740 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 3740)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_3740_3759 i hlen'
                      ·
                        by_cases hcut : n < 3780
                        ·
                          let i : Fin 20 := ⟨n - 3760, by omega⟩
                          have hval : i.val + 3760 = n := by change n - 3760 + 3760 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 3760)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_3760_3779 i hlen'
                        ·
                          let i : Fin 20 := ⟨n - 3780, by omega⟩
                          have hval : i.val + 3780 = n := by change n - 3780 + 3780 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 3780)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_3780_3799 i hlen'
                ·
                  by_cases hcut : n < 3900
                  ·
                    by_cases hcut : n < 3840
                    ·
                      by_cases hcut : n < 3820
                      ·
                        let i : Fin 20 := ⟨n - 3800, by omega⟩
                        have hval : i.val + 3800 = n := by change n - 3800 + 3800 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 3800)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_3800_3819 i hlen'
                      ·
                        let i : Fin 20 := ⟨n - 3820, by omega⟩
                        have hval : i.val + 3820 = n := by change n - 3820 + 3820 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 3820)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_3820_3839 i hlen'
                    ·
                      by_cases hcut : n < 3860
                      ·
                        let i : Fin 20 := ⟨n - 3840, by omega⟩
                        have hval : i.val + 3840 = n := by change n - 3840 + 3840 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 3840)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_3840_3859 i hlen'
                      ·
                        by_cases hcut : n < 3880
                        ·
                          let i : Fin 20 := ⟨n - 3860, by omega⟩
                          have hval : i.val + 3860 = n := by change n - 3860 + 3860 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 3860)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_3860_3879 i hlen'
                        ·
                          let i : Fin 20 := ⟨n - 3880, by omega⟩
                          have hval : i.val + 3880 = n := by change n - 3880 + 3880 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 3880)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_3880_3899 i hlen'
                  ·
                    by_cases hcut : n < 3960
                    ·
                      by_cases hcut : n < 3920
                      ·
                        let i : Fin 20 := ⟨n - 3900, by omega⟩
                        have hval : i.val + 3900 = n := by change n - 3900 + 3900 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 3900)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_3900_3919 i hlen'
                      ·
                        by_cases hcut : n < 3940
                        ·
                          let i : Fin 20 := ⟨n - 3920, by omega⟩
                          have hval : i.val + 3920 = n := by change n - 3920 + 3920 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 3920)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_3920_3939 i hlen'
                        ·
                          let i : Fin 20 := ⟨n - 3940, by omega⟩
                          have hval : i.val + 3940 = n := by change n - 3940 + 3940 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 3940)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_3940_3959 i hlen'
                    ·
                      by_cases hcut : n < 3980
                      ·
                        let i : Fin 20 := ⟨n - 3960, by omega⟩
                        have hval : i.val + 3960 = n := by change n - 3960 + 3960 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 3960)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_3960_3979 i hlen'
                      ·
                        by_cases hcut : n < 4000
                        ·
                          let i : Fin 20 := ⟨n - 3980, by omega⟩
                          have hval : i.val + 3980 = n := by change n - 3980 + 3980 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 3980)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_3980_3999 i hlen'
                        ·
                          let i : Fin 20 := ⟨n - 4000, by omega⟩
                          have hval : i.val + 4000 = n := by change n - 4000 + 4000 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 4000)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_4000_4019 i hlen'
              ·
                by_cases hcut : n < 4240
                ·
                  by_cases hcut : n < 4120
                  ·
                    by_cases hcut : n < 4060
                    ·
                      by_cases hcut : n < 4040
                      ·
                        let i : Fin 20 := ⟨n - 4020, by omega⟩
                        have hval : i.val + 4020 = n := by change n - 4020 + 4020 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 4020)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_4020_4039 i hlen'
                      ·
                        let i : Fin 20 := ⟨n - 4040, by omega⟩
                        have hval : i.val + 4040 = n := by change n - 4040 + 4040 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 4040)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_4040_4059 i hlen'
                    ·
                      by_cases hcut : n < 4080
                      ·
                        let i : Fin 20 := ⟨n - 4060, by omega⟩
                        have hval : i.val + 4060 = n := by change n - 4060 + 4060 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 4060)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_4060_4079 i hlen'
                      ·
                        by_cases hcut : n < 4100
                        ·
                          let i : Fin 20 := ⟨n - 4080, by omega⟩
                          have hval : i.val + 4080 = n := by change n - 4080 + 4080 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 4080)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_4080_4099 i hlen'
                        ·
                          let i : Fin 20 := ⟨n - 4100, by omega⟩
                          have hval : i.val + 4100 = n := by change n - 4100 + 4100 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 4100)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_4100_4119 i hlen'
                  ·
                    by_cases hcut : n < 4180
                    ·
                      by_cases hcut : n < 4140
                      ·
                        let i : Fin 20 := ⟨n - 4120, by omega⟩
                        have hval : i.val + 4120 = n := by change n - 4120 + 4120 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 4120)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_4120_4139 i hlen'
                      ·
                        by_cases hcut : n < 4160
                        ·
                          let i : Fin 20 := ⟨n - 4140, by omega⟩
                          have hval : i.val + 4140 = n := by change n - 4140 + 4140 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 4140)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_4140_4159 i hlen'
                        ·
                          let i : Fin 20 := ⟨n - 4160, by omega⟩
                          have hval : i.val + 4160 = n := by change n - 4160 + 4160 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 4160)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_4160_4179 i hlen'
                    ·
                      by_cases hcut : n < 4200
                      ·
                        let i : Fin 20 := ⟨n - 4180, by omega⟩
                        have hval : i.val + 4180 = n := by change n - 4180 + 4180 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 4180)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_4180_4199 i hlen'
                      ·
                        by_cases hcut : n < 4220
                        ·
                          let i : Fin 20 := ⟨n - 4200, by omega⟩
                          have hval : i.val + 4200 = n := by change n - 4200 + 4200 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 4200)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_4200_4219 i hlen'
                        ·
                          let i : Fin 20 := ⟨n - 4220, by omega⟩
                          have hval : i.val + 4220 = n := by change n - 4220 + 4220 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 4220)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_4220_4239 i hlen'
                ·
                  by_cases hcut : n < 4360
                  ·
                    by_cases hcut : n < 4300
                    ·
                      by_cases hcut : n < 4260
                      ·
                        let i : Fin 20 := ⟨n - 4240, by omega⟩
                        have hval : i.val + 4240 = n := by change n - 4240 + 4240 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 4240)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_4240_4259 i hlen'
                      ·
                        by_cases hcut : n < 4280
                        ·
                          let i : Fin 20 := ⟨n - 4260, by omega⟩
                          have hval : i.val + 4260 = n := by change n - 4260 + 4260 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 4260)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_4260_4279 i hlen'
                        ·
                          let i : Fin 20 := ⟨n - 4280, by omega⟩
                          have hval : i.val + 4280 = n := by change n - 4280 + 4280 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 4280)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_4280_4299 i hlen'
                    ·
                      by_cases hcut : n < 4320
                      ·
                        let i : Fin 20 := ⟨n - 4300, by omega⟩
                        have hval : i.val + 4300 = n := by change n - 4300 + 4300 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 4300)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_4300_4319 i hlen'
                      ·
                        by_cases hcut : n < 4340
                        ·
                          let i : Fin 20 := ⟨n - 4320, by omega⟩
                          have hval : i.val + 4320 = n := by change n - 4320 + 4320 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 4320)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_4320_4339 i hlen'
                        ·
                          let i : Fin 20 := ⟨n - 4340, by omega⟩
                          have hval : i.val + 4340 = n := by change n - 4340 + 4340 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 4340)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_4340_4359 i hlen'
                  ·
                    by_cases hcut : n < 4420
                    ·
                      by_cases hcut : n < 4380
                      ·
                        let i : Fin 20 := ⟨n - 4360, by omega⟩
                        have hval : i.val + 4360 = n := by change n - 4360 + 4360 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 4360)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_4360_4379 i hlen'
                      ·
                        by_cases hcut : n < 4400
                        ·
                          let i : Fin 20 := ⟨n - 4380, by omega⟩
                          have hval : i.val + 4380 = n := by change n - 4380 + 4380 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 4380)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_4380_4399 i hlen'
                        ·
                          let i : Fin 20 := ⟨n - 4400, by omega⟩
                          have hval : i.val + 4400 = n := by change n - 4400 + 4400 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 4400)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_4400_4419 i hlen'
                    ·
                      by_cases hcut : n < 4440
                      ·
                        let i : Fin 20 := ⟨n - 4420, by omega⟩
                        have hval : i.val + 4420 = n := by change n - 4420 + 4420 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 4420)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_4420_4439 i hlen'
                      ·
                        by_cases hcut : n < 4460
                        ·
                          let i : Fin 20 := ⟨n - 4440, by omega⟩
                          have hval : i.val + 4440 = n := by change n - 4440 + 4440 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 4440)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_4440_4459 i hlen'
                        ·
                          let i : Fin 20 := ⟨n - 4460, by omega⟩
                          have hval : i.val + 4460 = n := by change n - 4460 + 4460 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 4460)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_4460_4479 i hlen'
            ·
              by_cases hcut : n < 4920
              ·
                by_cases hcut : n < 4700
                ·
                  by_cases hcut : n < 4580
                  ·
                    by_cases hcut : n < 4520
                    ·
                      by_cases hcut : n < 4500
                      ·
                        let i : Fin 20 := ⟨n - 4480, by omega⟩
                        have hval : i.val + 4480 = n := by change n - 4480 + 4480 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 4480)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_4480_4499 i hlen'
                      ·
                        let i : Fin 20 := ⟨n - 4500, by omega⟩
                        have hval : i.val + 4500 = n := by change n - 4500 + 4500 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 4500)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_4500_4519 i hlen'
                    ·
                      by_cases hcut : n < 4540
                      ·
                        let i : Fin 20 := ⟨n - 4520, by omega⟩
                        have hval : i.val + 4520 = n := by change n - 4520 + 4520 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 4520)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_4520_4539 i hlen'
                      ·
                        by_cases hcut : n < 4560
                        ·
                          let i : Fin 20 := ⟨n - 4540, by omega⟩
                          have hval : i.val + 4540 = n := by change n - 4540 + 4540 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 4540)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_4540_4559 i hlen'
                        ·
                          let i : Fin 20 := ⟨n - 4560, by omega⟩
                          have hval : i.val + 4560 = n := by change n - 4560 + 4560 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 4560)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_4560_4579 i hlen'
                  ·
                    by_cases hcut : n < 4640
                    ·
                      by_cases hcut : n < 4600
                      ·
                        let i : Fin 20 := ⟨n - 4580, by omega⟩
                        have hval : i.val + 4580 = n := by change n - 4580 + 4580 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 4580)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_4580_4599 i hlen'
                      ·
                        by_cases hcut : n < 4620
                        ·
                          let i : Fin 20 := ⟨n - 4600, by omega⟩
                          have hval : i.val + 4600 = n := by change n - 4600 + 4600 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 4600)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_4600_4619 i hlen'
                        ·
                          let i : Fin 20 := ⟨n - 4620, by omega⟩
                          have hval : i.val + 4620 = n := by change n - 4620 + 4620 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 4620)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_4620_4639 i hlen'
                    ·
                      by_cases hcut : n < 4660
                      ·
                        let i : Fin 20 := ⟨n - 4640, by omega⟩
                        have hval : i.val + 4640 = n := by change n - 4640 + 4640 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 4640)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_4640_4659 i hlen'
                      ·
                        by_cases hcut : n < 4680
                        ·
                          let i : Fin 20 := ⟨n - 4660, by omega⟩
                          have hval : i.val + 4660 = n := by change n - 4660 + 4660 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 4660)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_4660_4679 i hlen'
                        ·
                          let i : Fin 20 := ⟨n - 4680, by omega⟩
                          have hval : i.val + 4680 = n := by change n - 4680 + 4680 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 4680)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_4680_4699 i hlen'
                ·
                  by_cases hcut : n < 4800
                  ·
                    by_cases hcut : n < 4740
                    ·
                      by_cases hcut : n < 4720
                      ·
                        let i : Fin 20 := ⟨n - 4700, by omega⟩
                        have hval : i.val + 4700 = n := by change n - 4700 + 4700 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 4700)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_4700_4719 i hlen'
                      ·
                        let i : Fin 20 := ⟨n - 4720, by omega⟩
                        have hval : i.val + 4720 = n := by change n - 4720 + 4720 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 4720)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_4720_4739 i hlen'
                    ·
                      by_cases hcut : n < 4760
                      ·
                        let i : Fin 20 := ⟨n - 4740, by omega⟩
                        have hval : i.val + 4740 = n := by change n - 4740 + 4740 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 4740)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_4740_4759 i hlen'
                      ·
                        by_cases hcut : n < 4780
                        ·
                          let i : Fin 20 := ⟨n - 4760, by omega⟩
                          have hval : i.val + 4760 = n := by change n - 4760 + 4760 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 4760)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_4760_4779 i hlen'
                        ·
                          let i : Fin 20 := ⟨n - 4780, by omega⟩
                          have hval : i.val + 4780 = n := by change n - 4780 + 4780 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 4780)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_4780_4799 i hlen'
                  ·
                    by_cases hcut : n < 4860
                    ·
                      by_cases hcut : n < 4820
                      ·
                        let i : Fin 20 := ⟨n - 4800, by omega⟩
                        have hval : i.val + 4800 = n := by change n - 4800 + 4800 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 4800)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_4800_4819 i hlen'
                      ·
                        by_cases hcut : n < 4840
                        ·
                          let i : Fin 20 := ⟨n - 4820, by omega⟩
                          have hval : i.val + 4820 = n := by change n - 4820 + 4820 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 4820)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_4820_4839 i hlen'
                        ·
                          let i : Fin 20 := ⟨n - 4840, by omega⟩
                          have hval : i.val + 4840 = n := by change n - 4840 + 4840 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 4840)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_4840_4859 i hlen'
                    ·
                      by_cases hcut : n < 4880
                      ·
                        let i : Fin 20 := ⟨n - 4860, by omega⟩
                        have hval : i.val + 4860 = n := by change n - 4860 + 4860 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 4860)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_4860_4879 i hlen'
                      ·
                        by_cases hcut : n < 4900
                        ·
                          let i : Fin 20 := ⟨n - 4880, by omega⟩
                          have hval : i.val + 4880 = n := by change n - 4880 + 4880 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 4880)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_4880_4899 i hlen'
                        ·
                          let i : Fin 20 := ⟨n - 4900, by omega⟩
                          have hval : i.val + 4900 = n := by change n - 4900 + 4900 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 4900)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_4900_4919 i hlen'
              ·
                by_cases hcut : n < 5140
                ·
                  by_cases hcut : n < 5020
                  ·
                    by_cases hcut : n < 4960
                    ·
                      by_cases hcut : n < 4940
                      ·
                        let i : Fin 20 := ⟨n - 4920, by omega⟩
                        have hval : i.val + 4920 = n := by change n - 4920 + 4920 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 4920)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_4920_4939 i hlen'
                      ·
                        let i : Fin 20 := ⟨n - 4940, by omega⟩
                        have hval : i.val + 4940 = n := by change n - 4940 + 4940 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 4940)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_4940_4959 i hlen'
                    ·
                      by_cases hcut : n < 4980
                      ·
                        let i : Fin 20 := ⟨n - 4960, by omega⟩
                        have hval : i.val + 4960 = n := by change n - 4960 + 4960 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 4960)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_4960_4979 i hlen'
                      ·
                        by_cases hcut : n < 5000
                        ·
                          let i : Fin 20 := ⟨n - 4980, by omega⟩
                          have hval : i.val + 4980 = n := by change n - 4980 + 4980 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 4980)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_4980_4999 i hlen'
                        ·
                          let i : Fin 20 := ⟨n - 5000, by omega⟩
                          have hval : i.val + 5000 = n := by change n - 5000 + 5000 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 5000)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_5000_5019 i hlen'
                  ·
                    by_cases hcut : n < 5080
                    ·
                      by_cases hcut : n < 5040
                      ·
                        let i : Fin 20 := ⟨n - 5020, by omega⟩
                        have hval : i.val + 5020 = n := by change n - 5020 + 5020 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 5020)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_5020_5039 i hlen'
                      ·
                        by_cases hcut : n < 5060
                        ·
                          let i : Fin 20 := ⟨n - 5040, by omega⟩
                          have hval : i.val + 5040 = n := by change n - 5040 + 5040 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 5040)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_5040_5059 i hlen'
                        ·
                          let i : Fin 20 := ⟨n - 5060, by omega⟩
                          have hval : i.val + 5060 = n := by change n - 5060 + 5060 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 5060)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_5060_5079 i hlen'
                    ·
                      by_cases hcut : n < 5100
                      ·
                        let i : Fin 20 := ⟨n - 5080, by omega⟩
                        have hval : i.val + 5080 = n := by change n - 5080 + 5080 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 5080)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_5080_5099 i hlen'
                      ·
                        by_cases hcut : n < 5120
                        ·
                          let i : Fin 20 := ⟨n - 5100, by omega⟩
                          have hval : i.val + 5100 = n := by change n - 5100 + 5100 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 5100)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_5100_5119 i hlen'
                        ·
                          let i : Fin 20 := ⟨n - 5120, by omega⟩
                          have hval : i.val + 5120 = n := by change n - 5120 + 5120 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 5120)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_5120_5139 i hlen'
                ·
                  by_cases hcut : n < 5260
                  ·
                    by_cases hcut : n < 5200
                    ·
                      by_cases hcut : n < 5160
                      ·
                        let i : Fin 20 := ⟨n - 5140, by omega⟩
                        have hval : i.val + 5140 = n := by change n - 5140 + 5140 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 5140)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_5140_5159 i hlen'
                      ·
                        by_cases hcut : n < 5180
                        ·
                          let i : Fin 20 := ⟨n - 5160, by omega⟩
                          have hval : i.val + 5160 = n := by change n - 5160 + 5160 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 5160)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_5160_5179 i hlen'
                        ·
                          let i : Fin 20 := ⟨n - 5180, by omega⟩
                          have hval : i.val + 5180 = n := by change n - 5180 + 5180 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 5180)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_5180_5199 i hlen'
                    ·
                      by_cases hcut : n < 5220
                      ·
                        let i : Fin 20 := ⟨n - 5200, by omega⟩
                        have hval : i.val + 5200 = n := by change n - 5200 + 5200 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 5200)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_5200_5219 i hlen'
                      ·
                        by_cases hcut : n < 5240
                        ·
                          let i : Fin 20 := ⟨n - 5220, by omega⟩
                          have hval : i.val + 5220 = n := by change n - 5220 + 5220 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 5220)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_5220_5239 i hlen'
                        ·
                          let i : Fin 20 := ⟨n - 5240, by omega⟩
                          have hval : i.val + 5240 = n := by change n - 5240 + 5240 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 5240)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_5240_5259 i hlen'
                  ·
                    by_cases hcut : n < 5320
                    ·
                      by_cases hcut : n < 5280
                      ·
                        let i : Fin 20 := ⟨n - 5260, by omega⟩
                        have hval : i.val + 5260 = n := by change n - 5260 + 5260 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 5260)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_5260_5279 i hlen'
                      ·
                        by_cases hcut : n < 5300
                        ·
                          let i : Fin 20 := ⟨n - 5280, by omega⟩
                          have hval : i.val + 5280 = n := by change n - 5280 + 5280 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 5280)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_5280_5299 i hlen'
                        ·
                          let i : Fin 20 := ⟨n - 5300, by omega⟩
                          have hval : i.val + 5300 = n := by change n - 5300 + 5300 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 5300)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_5300_5319 i hlen'
                    ·
                      by_cases hcut : n < 5340
                      ·
                        let i : Fin 20 := ⟨n - 5320, by omega⟩
                        have hval : i.val + 5320 = n := by change n - 5320 + 5320 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 5320)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_5320_5339 i hlen'
                      ·
                        by_cases hcut : n < 5360
                        ·
                          let i : Fin 20 := ⟨n - 5340, by omega⟩
                          have hval : i.val + 5340 = n := by change n - 5340 + 5340 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 5340)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_5340_5359 i hlen'
                        ·
                          let i : Fin 20 := ⟨n - 5360, by omega⟩
                          have hval : i.val + 5360 = n := by change n - 5360 + 5360 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 5360)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_5360_5379 i hlen'
          ·
            by_cases hcut : n < 6280
            ·
              by_cases hcut : n < 5820
              ·
                by_cases hcut : n < 5600
                ·
                  by_cases hcut : n < 5480
                  ·
                    by_cases hcut : n < 5420
                    ·
                      by_cases hcut : n < 5400
                      ·
                        let i : Fin 20 := ⟨n - 5380, by omega⟩
                        have hval : i.val + 5380 = n := by change n - 5380 + 5380 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 5380)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_5380_5399 i hlen'
                      ·
                        let i : Fin 20 := ⟨n - 5400, by omega⟩
                        have hval : i.val + 5400 = n := by change n - 5400 + 5400 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 5400)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_5400_5419 i hlen'
                    ·
                      by_cases hcut : n < 5440
                      ·
                        let i : Fin 20 := ⟨n - 5420, by omega⟩
                        have hval : i.val + 5420 = n := by change n - 5420 + 5420 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 5420)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_5420_5439 i hlen'
                      ·
                        by_cases hcut : n < 5460
                        ·
                          let i : Fin 20 := ⟨n - 5440, by omega⟩
                          have hval : i.val + 5440 = n := by change n - 5440 + 5440 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 5440)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_5440_5459 i hlen'
                        ·
                          let i : Fin 20 := ⟨n - 5460, by omega⟩
                          have hval : i.val + 5460 = n := by change n - 5460 + 5460 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 5460)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_5460_5479 i hlen'
                  ·
                    by_cases hcut : n < 5540
                    ·
                      by_cases hcut : n < 5500
                      ·
                        let i : Fin 20 := ⟨n - 5480, by omega⟩
                        have hval : i.val + 5480 = n := by change n - 5480 + 5480 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 5480)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_5480_5499 i hlen'
                      ·
                        by_cases hcut : n < 5520
                        ·
                          let i : Fin 20 := ⟨n - 5500, by omega⟩
                          have hval : i.val + 5500 = n := by change n - 5500 + 5500 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 5500)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_5500_5519 i hlen'
                        ·
                          let i : Fin 20 := ⟨n - 5520, by omega⟩
                          have hval : i.val + 5520 = n := by change n - 5520 + 5520 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 5520)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_5520_5539 i hlen'
                    ·
                      by_cases hcut : n < 5560
                      ·
                        let i : Fin 20 := ⟨n - 5540, by omega⟩
                        have hval : i.val + 5540 = n := by change n - 5540 + 5540 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 5540)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_5540_5559 i hlen'
                      ·
                        by_cases hcut : n < 5580
                        ·
                          let i : Fin 20 := ⟨n - 5560, by omega⟩
                          have hval : i.val + 5560 = n := by change n - 5560 + 5560 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 5560)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_5560_5579 i hlen'
                        ·
                          let i : Fin 20 := ⟨n - 5580, by omega⟩
                          have hval : i.val + 5580 = n := by change n - 5580 + 5580 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 5580)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_5580_5599 i hlen'
                ·
                  by_cases hcut : n < 5700
                  ·
                    by_cases hcut : n < 5640
                    ·
                      by_cases hcut : n < 5620
                      ·
                        let i : Fin 20 := ⟨n - 5600, by omega⟩
                        have hval : i.val + 5600 = n := by change n - 5600 + 5600 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 5600)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_5600_5619 i hlen'
                      ·
                        let i : Fin 20 := ⟨n - 5620, by omega⟩
                        have hval : i.val + 5620 = n := by change n - 5620 + 5620 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 5620)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_5620_5639 i hlen'
                    ·
                      by_cases hcut : n < 5660
                      ·
                        let i : Fin 20 := ⟨n - 5640, by omega⟩
                        have hval : i.val + 5640 = n := by change n - 5640 + 5640 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 5640)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_5640_5659 i hlen'
                      ·
                        by_cases hcut : n < 5680
                        ·
                          let i : Fin 20 := ⟨n - 5660, by omega⟩
                          have hval : i.val + 5660 = n := by change n - 5660 + 5660 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 5660)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_5660_5679 i hlen'
                        ·
                          let i : Fin 20 := ⟨n - 5680, by omega⟩
                          have hval : i.val + 5680 = n := by change n - 5680 + 5680 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 5680)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_5680_5699 i hlen'
                  ·
                    by_cases hcut : n < 5760
                    ·
                      by_cases hcut : n < 5720
                      ·
                        let i : Fin 20 := ⟨n - 5700, by omega⟩
                        have hval : i.val + 5700 = n := by change n - 5700 + 5700 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 5700)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_5700_5719 i hlen'
                      ·
                        by_cases hcut : n < 5740
                        ·
                          let i : Fin 20 := ⟨n - 5720, by omega⟩
                          have hval : i.val + 5720 = n := by change n - 5720 + 5720 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 5720)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_5720_5739 i hlen'
                        ·
                          let i : Fin 20 := ⟨n - 5740, by omega⟩
                          have hval : i.val + 5740 = n := by change n - 5740 + 5740 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 5740)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_5740_5759 i hlen'
                    ·
                      by_cases hcut : n < 5780
                      ·
                        let i : Fin 20 := ⟨n - 5760, by omega⟩
                        have hval : i.val + 5760 = n := by change n - 5760 + 5760 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 5760)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_5760_5779 i hlen'
                      ·
                        by_cases hcut : n < 5800
                        ·
                          let i : Fin 20 := ⟨n - 5780, by omega⟩
                          have hval : i.val + 5780 = n := by change n - 5780 + 5780 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 5780)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_5780_5799 i hlen'
                        ·
                          let i : Fin 20 := ⟨n - 5800, by omega⟩
                          have hval : i.val + 5800 = n := by change n - 5800 + 5800 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 5800)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_5800_5819 i hlen'
              ·
                by_cases hcut : n < 6040
                ·
                  by_cases hcut : n < 5920
                  ·
                    by_cases hcut : n < 5860
                    ·
                      by_cases hcut : n < 5840
                      ·
                        let i : Fin 20 := ⟨n - 5820, by omega⟩
                        have hval : i.val + 5820 = n := by change n - 5820 + 5820 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 5820)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_5820_5839 i hlen'
                      ·
                        let i : Fin 20 := ⟨n - 5840, by omega⟩
                        have hval : i.val + 5840 = n := by change n - 5840 + 5840 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 5840)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_5840_5859 i hlen'
                    ·
                      by_cases hcut : n < 5880
                      ·
                        let i : Fin 20 := ⟨n - 5860, by omega⟩
                        have hval : i.val + 5860 = n := by change n - 5860 + 5860 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 5860)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_5860_5879 i hlen'
                      ·
                        by_cases hcut : n < 5900
                        ·
                          let i : Fin 20 := ⟨n - 5880, by omega⟩
                          have hval : i.val + 5880 = n := by change n - 5880 + 5880 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 5880)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_5880_5899 i hlen'
                        ·
                          let i : Fin 20 := ⟨n - 5900, by omega⟩
                          have hval : i.val + 5900 = n := by change n - 5900 + 5900 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 5900)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_5900_5919 i hlen'
                  ·
                    by_cases hcut : n < 5980
                    ·
                      by_cases hcut : n < 5940
                      ·
                        let i : Fin 20 := ⟨n - 5920, by omega⟩
                        have hval : i.val + 5920 = n := by change n - 5920 + 5920 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 5920)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_5920_5939 i hlen'
                      ·
                        by_cases hcut : n < 5960
                        ·
                          let i : Fin 20 := ⟨n - 5940, by omega⟩
                          have hval : i.val + 5940 = n := by change n - 5940 + 5940 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 5940)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_5940_5959 i hlen'
                        ·
                          let i : Fin 20 := ⟨n - 5960, by omega⟩
                          have hval : i.val + 5960 = n := by change n - 5960 + 5960 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 5960)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_5960_5979 i hlen'
                    ·
                      by_cases hcut : n < 6000
                      ·
                        let i : Fin 20 := ⟨n - 5980, by omega⟩
                        have hval : i.val + 5980 = n := by change n - 5980 + 5980 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 5980)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_5980_5999 i hlen'
                      ·
                        by_cases hcut : n < 6020
                        ·
                          let i : Fin 20 := ⟨n - 6000, by omega⟩
                          have hval : i.val + 6000 = n := by change n - 6000 + 6000 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 6000)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_6000_6019 i hlen'
                        ·
                          let i : Fin 20 := ⟨n - 6020, by omega⟩
                          have hval : i.val + 6020 = n := by change n - 6020 + 6020 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 6020)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_6020_6039 i hlen'
                ·
                  by_cases hcut : n < 6160
                  ·
                    by_cases hcut : n < 6100
                    ·
                      by_cases hcut : n < 6060
                      ·
                        let i : Fin 20 := ⟨n - 6040, by omega⟩
                        have hval : i.val + 6040 = n := by change n - 6040 + 6040 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 6040)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_6040_6059 i hlen'
                      ·
                        by_cases hcut : n < 6080
                        ·
                          let i : Fin 20 := ⟨n - 6060, by omega⟩
                          have hval : i.val + 6060 = n := by change n - 6060 + 6060 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 6060)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_6060_6079 i hlen'
                        ·
                          let i : Fin 20 := ⟨n - 6080, by omega⟩
                          have hval : i.val + 6080 = n := by change n - 6080 + 6080 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 6080)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_6080_6099 i hlen'
                    ·
                      by_cases hcut : n < 6120
                      ·
                        let i : Fin 20 := ⟨n - 6100, by omega⟩
                        have hval : i.val + 6100 = n := by change n - 6100 + 6100 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 6100)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_6100_6119 i hlen'
                      ·
                        by_cases hcut : n < 6140
                        ·
                          let i : Fin 20 := ⟨n - 6120, by omega⟩
                          have hval : i.val + 6120 = n := by change n - 6120 + 6120 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 6120)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_6120_6139 i hlen'
                        ·
                          let i : Fin 20 := ⟨n - 6140, by omega⟩
                          have hval : i.val + 6140 = n := by change n - 6140 + 6140 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 6140)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_6140_6159 i hlen'
                  ·
                    by_cases hcut : n < 6220
                    ·
                      by_cases hcut : n < 6180
                      ·
                        let i : Fin 20 := ⟨n - 6160, by omega⟩
                        have hval : i.val + 6160 = n := by change n - 6160 + 6160 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 6160)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_6160_6179 i hlen'
                      ·
                        by_cases hcut : n < 6200
                        ·
                          let i : Fin 20 := ⟨n - 6180, by omega⟩
                          have hval : i.val + 6180 = n := by change n - 6180 + 6180 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 6180)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_6180_6199 i hlen'
                        ·
                          let i : Fin 20 := ⟨n - 6200, by omega⟩
                          have hval : i.val + 6200 = n := by change n - 6200 + 6200 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 6200)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_6200_6219 i hlen'
                    ·
                      by_cases hcut : n < 6240
                      ·
                        let i : Fin 20 := ⟨n - 6220, by omega⟩
                        have hval : i.val + 6220 = n := by change n - 6220 + 6220 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 6220)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_6220_6239 i hlen'
                      ·
                        by_cases hcut : n < 6260
                        ·
                          let i : Fin 20 := ⟨n - 6240, by omega⟩
                          have hval : i.val + 6240 = n := by change n - 6240 + 6240 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 6240)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_6240_6259 i hlen'
                        ·
                          let i : Fin 20 := ⟨n - 6260, by omega⟩
                          have hval : i.val + 6260 = n := by change n - 6260 + 6260 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 6260)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_6260_6279 i hlen'
            ·
              by_cases hcut : n < 6720
              ·
                by_cases hcut : n < 6500
                ·
                  by_cases hcut : n < 6380
                  ·
                    by_cases hcut : n < 6320
                    ·
                      by_cases hcut : n < 6300
                      ·
                        let i : Fin 20 := ⟨n - 6280, by omega⟩
                        have hval : i.val + 6280 = n := by change n - 6280 + 6280 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 6280)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_6280_6299 i hlen'
                      ·
                        let i : Fin 20 := ⟨n - 6300, by omega⟩
                        have hval : i.val + 6300 = n := by change n - 6300 + 6300 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 6300)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_6300_6319 i hlen'
                    ·
                      by_cases hcut : n < 6340
                      ·
                        let i : Fin 20 := ⟨n - 6320, by omega⟩
                        have hval : i.val + 6320 = n := by change n - 6320 + 6320 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 6320)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_6320_6339 i hlen'
                      ·
                        by_cases hcut : n < 6360
                        ·
                          let i : Fin 20 := ⟨n - 6340, by omega⟩
                          have hval : i.val + 6340 = n := by change n - 6340 + 6340 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 6340)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_6340_6359 i hlen'
                        ·
                          let i : Fin 20 := ⟨n - 6360, by omega⟩
                          have hval : i.val + 6360 = n := by change n - 6360 + 6360 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 6360)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_6360_6379 i hlen'
                  ·
                    by_cases hcut : n < 6440
                    ·
                      by_cases hcut : n < 6400
                      ·
                        let i : Fin 20 := ⟨n - 6380, by omega⟩
                        have hval : i.val + 6380 = n := by change n - 6380 + 6380 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 6380)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_6380_6399 i hlen'
                      ·
                        by_cases hcut : n < 6420
                        ·
                          let i : Fin 20 := ⟨n - 6400, by omega⟩
                          have hval : i.val + 6400 = n := by change n - 6400 + 6400 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 6400)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_6400_6419 i hlen'
                        ·
                          let i : Fin 20 := ⟨n - 6420, by omega⟩
                          have hval : i.val + 6420 = n := by change n - 6420 + 6420 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 6420)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_6420_6439 i hlen'
                    ·
                      by_cases hcut : n < 6460
                      ·
                        let i : Fin 20 := ⟨n - 6440, by omega⟩
                        have hval : i.val + 6440 = n := by change n - 6440 + 6440 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 6440)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_6440_6459 i hlen'
                      ·
                        by_cases hcut : n < 6480
                        ·
                          let i : Fin 20 := ⟨n - 6460, by omega⟩
                          have hval : i.val + 6460 = n := by change n - 6460 + 6460 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 6460)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_6460_6479 i hlen'
                        ·
                          let i : Fin 20 := ⟨n - 6480, by omega⟩
                          have hval : i.val + 6480 = n := by change n - 6480 + 6480 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 6480)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_6480_6499 i hlen'
                ·
                  by_cases hcut : n < 6600
                  ·
                    by_cases hcut : n < 6540
                    ·
                      by_cases hcut : n < 6520
                      ·
                        let i : Fin 20 := ⟨n - 6500, by omega⟩
                        have hval : i.val + 6500 = n := by change n - 6500 + 6500 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 6500)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_6500_6519 i hlen'
                      ·
                        let i : Fin 20 := ⟨n - 6520, by omega⟩
                        have hval : i.val + 6520 = n := by change n - 6520 + 6520 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 6520)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_6520_6539 i hlen'
                    ·
                      by_cases hcut : n < 6560
                      ·
                        let i : Fin 20 := ⟨n - 6540, by omega⟩
                        have hval : i.val + 6540 = n := by change n - 6540 + 6540 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 6540)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_6540_6559 i hlen'
                      ·
                        by_cases hcut : n < 6580
                        ·
                          let i : Fin 20 := ⟨n - 6560, by omega⟩
                          have hval : i.val + 6560 = n := by change n - 6560 + 6560 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 6560)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_6560_6579 i hlen'
                        ·
                          let i : Fin 20 := ⟨n - 6580, by omega⟩
                          have hval : i.val + 6580 = n := by change n - 6580 + 6580 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 6580)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_6580_6599 i hlen'
                  ·
                    by_cases hcut : n < 6660
                    ·
                      by_cases hcut : n < 6620
                      ·
                        let i : Fin 20 := ⟨n - 6600, by omega⟩
                        have hval : i.val + 6600 = n := by change n - 6600 + 6600 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 6600)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_6600_6619 i hlen'
                      ·
                        by_cases hcut : n < 6640
                        ·
                          let i : Fin 20 := ⟨n - 6620, by omega⟩
                          have hval : i.val + 6620 = n := by change n - 6620 + 6620 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 6620)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_6620_6639 i hlen'
                        ·
                          let i : Fin 20 := ⟨n - 6640, by omega⟩
                          have hval : i.val + 6640 = n := by change n - 6640 + 6640 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 6640)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_6640_6659 i hlen'
                    ·
                      by_cases hcut : n < 6680
                      ·
                        let i : Fin 20 := ⟨n - 6660, by omega⟩
                        have hval : i.val + 6660 = n := by change n - 6660 + 6660 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 6660)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_6660_6679 i hlen'
                      ·
                        by_cases hcut : n < 6700
                        ·
                          let i : Fin 20 := ⟨n - 6680, by omega⟩
                          have hval : i.val + 6680 = n := by change n - 6680 + 6680 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 6680)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_6680_6699 i hlen'
                        ·
                          let i : Fin 20 := ⟨n - 6700, by omega⟩
                          have hval : i.val + 6700 = n := by change n - 6700 + 6700 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 6700)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_6700_6719 i hlen'
              ·
                by_cases hcut : n < 6940
                ·
                  by_cases hcut : n < 6820
                  ·
                    by_cases hcut : n < 6760
                    ·
                      by_cases hcut : n < 6740
                      ·
                        let i : Fin 20 := ⟨n - 6720, by omega⟩
                        have hval : i.val + 6720 = n := by change n - 6720 + 6720 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 6720)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_6720_6739 i hlen'
                      ·
                        let i : Fin 20 := ⟨n - 6740, by omega⟩
                        have hval : i.val + 6740 = n := by change n - 6740 + 6740 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 6740)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_6740_6759 i hlen'
                    ·
                      by_cases hcut : n < 6780
                      ·
                        let i : Fin 20 := ⟨n - 6760, by omega⟩
                        have hval : i.val + 6760 = n := by change n - 6760 + 6760 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 6760)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_6760_6779 i hlen'
                      ·
                        by_cases hcut : n < 6800
                        ·
                          let i : Fin 20 := ⟨n - 6780, by omega⟩
                          have hval : i.val + 6780 = n := by change n - 6780 + 6780 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 6780)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_6780_6799 i hlen'
                        ·
                          let i : Fin 20 := ⟨n - 6800, by omega⟩
                          have hval : i.val + 6800 = n := by change n - 6800 + 6800 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 6800)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_6800_6819 i hlen'
                  ·
                    by_cases hcut : n < 6880
                    ·
                      by_cases hcut : n < 6840
                      ·
                        let i : Fin 20 := ⟨n - 6820, by omega⟩
                        have hval : i.val + 6820 = n := by change n - 6820 + 6820 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 6820)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_6820_6839 i hlen'
                      ·
                        by_cases hcut : n < 6860
                        ·
                          let i : Fin 20 := ⟨n - 6840, by omega⟩
                          have hval : i.val + 6840 = n := by change n - 6840 + 6840 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 6840)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_6840_6859 i hlen'
                        ·
                          let i : Fin 20 := ⟨n - 6860, by omega⟩
                          have hval : i.val + 6860 = n := by change n - 6860 + 6860 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 6860)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_6860_6879 i hlen'
                    ·
                      by_cases hcut : n < 6900
                      ·
                        let i : Fin 20 := ⟨n - 6880, by omega⟩
                        have hval : i.val + 6880 = n := by change n - 6880 + 6880 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 6880)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_6880_6899 i hlen'
                      ·
                        by_cases hcut : n < 6920
                        ·
                          let i : Fin 20 := ⟨n - 6900, by omega⟩
                          have hval : i.val + 6900 = n := by change n - 6900 + 6900 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 6900)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_6900_6919 i hlen'
                        ·
                          let i : Fin 20 := ⟨n - 6920, by omega⟩
                          have hval : i.val + 6920 = n := by change n - 6920 + 6920 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 6920)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_6920_6939 i hlen'
                ·
                  by_cases hcut : n < 7060
                  ·
                    by_cases hcut : n < 7000
                    ·
                      by_cases hcut : n < 6960
                      ·
                        let i : Fin 20 := ⟨n - 6940, by omega⟩
                        have hval : i.val + 6940 = n := by change n - 6940 + 6940 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 6940)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_6940_6959 i hlen'
                      ·
                        by_cases hcut : n < 6980
                        ·
                          let i : Fin 20 := ⟨n - 6960, by omega⟩
                          have hval : i.val + 6960 = n := by change n - 6960 + 6960 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 6960)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_6960_6979 i hlen'
                        ·
                          let i : Fin 20 := ⟨n - 6980, by omega⟩
                          have hval : i.val + 6980 = n := by change n - 6980 + 6980 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 6980)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_6980_6999 i hlen'
                    ·
                      by_cases hcut : n < 7020
                      ·
                        let i : Fin 20 := ⟨n - 7000, by omega⟩
                        have hval : i.val + 7000 = n := by change n - 7000 + 7000 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 7000)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_7000_7019 i hlen'
                      ·
                        by_cases hcut : n < 7040
                        ·
                          let i : Fin 20 := ⟨n - 7020, by omega⟩
                          have hval : i.val + 7020 = n := by change n - 7020 + 7020 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 7020)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_7020_7039 i hlen'
                        ·
                          let i : Fin 20 := ⟨n - 7040, by omega⟩
                          have hval : i.val + 7040 = n := by change n - 7040 + 7040 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 7040)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_7040_7059 i hlen'
                  ·
                    by_cases hcut : n < 7120
                    ·
                      by_cases hcut : n < 7080
                      ·
                        let i : Fin 20 := ⟨n - 7060, by omega⟩
                        have hval : i.val + 7060 = n := by change n - 7060 + 7060 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 7060)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_7060_7079 i hlen'
                      ·
                        by_cases hcut : n < 7100
                        ·
                          let i : Fin 20 := ⟨n - 7080, by omega⟩
                          have hval : i.val + 7080 = n := by change n - 7080 + 7080 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 7080)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_7080_7099 i hlen'
                        ·
                          let i : Fin 20 := ⟨n - 7100, by omega⟩
                          have hval : i.val + 7100 = n := by change n - 7100 + 7100 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 7100)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_7100_7119 i hlen'
                    ·
                      by_cases hcut : n < 7140
                      ·
                        let i : Fin 20 := ⟨n - 7120, by omega⟩
                        have hval : i.val + 7120 = n := by change n - 7120 + 7120 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 7120)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_7120_7139 i hlen'
                      ·
                        by_cases hcut : n < 7160
                        ·
                          let i : Fin 20 := ⟨n - 7140, by omega⟩
                          have hval : i.val + 7140 = n := by change n - 7140 + 7140 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 7140)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_7140_7159 i hlen'
                        ·
                          let i : Fin 20 := ⟨n - 7160, by omega⟩
                          have hval : i.val + 7160 = n := by change n - 7160 + 7160 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 7160)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_7160_7179 i hlen'
      ·
        by_cases hcut : n < 10780
        ·
          by_cases hcut : n < 8980
          ·
            by_cases hcut : n < 8080
            ·
              by_cases hcut : n < 7620
              ·
                by_cases hcut : n < 7400
                ·
                  by_cases hcut : n < 7280
                  ·
                    by_cases hcut : n < 7220
                    ·
                      by_cases hcut : n < 7200
                      ·
                        let i : Fin 20 := ⟨n - 7180, by omega⟩
                        have hval : i.val + 7180 = n := by change n - 7180 + 7180 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 7180)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_7180_7199 i hlen'
                      ·
                        let i : Fin 20 := ⟨n - 7200, by omega⟩
                        have hval : i.val + 7200 = n := by change n - 7200 + 7200 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 7200)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_7200_7219 i hlen'
                    ·
                      by_cases hcut : n < 7240
                      ·
                        let i : Fin 20 := ⟨n - 7220, by omega⟩
                        have hval : i.val + 7220 = n := by change n - 7220 + 7220 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 7220)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_7220_7239 i hlen'
                      ·
                        by_cases hcut : n < 7260
                        ·
                          let i : Fin 20 := ⟨n - 7240, by omega⟩
                          have hval : i.val + 7240 = n := by change n - 7240 + 7240 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 7240)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_7240_7259 i hlen'
                        ·
                          let i : Fin 20 := ⟨n - 7260, by omega⟩
                          have hval : i.val + 7260 = n := by change n - 7260 + 7260 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 7260)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_7260_7279 i hlen'
                  ·
                    by_cases hcut : n < 7340
                    ·
                      by_cases hcut : n < 7300
                      ·
                        let i : Fin 20 := ⟨n - 7280, by omega⟩
                        have hval : i.val + 7280 = n := by change n - 7280 + 7280 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 7280)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_7280_7299 i hlen'
                      ·
                        by_cases hcut : n < 7320
                        ·
                          let i : Fin 20 := ⟨n - 7300, by omega⟩
                          have hval : i.val + 7300 = n := by change n - 7300 + 7300 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 7300)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_7300_7319 i hlen'
                        ·
                          let i : Fin 20 := ⟨n - 7320, by omega⟩
                          have hval : i.val + 7320 = n := by change n - 7320 + 7320 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 7320)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_7320_7339 i hlen'
                    ·
                      by_cases hcut : n < 7360
                      ·
                        let i : Fin 20 := ⟨n - 7340, by omega⟩
                        have hval : i.val + 7340 = n := by change n - 7340 + 7340 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 7340)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_7340_7359 i hlen'
                      ·
                        by_cases hcut : n < 7380
                        ·
                          let i : Fin 20 := ⟨n - 7360, by omega⟩
                          have hval : i.val + 7360 = n := by change n - 7360 + 7360 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 7360)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_7360_7379 i hlen'
                        ·
                          let i : Fin 20 := ⟨n - 7380, by omega⟩
                          have hval : i.val + 7380 = n := by change n - 7380 + 7380 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 7380)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_7380_7399 i hlen'
                ·
                  by_cases hcut : n < 7500
                  ·
                    by_cases hcut : n < 7440
                    ·
                      by_cases hcut : n < 7420
                      ·
                        let i : Fin 20 := ⟨n - 7400, by omega⟩
                        have hval : i.val + 7400 = n := by change n - 7400 + 7400 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 7400)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_7400_7419 i hlen'
                      ·
                        let i : Fin 20 := ⟨n - 7420, by omega⟩
                        have hval : i.val + 7420 = n := by change n - 7420 + 7420 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 7420)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_7420_7439 i hlen'
                    ·
                      by_cases hcut : n < 7460
                      ·
                        let i : Fin 20 := ⟨n - 7440, by omega⟩
                        have hval : i.val + 7440 = n := by change n - 7440 + 7440 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 7440)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_7440_7459 i hlen'
                      ·
                        by_cases hcut : n < 7480
                        ·
                          let i : Fin 20 := ⟨n - 7460, by omega⟩
                          have hval : i.val + 7460 = n := by change n - 7460 + 7460 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 7460)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_7460_7479 i hlen'
                        ·
                          let i : Fin 20 := ⟨n - 7480, by omega⟩
                          have hval : i.val + 7480 = n := by change n - 7480 + 7480 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 7480)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_7480_7499 i hlen'
                  ·
                    by_cases hcut : n < 7560
                    ·
                      by_cases hcut : n < 7520
                      ·
                        let i : Fin 20 := ⟨n - 7500, by omega⟩
                        have hval : i.val + 7500 = n := by change n - 7500 + 7500 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 7500)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_7500_7519 i hlen'
                      ·
                        by_cases hcut : n < 7540
                        ·
                          let i : Fin 20 := ⟨n - 7520, by omega⟩
                          have hval : i.val + 7520 = n := by change n - 7520 + 7520 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 7520)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_7520_7539 i hlen'
                        ·
                          let i : Fin 20 := ⟨n - 7540, by omega⟩
                          have hval : i.val + 7540 = n := by change n - 7540 + 7540 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 7540)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_7540_7559 i hlen'
                    ·
                      by_cases hcut : n < 7580
                      ·
                        let i : Fin 20 := ⟨n - 7560, by omega⟩
                        have hval : i.val + 7560 = n := by change n - 7560 + 7560 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 7560)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_7560_7579 i hlen'
                      ·
                        by_cases hcut : n < 7600
                        ·
                          let i : Fin 20 := ⟨n - 7580, by omega⟩
                          have hval : i.val + 7580 = n := by change n - 7580 + 7580 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 7580)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_7580_7599 i hlen'
                        ·
                          let i : Fin 20 := ⟨n - 7600, by omega⟩
                          have hval : i.val + 7600 = n := by change n - 7600 + 7600 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 7600)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_7600_7619 i hlen'
              ·
                by_cases hcut : n < 7840
                ·
                  by_cases hcut : n < 7720
                  ·
                    by_cases hcut : n < 7660
                    ·
                      by_cases hcut : n < 7640
                      ·
                        let i : Fin 20 := ⟨n - 7620, by omega⟩
                        have hval : i.val + 7620 = n := by change n - 7620 + 7620 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 7620)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_7620_7639 i hlen'
                      ·
                        let i : Fin 20 := ⟨n - 7640, by omega⟩
                        have hval : i.val + 7640 = n := by change n - 7640 + 7640 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 7640)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_7640_7659 i hlen'
                    ·
                      by_cases hcut : n < 7680
                      ·
                        let i : Fin 20 := ⟨n - 7660, by omega⟩
                        have hval : i.val + 7660 = n := by change n - 7660 + 7660 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 7660)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_7660_7679 i hlen'
                      ·
                        by_cases hcut : n < 7700
                        ·
                          let i : Fin 20 := ⟨n - 7680, by omega⟩
                          have hval : i.val + 7680 = n := by change n - 7680 + 7680 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 7680)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_7680_7699 i hlen'
                        ·
                          let i : Fin 20 := ⟨n - 7700, by omega⟩
                          have hval : i.val + 7700 = n := by change n - 7700 + 7700 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 7700)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_7700_7719 i hlen'
                  ·
                    by_cases hcut : n < 7780
                    ·
                      by_cases hcut : n < 7740
                      ·
                        let i : Fin 20 := ⟨n - 7720, by omega⟩
                        have hval : i.val + 7720 = n := by change n - 7720 + 7720 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 7720)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_7720_7739 i hlen'
                      ·
                        by_cases hcut : n < 7760
                        ·
                          let i : Fin 20 := ⟨n - 7740, by omega⟩
                          have hval : i.val + 7740 = n := by change n - 7740 + 7740 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 7740)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_7740_7759 i hlen'
                        ·
                          let i : Fin 20 := ⟨n - 7760, by omega⟩
                          have hval : i.val + 7760 = n := by change n - 7760 + 7760 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 7760)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_7760_7779 i hlen'
                    ·
                      by_cases hcut : n < 7800
                      ·
                        let i : Fin 20 := ⟨n - 7780, by omega⟩
                        have hval : i.val + 7780 = n := by change n - 7780 + 7780 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 7780)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_7780_7799 i hlen'
                      ·
                        by_cases hcut : n < 7820
                        ·
                          let i : Fin 20 := ⟨n - 7800, by omega⟩
                          have hval : i.val + 7800 = n := by change n - 7800 + 7800 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 7800)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_7800_7819 i hlen'
                        ·
                          let i : Fin 20 := ⟨n - 7820, by omega⟩
                          have hval : i.val + 7820 = n := by change n - 7820 + 7820 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 7820)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_7820_7839 i hlen'
                ·
                  by_cases hcut : n < 7960
                  ·
                    by_cases hcut : n < 7900
                    ·
                      by_cases hcut : n < 7860
                      ·
                        let i : Fin 20 := ⟨n - 7840, by omega⟩
                        have hval : i.val + 7840 = n := by change n - 7840 + 7840 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 7840)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_7840_7859 i hlen'
                      ·
                        by_cases hcut : n < 7880
                        ·
                          let i : Fin 20 := ⟨n - 7860, by omega⟩
                          have hval : i.val + 7860 = n := by change n - 7860 + 7860 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 7860)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_7860_7879 i hlen'
                        ·
                          let i : Fin 20 := ⟨n - 7880, by omega⟩
                          have hval : i.val + 7880 = n := by change n - 7880 + 7880 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 7880)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_7880_7899 i hlen'
                    ·
                      by_cases hcut : n < 7920
                      ·
                        let i : Fin 20 := ⟨n - 7900, by omega⟩
                        have hval : i.val + 7900 = n := by change n - 7900 + 7900 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 7900)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_7900_7919 i hlen'
                      ·
                        by_cases hcut : n < 7940
                        ·
                          let i : Fin 20 := ⟨n - 7920, by omega⟩
                          have hval : i.val + 7920 = n := by change n - 7920 + 7920 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 7920)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_7920_7939 i hlen'
                        ·
                          let i : Fin 20 := ⟨n - 7940, by omega⟩
                          have hval : i.val + 7940 = n := by change n - 7940 + 7940 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 7940)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_7940_7959 i hlen'
                  ·
                    by_cases hcut : n < 8020
                    ·
                      by_cases hcut : n < 7980
                      ·
                        let i : Fin 20 := ⟨n - 7960, by omega⟩
                        have hval : i.val + 7960 = n := by change n - 7960 + 7960 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 7960)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_7960_7979 i hlen'
                      ·
                        by_cases hcut : n < 8000
                        ·
                          let i : Fin 20 := ⟨n - 7980, by omega⟩
                          have hval : i.val + 7980 = n := by change n - 7980 + 7980 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 7980)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_7980_7999 i hlen'
                        ·
                          let i : Fin 20 := ⟨n - 8000, by omega⟩
                          have hval : i.val + 8000 = n := by change n - 8000 + 8000 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 8000)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_8000_8019 i hlen'
                    ·
                      by_cases hcut : n < 8040
                      ·
                        let i : Fin 20 := ⟨n - 8020, by omega⟩
                        have hval : i.val + 8020 = n := by change n - 8020 + 8020 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 8020)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_8020_8039 i hlen'
                      ·
                        by_cases hcut : n < 8060
                        ·
                          let i : Fin 20 := ⟨n - 8040, by omega⟩
                          have hval : i.val + 8040 = n := by change n - 8040 + 8040 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 8040)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_8040_8059 i hlen'
                        ·
                          let i : Fin 20 := ⟨n - 8060, by omega⟩
                          have hval : i.val + 8060 = n := by change n - 8060 + 8060 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 8060)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_8060_8079 i hlen'
            ·
              by_cases hcut : n < 8520
              ·
                by_cases hcut : n < 8300
                ·
                  by_cases hcut : n < 8180
                  ·
                    by_cases hcut : n < 8120
                    ·
                      by_cases hcut : n < 8100
                      ·
                        let i : Fin 20 := ⟨n - 8080, by omega⟩
                        have hval : i.val + 8080 = n := by change n - 8080 + 8080 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 8080)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_8080_8099 i hlen'
                      ·
                        let i : Fin 20 := ⟨n - 8100, by omega⟩
                        have hval : i.val + 8100 = n := by change n - 8100 + 8100 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 8100)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_8100_8119 i hlen'
                    ·
                      by_cases hcut : n < 8140
                      ·
                        let i : Fin 20 := ⟨n - 8120, by omega⟩
                        have hval : i.val + 8120 = n := by change n - 8120 + 8120 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 8120)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_8120_8139 i hlen'
                      ·
                        by_cases hcut : n < 8160
                        ·
                          let i : Fin 20 := ⟨n - 8140, by omega⟩
                          have hval : i.val + 8140 = n := by change n - 8140 + 8140 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 8140)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_8140_8159 i hlen'
                        ·
                          let i : Fin 20 := ⟨n - 8160, by omega⟩
                          have hval : i.val + 8160 = n := by change n - 8160 + 8160 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 8160)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_8160_8179 i hlen'
                  ·
                    by_cases hcut : n < 8240
                    ·
                      by_cases hcut : n < 8200
                      ·
                        let i : Fin 20 := ⟨n - 8180, by omega⟩
                        have hval : i.val + 8180 = n := by change n - 8180 + 8180 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 8180)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_8180_8199 i hlen'
                      ·
                        by_cases hcut : n < 8220
                        ·
                          let i : Fin 20 := ⟨n - 8200, by omega⟩
                          have hval : i.val + 8200 = n := by change n - 8200 + 8200 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 8200)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_8200_8219 i hlen'
                        ·
                          let i : Fin 20 := ⟨n - 8220, by omega⟩
                          have hval : i.val + 8220 = n := by change n - 8220 + 8220 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 8220)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_8220_8239 i hlen'
                    ·
                      by_cases hcut : n < 8260
                      ·
                        let i : Fin 20 := ⟨n - 8240, by omega⟩
                        have hval : i.val + 8240 = n := by change n - 8240 + 8240 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 8240)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_8240_8259 i hlen'
                      ·
                        by_cases hcut : n < 8280
                        ·
                          let i : Fin 20 := ⟨n - 8260, by omega⟩
                          have hval : i.val + 8260 = n := by change n - 8260 + 8260 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 8260)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_8260_8279 i hlen'
                        ·
                          let i : Fin 20 := ⟨n - 8280, by omega⟩
                          have hval : i.val + 8280 = n := by change n - 8280 + 8280 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 8280)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_8280_8299 i hlen'
                ·
                  by_cases hcut : n < 8400
                  ·
                    by_cases hcut : n < 8340
                    ·
                      by_cases hcut : n < 8320
                      ·
                        let i : Fin 20 := ⟨n - 8300, by omega⟩
                        have hval : i.val + 8300 = n := by change n - 8300 + 8300 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 8300)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_8300_8319 i hlen'
                      ·
                        let i : Fin 20 := ⟨n - 8320, by omega⟩
                        have hval : i.val + 8320 = n := by change n - 8320 + 8320 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 8320)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_8320_8339 i hlen'
                    ·
                      by_cases hcut : n < 8360
                      ·
                        let i : Fin 20 := ⟨n - 8340, by omega⟩
                        have hval : i.val + 8340 = n := by change n - 8340 + 8340 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 8340)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_8340_8359 i hlen'
                      ·
                        by_cases hcut : n < 8380
                        ·
                          let i : Fin 20 := ⟨n - 8360, by omega⟩
                          have hval : i.val + 8360 = n := by change n - 8360 + 8360 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 8360)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_8360_8379 i hlen'
                        ·
                          let i : Fin 20 := ⟨n - 8380, by omega⟩
                          have hval : i.val + 8380 = n := by change n - 8380 + 8380 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 8380)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_8380_8399 i hlen'
                  ·
                    by_cases hcut : n < 8460
                    ·
                      by_cases hcut : n < 8420
                      ·
                        let i : Fin 20 := ⟨n - 8400, by omega⟩
                        have hval : i.val + 8400 = n := by change n - 8400 + 8400 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 8400)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_8400_8419 i hlen'
                      ·
                        by_cases hcut : n < 8440
                        ·
                          let i : Fin 20 := ⟨n - 8420, by omega⟩
                          have hval : i.val + 8420 = n := by change n - 8420 + 8420 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 8420)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_8420_8439 i hlen'
                        ·
                          let i : Fin 20 := ⟨n - 8440, by omega⟩
                          have hval : i.val + 8440 = n := by change n - 8440 + 8440 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 8440)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_8440_8459 i hlen'
                    ·
                      by_cases hcut : n < 8480
                      ·
                        let i : Fin 20 := ⟨n - 8460, by omega⟩
                        have hval : i.val + 8460 = n := by change n - 8460 + 8460 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 8460)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_8460_8479 i hlen'
                      ·
                        by_cases hcut : n < 8500
                        ·
                          let i : Fin 20 := ⟨n - 8480, by omega⟩
                          have hval : i.val + 8480 = n := by change n - 8480 + 8480 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 8480)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_8480_8499 i hlen'
                        ·
                          let i : Fin 20 := ⟨n - 8500, by omega⟩
                          have hval : i.val + 8500 = n := by change n - 8500 + 8500 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 8500)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_8500_8519 i hlen'
              ·
                by_cases hcut : n < 8740
                ·
                  by_cases hcut : n < 8620
                  ·
                    by_cases hcut : n < 8560
                    ·
                      by_cases hcut : n < 8540
                      ·
                        let i : Fin 20 := ⟨n - 8520, by omega⟩
                        have hval : i.val + 8520 = n := by change n - 8520 + 8520 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 8520)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_8520_8539 i hlen'
                      ·
                        let i : Fin 20 := ⟨n - 8540, by omega⟩
                        have hval : i.val + 8540 = n := by change n - 8540 + 8540 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 8540)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_8540_8559 i hlen'
                    ·
                      by_cases hcut : n < 8580
                      ·
                        let i : Fin 20 := ⟨n - 8560, by omega⟩
                        have hval : i.val + 8560 = n := by change n - 8560 + 8560 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 8560)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_8560_8579 i hlen'
                      ·
                        by_cases hcut : n < 8600
                        ·
                          let i : Fin 20 := ⟨n - 8580, by omega⟩
                          have hval : i.val + 8580 = n := by change n - 8580 + 8580 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 8580)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_8580_8599 i hlen'
                        ·
                          let i : Fin 20 := ⟨n - 8600, by omega⟩
                          have hval : i.val + 8600 = n := by change n - 8600 + 8600 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 8600)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_8600_8619 i hlen'
                  ·
                    by_cases hcut : n < 8680
                    ·
                      by_cases hcut : n < 8640
                      ·
                        let i : Fin 20 := ⟨n - 8620, by omega⟩
                        have hval : i.val + 8620 = n := by change n - 8620 + 8620 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 8620)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_8620_8639 i hlen'
                      ·
                        by_cases hcut : n < 8660
                        ·
                          let i : Fin 20 := ⟨n - 8640, by omega⟩
                          have hval : i.val + 8640 = n := by change n - 8640 + 8640 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 8640)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_8640_8659 i hlen'
                        ·
                          let i : Fin 20 := ⟨n - 8660, by omega⟩
                          have hval : i.val + 8660 = n := by change n - 8660 + 8660 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 8660)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_8660_8679 i hlen'
                    ·
                      by_cases hcut : n < 8700
                      ·
                        let i : Fin 20 := ⟨n - 8680, by omega⟩
                        have hval : i.val + 8680 = n := by change n - 8680 + 8680 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 8680)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_8680_8699 i hlen'
                      ·
                        by_cases hcut : n < 8720
                        ·
                          let i : Fin 20 := ⟨n - 8700, by omega⟩
                          have hval : i.val + 8700 = n := by change n - 8700 + 8700 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 8700)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_8700_8719 i hlen'
                        ·
                          let i : Fin 20 := ⟨n - 8720, by omega⟩
                          have hval : i.val + 8720 = n := by change n - 8720 + 8720 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 8720)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_8720_8739 i hlen'
                ·
                  by_cases hcut : n < 8860
                  ·
                    by_cases hcut : n < 8800
                    ·
                      by_cases hcut : n < 8760
                      ·
                        let i : Fin 20 := ⟨n - 8740, by omega⟩
                        have hval : i.val + 8740 = n := by change n - 8740 + 8740 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 8740)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_8740_8759 i hlen'
                      ·
                        by_cases hcut : n < 8780
                        ·
                          let i : Fin 20 := ⟨n - 8760, by omega⟩
                          have hval : i.val + 8760 = n := by change n - 8760 + 8760 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 8760)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_8760_8779 i hlen'
                        ·
                          let i : Fin 20 := ⟨n - 8780, by omega⟩
                          have hval : i.val + 8780 = n := by change n - 8780 + 8780 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 8780)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_8780_8799 i hlen'
                    ·
                      by_cases hcut : n < 8820
                      ·
                        let i : Fin 20 := ⟨n - 8800, by omega⟩
                        have hval : i.val + 8800 = n := by change n - 8800 + 8800 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 8800)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_8800_8819 i hlen'
                      ·
                        by_cases hcut : n < 8840
                        ·
                          let i : Fin 20 := ⟨n - 8820, by omega⟩
                          have hval : i.val + 8820 = n := by change n - 8820 + 8820 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 8820)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_8820_8839 i hlen'
                        ·
                          let i : Fin 20 := ⟨n - 8840, by omega⟩
                          have hval : i.val + 8840 = n := by change n - 8840 + 8840 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 8840)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_8840_8859 i hlen'
                  ·
                    by_cases hcut : n < 8920
                    ·
                      by_cases hcut : n < 8880
                      ·
                        let i : Fin 20 := ⟨n - 8860, by omega⟩
                        have hval : i.val + 8860 = n := by change n - 8860 + 8860 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 8860)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_8860_8879 i hlen'
                      ·
                        by_cases hcut : n < 8900
                        ·
                          let i : Fin 20 := ⟨n - 8880, by omega⟩
                          have hval : i.val + 8880 = n := by change n - 8880 + 8880 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 8880)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_8880_8899 i hlen'
                        ·
                          let i : Fin 20 := ⟨n - 8900, by omega⟩
                          have hval : i.val + 8900 = n := by change n - 8900 + 8900 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 8900)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_8900_8919 i hlen'
                    ·
                      by_cases hcut : n < 8940
                      ·
                        let i : Fin 20 := ⟨n - 8920, by omega⟩
                        have hval : i.val + 8920 = n := by change n - 8920 + 8920 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 8920)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_8920_8939 i hlen'
                      ·
                        by_cases hcut : n < 8960
                        ·
                          let i : Fin 20 := ⟨n - 8940, by omega⟩
                          have hval : i.val + 8940 = n := by change n - 8940 + 8940 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 8940)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_8940_8959 i hlen'
                        ·
                          let i : Fin 20 := ⟨n - 8960, by omega⟩
                          have hval : i.val + 8960 = n := by change n - 8960 + 8960 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 8960)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_8960_8979 i hlen'
          ·
            by_cases hcut : n < 9880
            ·
              by_cases hcut : n < 9420
              ·
                by_cases hcut : n < 9200
                ·
                  by_cases hcut : n < 9080
                  ·
                    by_cases hcut : n < 9020
                    ·
                      by_cases hcut : n < 9000
                      ·
                        let i : Fin 20 := ⟨n - 8980, by omega⟩
                        have hval : i.val + 8980 = n := by change n - 8980 + 8980 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 8980)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_8980_8999 i hlen'
                      ·
                        let i : Fin 20 := ⟨n - 9000, by omega⟩
                        have hval : i.val + 9000 = n := by change n - 9000 + 9000 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 9000)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_9000_9019 i hlen'
                    ·
                      by_cases hcut : n < 9040
                      ·
                        let i : Fin 20 := ⟨n - 9020, by omega⟩
                        have hval : i.val + 9020 = n := by change n - 9020 + 9020 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 9020)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_9020_9039 i hlen'
                      ·
                        by_cases hcut : n < 9060
                        ·
                          let i : Fin 20 := ⟨n - 9040, by omega⟩
                          have hval : i.val + 9040 = n := by change n - 9040 + 9040 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 9040)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_9040_9059 i hlen'
                        ·
                          let i : Fin 20 := ⟨n - 9060, by omega⟩
                          have hval : i.val + 9060 = n := by change n - 9060 + 9060 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 9060)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_9060_9079 i hlen'
                  ·
                    by_cases hcut : n < 9140
                    ·
                      by_cases hcut : n < 9100
                      ·
                        let i : Fin 20 := ⟨n - 9080, by omega⟩
                        have hval : i.val + 9080 = n := by change n - 9080 + 9080 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 9080)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_9080_9099 i hlen'
                      ·
                        by_cases hcut : n < 9120
                        ·
                          let i : Fin 20 := ⟨n - 9100, by omega⟩
                          have hval : i.val + 9100 = n := by change n - 9100 + 9100 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 9100)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_9100_9119 i hlen'
                        ·
                          let i : Fin 20 := ⟨n - 9120, by omega⟩
                          have hval : i.val + 9120 = n := by change n - 9120 + 9120 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 9120)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_9120_9139 i hlen'
                    ·
                      by_cases hcut : n < 9160
                      ·
                        let i : Fin 20 := ⟨n - 9140, by omega⟩
                        have hval : i.val + 9140 = n := by change n - 9140 + 9140 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 9140)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_9140_9159 i hlen'
                      ·
                        by_cases hcut : n < 9180
                        ·
                          let i : Fin 20 := ⟨n - 9160, by omega⟩
                          have hval : i.val + 9160 = n := by change n - 9160 + 9160 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 9160)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_9160_9179 i hlen'
                        ·
                          let i : Fin 20 := ⟨n - 9180, by omega⟩
                          have hval : i.val + 9180 = n := by change n - 9180 + 9180 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 9180)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_9180_9199 i hlen'
                ·
                  by_cases hcut : n < 9300
                  ·
                    by_cases hcut : n < 9240
                    ·
                      by_cases hcut : n < 9220
                      ·
                        let i : Fin 20 := ⟨n - 9200, by omega⟩
                        have hval : i.val + 9200 = n := by change n - 9200 + 9200 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 9200)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_9200_9219 i hlen'
                      ·
                        let i : Fin 20 := ⟨n - 9220, by omega⟩
                        have hval : i.val + 9220 = n := by change n - 9220 + 9220 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 9220)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_9220_9239 i hlen'
                    ·
                      by_cases hcut : n < 9260
                      ·
                        let i : Fin 20 := ⟨n - 9240, by omega⟩
                        have hval : i.val + 9240 = n := by change n - 9240 + 9240 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 9240)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_9240_9259 i hlen'
                      ·
                        by_cases hcut : n < 9280
                        ·
                          let i : Fin 20 := ⟨n - 9260, by omega⟩
                          have hval : i.val + 9260 = n := by change n - 9260 + 9260 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 9260)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_9260_9279 i hlen'
                        ·
                          let i : Fin 20 := ⟨n - 9280, by omega⟩
                          have hval : i.val + 9280 = n := by change n - 9280 + 9280 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 9280)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_9280_9299 i hlen'
                  ·
                    by_cases hcut : n < 9360
                    ·
                      by_cases hcut : n < 9320
                      ·
                        let i : Fin 20 := ⟨n - 9300, by omega⟩
                        have hval : i.val + 9300 = n := by change n - 9300 + 9300 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 9300)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_9300_9319 i hlen'
                      ·
                        by_cases hcut : n < 9340
                        ·
                          let i : Fin 20 := ⟨n - 9320, by omega⟩
                          have hval : i.val + 9320 = n := by change n - 9320 + 9320 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 9320)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_9320_9339 i hlen'
                        ·
                          let i : Fin 20 := ⟨n - 9340, by omega⟩
                          have hval : i.val + 9340 = n := by change n - 9340 + 9340 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 9340)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_9340_9359 i hlen'
                    ·
                      by_cases hcut : n < 9380
                      ·
                        let i : Fin 20 := ⟨n - 9360, by omega⟩
                        have hval : i.val + 9360 = n := by change n - 9360 + 9360 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 9360)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_9360_9379 i hlen'
                      ·
                        by_cases hcut : n < 9400
                        ·
                          let i : Fin 20 := ⟨n - 9380, by omega⟩
                          have hval : i.val + 9380 = n := by change n - 9380 + 9380 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 9380)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_9380_9399 i hlen'
                        ·
                          let i : Fin 20 := ⟨n - 9400, by omega⟩
                          have hval : i.val + 9400 = n := by change n - 9400 + 9400 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 9400)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_9400_9419 i hlen'
              ·
                by_cases hcut : n < 9640
                ·
                  by_cases hcut : n < 9520
                  ·
                    by_cases hcut : n < 9460
                    ·
                      by_cases hcut : n < 9440
                      ·
                        let i : Fin 20 := ⟨n - 9420, by omega⟩
                        have hval : i.val + 9420 = n := by change n - 9420 + 9420 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 9420)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_9420_9439 i hlen'
                      ·
                        let i : Fin 20 := ⟨n - 9440, by omega⟩
                        have hval : i.val + 9440 = n := by change n - 9440 + 9440 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 9440)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_9440_9459 i hlen'
                    ·
                      by_cases hcut : n < 9480
                      ·
                        let i : Fin 20 := ⟨n - 9460, by omega⟩
                        have hval : i.val + 9460 = n := by change n - 9460 + 9460 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 9460)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_9460_9479 i hlen'
                      ·
                        by_cases hcut : n < 9500
                        ·
                          let i : Fin 20 := ⟨n - 9480, by omega⟩
                          have hval : i.val + 9480 = n := by change n - 9480 + 9480 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 9480)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_9480_9499 i hlen'
                        ·
                          let i : Fin 20 := ⟨n - 9500, by omega⟩
                          have hval : i.val + 9500 = n := by change n - 9500 + 9500 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 9500)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_9500_9519 i hlen'
                  ·
                    by_cases hcut : n < 9580
                    ·
                      by_cases hcut : n < 9540
                      ·
                        let i : Fin 20 := ⟨n - 9520, by omega⟩
                        have hval : i.val + 9520 = n := by change n - 9520 + 9520 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 9520)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_9520_9539 i hlen'
                      ·
                        by_cases hcut : n < 9560
                        ·
                          let i : Fin 20 := ⟨n - 9540, by omega⟩
                          have hval : i.val + 9540 = n := by change n - 9540 + 9540 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 9540)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_9540_9559 i hlen'
                        ·
                          let i : Fin 20 := ⟨n - 9560, by omega⟩
                          have hval : i.val + 9560 = n := by change n - 9560 + 9560 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 9560)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_9560_9579 i hlen'
                    ·
                      by_cases hcut : n < 9600
                      ·
                        let i : Fin 20 := ⟨n - 9580, by omega⟩
                        have hval : i.val + 9580 = n := by change n - 9580 + 9580 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 9580)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_9580_9599 i hlen'
                      ·
                        by_cases hcut : n < 9620
                        ·
                          let i : Fin 20 := ⟨n - 9600, by omega⟩
                          have hval : i.val + 9600 = n := by change n - 9600 + 9600 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 9600)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_9600_9619 i hlen'
                        ·
                          let i : Fin 20 := ⟨n - 9620, by omega⟩
                          have hval : i.val + 9620 = n := by change n - 9620 + 9620 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 9620)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_9620_9639 i hlen'
                ·
                  by_cases hcut : n < 9760
                  ·
                    by_cases hcut : n < 9700
                    ·
                      by_cases hcut : n < 9660
                      ·
                        let i : Fin 20 := ⟨n - 9640, by omega⟩
                        have hval : i.val + 9640 = n := by change n - 9640 + 9640 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 9640)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_9640_9659 i hlen'
                      ·
                        by_cases hcut : n < 9680
                        ·
                          let i : Fin 20 := ⟨n - 9660, by omega⟩
                          have hval : i.val + 9660 = n := by change n - 9660 + 9660 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 9660)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_9660_9679 i hlen'
                        ·
                          let i : Fin 20 := ⟨n - 9680, by omega⟩
                          have hval : i.val + 9680 = n := by change n - 9680 + 9680 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 9680)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_9680_9699 i hlen'
                    ·
                      by_cases hcut : n < 9720
                      ·
                        let i : Fin 20 := ⟨n - 9700, by omega⟩
                        have hval : i.val + 9700 = n := by change n - 9700 + 9700 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 9700)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_9700_9719 i hlen'
                      ·
                        by_cases hcut : n < 9740
                        ·
                          let i : Fin 20 := ⟨n - 9720, by omega⟩
                          have hval : i.val + 9720 = n := by change n - 9720 + 9720 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 9720)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_9720_9739 i hlen'
                        ·
                          let i : Fin 20 := ⟨n - 9740, by omega⟩
                          have hval : i.val + 9740 = n := by change n - 9740 + 9740 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 9740)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_9740_9759 i hlen'
                  ·
                    by_cases hcut : n < 9820
                    ·
                      by_cases hcut : n < 9780
                      ·
                        let i : Fin 20 := ⟨n - 9760, by omega⟩
                        have hval : i.val + 9760 = n := by change n - 9760 + 9760 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 9760)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_9760_9779 i hlen'
                      ·
                        by_cases hcut : n < 9800
                        ·
                          let i : Fin 20 := ⟨n - 9780, by omega⟩
                          have hval : i.val + 9780 = n := by change n - 9780 + 9780 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 9780)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_9780_9799 i hlen'
                        ·
                          let i : Fin 20 := ⟨n - 9800, by omega⟩
                          have hval : i.val + 9800 = n := by change n - 9800 + 9800 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 9800)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_9800_9819 i hlen'
                    ·
                      by_cases hcut : n < 9840
                      ·
                        let i : Fin 20 := ⟨n - 9820, by omega⟩
                        have hval : i.val + 9820 = n := by change n - 9820 + 9820 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 9820)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_9820_9839 i hlen'
                      ·
                        by_cases hcut : n < 9860
                        ·
                          let i : Fin 20 := ⟨n - 9840, by omega⟩
                          have hval : i.val + 9840 = n := by change n - 9840 + 9840 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 9840)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_9840_9859 i hlen'
                        ·
                          let i : Fin 20 := ⟨n - 9860, by omega⟩
                          have hval : i.val + 9860 = n := by change n - 9860 + 9860 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 9860)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_9860_9879 i hlen'
            ·
              by_cases hcut : n < 10320
              ·
                by_cases hcut : n < 10100
                ·
                  by_cases hcut : n < 9980
                  ·
                    by_cases hcut : n < 9920
                    ·
                      by_cases hcut : n < 9900
                      ·
                        let i : Fin 20 := ⟨n - 9880, by omega⟩
                        have hval : i.val + 9880 = n := by change n - 9880 + 9880 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 9880)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_9880_9899 i hlen'
                      ·
                        let i : Fin 20 := ⟨n - 9900, by omega⟩
                        have hval : i.val + 9900 = n := by change n - 9900 + 9900 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 9900)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_9900_9919 i hlen'
                    ·
                      by_cases hcut : n < 9940
                      ·
                        let i : Fin 20 := ⟨n - 9920, by omega⟩
                        have hval : i.val + 9920 = n := by change n - 9920 + 9920 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 9920)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_9920_9939 i hlen'
                      ·
                        by_cases hcut : n < 9960
                        ·
                          let i : Fin 20 := ⟨n - 9940, by omega⟩
                          have hval : i.val + 9940 = n := by change n - 9940 + 9940 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 9940)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_9940_9959 i hlen'
                        ·
                          let i : Fin 20 := ⟨n - 9960, by omega⟩
                          have hval : i.val + 9960 = n := by change n - 9960 + 9960 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 9960)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_9960_9979 i hlen'
                  ·
                    by_cases hcut : n < 10040
                    ·
                      by_cases hcut : n < 10000
                      ·
                        let i : Fin 20 := ⟨n - 9980, by omega⟩
                        have hval : i.val + 9980 = n := by change n - 9980 + 9980 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 9980)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_9980_9999 i hlen'
                      ·
                        by_cases hcut : n < 10020
                        ·
                          let i : Fin 20 := ⟨n - 10000, by omega⟩
                          have hval : i.val + 10000 = n := by change n - 10000 + 10000 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 10000)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_10000_10019 i hlen'
                        ·
                          let i : Fin 20 := ⟨n - 10020, by omega⟩
                          have hval : i.val + 10020 = n := by change n - 10020 + 10020 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 10020)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_10020_10039 i hlen'
                    ·
                      by_cases hcut : n < 10060
                      ·
                        let i : Fin 20 := ⟨n - 10040, by omega⟩
                        have hval : i.val + 10040 = n := by change n - 10040 + 10040 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 10040)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_10040_10059 i hlen'
                      ·
                        by_cases hcut : n < 10080
                        ·
                          let i : Fin 20 := ⟨n - 10060, by omega⟩
                          have hval : i.val + 10060 = n := by change n - 10060 + 10060 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 10060)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_10060_10079 i hlen'
                        ·
                          let i : Fin 20 := ⟨n - 10080, by omega⟩
                          have hval : i.val + 10080 = n := by change n - 10080 + 10080 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 10080)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_10080_10099 i hlen'
                ·
                  by_cases hcut : n < 10200
                  ·
                    by_cases hcut : n < 10140
                    ·
                      by_cases hcut : n < 10120
                      ·
                        let i : Fin 20 := ⟨n - 10100, by omega⟩
                        have hval : i.val + 10100 = n := by change n - 10100 + 10100 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 10100)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_10100_10119 i hlen'
                      ·
                        let i : Fin 20 := ⟨n - 10120, by omega⟩
                        have hval : i.val + 10120 = n := by change n - 10120 + 10120 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 10120)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_10120_10139 i hlen'
                    ·
                      by_cases hcut : n < 10160
                      ·
                        let i : Fin 20 := ⟨n - 10140, by omega⟩
                        have hval : i.val + 10140 = n := by change n - 10140 + 10140 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 10140)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_10140_10159 i hlen'
                      ·
                        by_cases hcut : n < 10180
                        ·
                          let i : Fin 20 := ⟨n - 10160, by omega⟩
                          have hval : i.val + 10160 = n := by change n - 10160 + 10160 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 10160)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_10160_10179 i hlen'
                        ·
                          let i : Fin 20 := ⟨n - 10180, by omega⟩
                          have hval : i.val + 10180 = n := by change n - 10180 + 10180 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 10180)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_10180_10199 i hlen'
                  ·
                    by_cases hcut : n < 10260
                    ·
                      by_cases hcut : n < 10220
                      ·
                        let i : Fin 20 := ⟨n - 10200, by omega⟩
                        have hval : i.val + 10200 = n := by change n - 10200 + 10200 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 10200)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_10200_10219 i hlen'
                      ·
                        by_cases hcut : n < 10240
                        ·
                          let i : Fin 20 := ⟨n - 10220, by omega⟩
                          have hval : i.val + 10220 = n := by change n - 10220 + 10220 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 10220)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_10220_10239 i hlen'
                        ·
                          let i : Fin 20 := ⟨n - 10240, by omega⟩
                          have hval : i.val + 10240 = n := by change n - 10240 + 10240 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 10240)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_10240_10259 i hlen'
                    ·
                      by_cases hcut : n < 10280
                      ·
                        let i : Fin 20 := ⟨n - 10260, by omega⟩
                        have hval : i.val + 10260 = n := by change n - 10260 + 10260 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 10260)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_10260_10279 i hlen'
                      ·
                        by_cases hcut : n < 10300
                        ·
                          let i : Fin 20 := ⟨n - 10280, by omega⟩
                          have hval : i.val + 10280 = n := by change n - 10280 + 10280 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 10280)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_10280_10299 i hlen'
                        ·
                          let i : Fin 20 := ⟨n - 10300, by omega⟩
                          have hval : i.val + 10300 = n := by change n - 10300 + 10300 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 10300)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_10300_10319 i hlen'
              ·
                by_cases hcut : n < 10540
                ·
                  by_cases hcut : n < 10420
                  ·
                    by_cases hcut : n < 10360
                    ·
                      by_cases hcut : n < 10340
                      ·
                        let i : Fin 20 := ⟨n - 10320, by omega⟩
                        have hval : i.val + 10320 = n := by change n - 10320 + 10320 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 10320)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_10320_10339 i hlen'
                      ·
                        let i : Fin 20 := ⟨n - 10340, by omega⟩
                        have hval : i.val + 10340 = n := by change n - 10340 + 10340 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 10340)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_10340_10359 i hlen'
                    ·
                      by_cases hcut : n < 10380
                      ·
                        let i : Fin 20 := ⟨n - 10360, by omega⟩
                        have hval : i.val + 10360 = n := by change n - 10360 + 10360 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 10360)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_10360_10379 i hlen'
                      ·
                        by_cases hcut : n < 10400
                        ·
                          let i : Fin 20 := ⟨n - 10380, by omega⟩
                          have hval : i.val + 10380 = n := by change n - 10380 + 10380 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 10380)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_10380_10399 i hlen'
                        ·
                          let i : Fin 20 := ⟨n - 10400, by omega⟩
                          have hval : i.val + 10400 = n := by change n - 10400 + 10400 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 10400)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_10400_10419 i hlen'
                  ·
                    by_cases hcut : n < 10480
                    ·
                      by_cases hcut : n < 10440
                      ·
                        let i : Fin 20 := ⟨n - 10420, by omega⟩
                        have hval : i.val + 10420 = n := by change n - 10420 + 10420 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 10420)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_10420_10439 i hlen'
                      ·
                        by_cases hcut : n < 10460
                        ·
                          let i : Fin 20 := ⟨n - 10440, by omega⟩
                          have hval : i.val + 10440 = n := by change n - 10440 + 10440 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 10440)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_10440_10459 i hlen'
                        ·
                          let i : Fin 20 := ⟨n - 10460, by omega⟩
                          have hval : i.val + 10460 = n := by change n - 10460 + 10460 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 10460)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_10460_10479 i hlen'
                    ·
                      by_cases hcut : n < 10500
                      ·
                        let i : Fin 20 := ⟨n - 10480, by omega⟩
                        have hval : i.val + 10480 = n := by change n - 10480 + 10480 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 10480)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_10480_10499 i hlen'
                      ·
                        by_cases hcut : n < 10520
                        ·
                          let i : Fin 20 := ⟨n - 10500, by omega⟩
                          have hval : i.val + 10500 = n := by change n - 10500 + 10500 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 10500)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_10500_10519 i hlen'
                        ·
                          let i : Fin 20 := ⟨n - 10520, by omega⟩
                          have hval : i.val + 10520 = n := by change n - 10520 + 10520 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 10520)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_10520_10539 i hlen'
                ·
                  by_cases hcut : n < 10660
                  ·
                    by_cases hcut : n < 10600
                    ·
                      by_cases hcut : n < 10560
                      ·
                        let i : Fin 20 := ⟨n - 10540, by omega⟩
                        have hval : i.val + 10540 = n := by change n - 10540 + 10540 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 10540)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_10540_10559 i hlen'
                      ·
                        by_cases hcut : n < 10580
                        ·
                          let i : Fin 20 := ⟨n - 10560, by omega⟩
                          have hval : i.val + 10560 = n := by change n - 10560 + 10560 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 10560)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_10560_10579 i hlen'
                        ·
                          let i : Fin 20 := ⟨n - 10580, by omega⟩
                          have hval : i.val + 10580 = n := by change n - 10580 + 10580 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 10580)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_10580_10599 i hlen'
                    ·
                      by_cases hcut : n < 10620
                      ·
                        let i : Fin 20 := ⟨n - 10600, by omega⟩
                        have hval : i.val + 10600 = n := by change n - 10600 + 10600 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 10600)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_10600_10619 i hlen'
                      ·
                        by_cases hcut : n < 10640
                        ·
                          let i : Fin 20 := ⟨n - 10620, by omega⟩
                          have hval : i.val + 10620 = n := by change n - 10620 + 10620 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 10620)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_10620_10639 i hlen'
                        ·
                          let i : Fin 20 := ⟨n - 10640, by omega⟩
                          have hval : i.val + 10640 = n := by change n - 10640 + 10640 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 10640)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_10640_10659 i hlen'
                  ·
                    by_cases hcut : n < 10720
                    ·
                      by_cases hcut : n < 10680
                      ·
                        let i : Fin 20 := ⟨n - 10660, by omega⟩
                        have hval : i.val + 10660 = n := by change n - 10660 + 10660 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 10660)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_10660_10679 i hlen'
                      ·
                        by_cases hcut : n < 10700
                        ·
                          let i : Fin 20 := ⟨n - 10680, by omega⟩
                          have hval : i.val + 10680 = n := by change n - 10680 + 10680 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 10680)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_10680_10699 i hlen'
                        ·
                          let i : Fin 20 := ⟨n - 10700, by omega⟩
                          have hval : i.val + 10700 = n := by change n - 10700 + 10700 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 10700)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_10700_10719 i hlen'
                    ·
                      by_cases hcut : n < 10740
                      ·
                        let i : Fin 20 := ⟨n - 10720, by omega⟩
                        have hval : i.val + 10720 = n := by change n - 10720 + 10720 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 10720)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_10720_10739 i hlen'
                      ·
                        by_cases hcut : n < 10760
                        ·
                          let i : Fin 20 := ⟨n - 10740, by omega⟩
                          have hval : i.val + 10740 = n := by change n - 10740 + 10740 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 10740)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_10740_10759 i hlen'
                        ·
                          let i : Fin 20 := ⟨n - 10760, by omega⟩
                          have hval : i.val + 10760 = n := by change n - 10760 + 10760 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 10760)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_10760_10779 i hlen'
        ·
          by_cases hcut : n < 12580
          ·
            by_cases hcut : n < 11680
            ·
              by_cases hcut : n < 11220
              ·
                by_cases hcut : n < 11000
                ·
                  by_cases hcut : n < 10880
                  ·
                    by_cases hcut : n < 10820
                    ·
                      by_cases hcut : n < 10800
                      ·
                        let i : Fin 20 := ⟨n - 10780, by omega⟩
                        have hval : i.val + 10780 = n := by change n - 10780 + 10780 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 10780)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_10780_10799 i hlen'
                      ·
                        let i : Fin 20 := ⟨n - 10800, by omega⟩
                        have hval : i.val + 10800 = n := by change n - 10800 + 10800 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 10800)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_10800_10819 i hlen'
                    ·
                      by_cases hcut : n < 10840
                      ·
                        let i : Fin 20 := ⟨n - 10820, by omega⟩
                        have hval : i.val + 10820 = n := by change n - 10820 + 10820 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 10820)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_10820_10839 i hlen'
                      ·
                        by_cases hcut : n < 10860
                        ·
                          let i : Fin 20 := ⟨n - 10840, by omega⟩
                          have hval : i.val + 10840 = n := by change n - 10840 + 10840 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 10840)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_10840_10859 i hlen'
                        ·
                          let i : Fin 20 := ⟨n - 10860, by omega⟩
                          have hval : i.val + 10860 = n := by change n - 10860 + 10860 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 10860)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_10860_10879 i hlen'
                  ·
                    by_cases hcut : n < 10940
                    ·
                      by_cases hcut : n < 10900
                      ·
                        let i : Fin 20 := ⟨n - 10880, by omega⟩
                        have hval : i.val + 10880 = n := by change n - 10880 + 10880 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 10880)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_10880_10899 i hlen'
                      ·
                        by_cases hcut : n < 10920
                        ·
                          let i : Fin 20 := ⟨n - 10900, by omega⟩
                          have hval : i.val + 10900 = n := by change n - 10900 + 10900 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 10900)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_10900_10919 i hlen'
                        ·
                          let i : Fin 20 := ⟨n - 10920, by omega⟩
                          have hval : i.val + 10920 = n := by change n - 10920 + 10920 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 10920)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_10920_10939 i hlen'
                    ·
                      by_cases hcut : n < 10960
                      ·
                        let i : Fin 20 := ⟨n - 10940, by omega⟩
                        have hval : i.val + 10940 = n := by change n - 10940 + 10940 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 10940)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_10940_10959 i hlen'
                      ·
                        by_cases hcut : n < 10980
                        ·
                          let i : Fin 20 := ⟨n - 10960, by omega⟩
                          have hval : i.val + 10960 = n := by change n - 10960 + 10960 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 10960)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_10960_10979 i hlen'
                        ·
                          let i : Fin 20 := ⟨n - 10980, by omega⟩
                          have hval : i.val + 10980 = n := by change n - 10980 + 10980 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 10980)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_10980_10999 i hlen'
                ·
                  by_cases hcut : n < 11100
                  ·
                    by_cases hcut : n < 11040
                    ·
                      by_cases hcut : n < 11020
                      ·
                        let i : Fin 20 := ⟨n - 11000, by omega⟩
                        have hval : i.val + 11000 = n := by change n - 11000 + 11000 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 11000)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_11000_11019 i hlen'
                      ·
                        let i : Fin 20 := ⟨n - 11020, by omega⟩
                        have hval : i.val + 11020 = n := by change n - 11020 + 11020 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 11020)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_11020_11039 i hlen'
                    ·
                      by_cases hcut : n < 11060
                      ·
                        let i : Fin 20 := ⟨n - 11040, by omega⟩
                        have hval : i.val + 11040 = n := by change n - 11040 + 11040 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 11040)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_11040_11059 i hlen'
                      ·
                        by_cases hcut : n < 11080
                        ·
                          let i : Fin 20 := ⟨n - 11060, by omega⟩
                          have hval : i.val + 11060 = n := by change n - 11060 + 11060 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 11060)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_11060_11079 i hlen'
                        ·
                          let i : Fin 20 := ⟨n - 11080, by omega⟩
                          have hval : i.val + 11080 = n := by change n - 11080 + 11080 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 11080)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_11080_11099 i hlen'
                  ·
                    by_cases hcut : n < 11160
                    ·
                      by_cases hcut : n < 11120
                      ·
                        let i : Fin 20 := ⟨n - 11100, by omega⟩
                        have hval : i.val + 11100 = n := by change n - 11100 + 11100 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 11100)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_11100_11119 i hlen'
                      ·
                        by_cases hcut : n < 11140
                        ·
                          let i : Fin 20 := ⟨n - 11120, by omega⟩
                          have hval : i.val + 11120 = n := by change n - 11120 + 11120 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 11120)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_11120_11139 i hlen'
                        ·
                          let i : Fin 20 := ⟨n - 11140, by omega⟩
                          have hval : i.val + 11140 = n := by change n - 11140 + 11140 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 11140)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_11140_11159 i hlen'
                    ·
                      by_cases hcut : n < 11180
                      ·
                        let i : Fin 20 := ⟨n - 11160, by omega⟩
                        have hval : i.val + 11160 = n := by change n - 11160 + 11160 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 11160)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_11160_11179 i hlen'
                      ·
                        by_cases hcut : n < 11200
                        ·
                          let i : Fin 20 := ⟨n - 11180, by omega⟩
                          have hval : i.val + 11180 = n := by change n - 11180 + 11180 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 11180)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_11180_11199 i hlen'
                        ·
                          let i : Fin 20 := ⟨n - 11200, by omega⟩
                          have hval : i.val + 11200 = n := by change n - 11200 + 11200 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 11200)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_11200_11219 i hlen'
              ·
                by_cases hcut : n < 11440
                ·
                  by_cases hcut : n < 11320
                  ·
                    by_cases hcut : n < 11260
                    ·
                      by_cases hcut : n < 11240
                      ·
                        let i : Fin 20 := ⟨n - 11220, by omega⟩
                        have hval : i.val + 11220 = n := by change n - 11220 + 11220 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 11220)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_11220_11239 i hlen'
                      ·
                        let i : Fin 20 := ⟨n - 11240, by omega⟩
                        have hval : i.val + 11240 = n := by change n - 11240 + 11240 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 11240)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_11240_11259 i hlen'
                    ·
                      by_cases hcut : n < 11280
                      ·
                        let i : Fin 20 := ⟨n - 11260, by omega⟩
                        have hval : i.val + 11260 = n := by change n - 11260 + 11260 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 11260)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_11260_11279 i hlen'
                      ·
                        by_cases hcut : n < 11300
                        ·
                          let i : Fin 20 := ⟨n - 11280, by omega⟩
                          have hval : i.val + 11280 = n := by change n - 11280 + 11280 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 11280)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_11280_11299 i hlen'
                        ·
                          let i : Fin 20 := ⟨n - 11300, by omega⟩
                          have hval : i.val + 11300 = n := by change n - 11300 + 11300 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 11300)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_11300_11319 i hlen'
                  ·
                    by_cases hcut : n < 11380
                    ·
                      by_cases hcut : n < 11340
                      ·
                        let i : Fin 20 := ⟨n - 11320, by omega⟩
                        have hval : i.val + 11320 = n := by change n - 11320 + 11320 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 11320)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_11320_11339 i hlen'
                      ·
                        by_cases hcut : n < 11360
                        ·
                          let i : Fin 20 := ⟨n - 11340, by omega⟩
                          have hval : i.val + 11340 = n := by change n - 11340 + 11340 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 11340)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_11340_11359 i hlen'
                        ·
                          let i : Fin 20 := ⟨n - 11360, by omega⟩
                          have hval : i.val + 11360 = n := by change n - 11360 + 11360 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 11360)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_11360_11379 i hlen'
                    ·
                      by_cases hcut : n < 11400
                      ·
                        let i : Fin 20 := ⟨n - 11380, by omega⟩
                        have hval : i.val + 11380 = n := by change n - 11380 + 11380 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 11380)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_11380_11399 i hlen'
                      ·
                        by_cases hcut : n < 11420
                        ·
                          let i : Fin 20 := ⟨n - 11400, by omega⟩
                          have hval : i.val + 11400 = n := by change n - 11400 + 11400 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 11400)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_11400_11419 i hlen'
                        ·
                          let i : Fin 20 := ⟨n - 11420, by omega⟩
                          have hval : i.val + 11420 = n := by change n - 11420 + 11420 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 11420)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_11420_11439 i hlen'
                ·
                  by_cases hcut : n < 11560
                  ·
                    by_cases hcut : n < 11500
                    ·
                      by_cases hcut : n < 11460
                      ·
                        let i : Fin 20 := ⟨n - 11440, by omega⟩
                        have hval : i.val + 11440 = n := by change n - 11440 + 11440 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 11440)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_11440_11459 i hlen'
                      ·
                        by_cases hcut : n < 11480
                        ·
                          let i : Fin 20 := ⟨n - 11460, by omega⟩
                          have hval : i.val + 11460 = n := by change n - 11460 + 11460 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 11460)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_11460_11479 i hlen'
                        ·
                          let i : Fin 20 := ⟨n - 11480, by omega⟩
                          have hval : i.val + 11480 = n := by change n - 11480 + 11480 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 11480)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_11480_11499 i hlen'
                    ·
                      by_cases hcut : n < 11520
                      ·
                        let i : Fin 20 := ⟨n - 11500, by omega⟩
                        have hval : i.val + 11500 = n := by change n - 11500 + 11500 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 11500)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_11500_11519 i hlen'
                      ·
                        by_cases hcut : n < 11540
                        ·
                          let i : Fin 20 := ⟨n - 11520, by omega⟩
                          have hval : i.val + 11520 = n := by change n - 11520 + 11520 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 11520)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_11520_11539 i hlen'
                        ·
                          let i : Fin 20 := ⟨n - 11540, by omega⟩
                          have hval : i.val + 11540 = n := by change n - 11540 + 11540 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 11540)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_11540_11559 i hlen'
                  ·
                    by_cases hcut : n < 11620
                    ·
                      by_cases hcut : n < 11580
                      ·
                        let i : Fin 20 := ⟨n - 11560, by omega⟩
                        have hval : i.val + 11560 = n := by change n - 11560 + 11560 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 11560)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_11560_11579 i hlen'
                      ·
                        by_cases hcut : n < 11600
                        ·
                          let i : Fin 20 := ⟨n - 11580, by omega⟩
                          have hval : i.val + 11580 = n := by change n - 11580 + 11580 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 11580)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_11580_11599 i hlen'
                        ·
                          let i : Fin 20 := ⟨n - 11600, by omega⟩
                          have hval : i.val + 11600 = n := by change n - 11600 + 11600 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 11600)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_11600_11619 i hlen'
                    ·
                      by_cases hcut : n < 11640
                      ·
                        let i : Fin 20 := ⟨n - 11620, by omega⟩
                        have hval : i.val + 11620 = n := by change n - 11620 + 11620 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 11620)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_11620_11639 i hlen'
                      ·
                        by_cases hcut : n < 11660
                        ·
                          let i : Fin 20 := ⟨n - 11640, by omega⟩
                          have hval : i.val + 11640 = n := by change n - 11640 + 11640 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 11640)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_11640_11659 i hlen'
                        ·
                          let i : Fin 20 := ⟨n - 11660, by omega⟩
                          have hval : i.val + 11660 = n := by change n - 11660 + 11660 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 11660)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_11660_11679 i hlen'
            ·
              by_cases hcut : n < 12120
              ·
                by_cases hcut : n < 11900
                ·
                  by_cases hcut : n < 11780
                  ·
                    by_cases hcut : n < 11720
                    ·
                      by_cases hcut : n < 11700
                      ·
                        let i : Fin 20 := ⟨n - 11680, by omega⟩
                        have hval : i.val + 11680 = n := by change n - 11680 + 11680 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 11680)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_11680_11699 i hlen'
                      ·
                        let i : Fin 20 := ⟨n - 11700, by omega⟩
                        have hval : i.val + 11700 = n := by change n - 11700 + 11700 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 11700)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_11700_11719 i hlen'
                    ·
                      by_cases hcut : n < 11740
                      ·
                        let i : Fin 20 := ⟨n - 11720, by omega⟩
                        have hval : i.val + 11720 = n := by change n - 11720 + 11720 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 11720)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_11720_11739 i hlen'
                      ·
                        by_cases hcut : n < 11760
                        ·
                          let i : Fin 20 := ⟨n - 11740, by omega⟩
                          have hval : i.val + 11740 = n := by change n - 11740 + 11740 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 11740)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_11740_11759 i hlen'
                        ·
                          let i : Fin 20 := ⟨n - 11760, by omega⟩
                          have hval : i.val + 11760 = n := by change n - 11760 + 11760 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 11760)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_11760_11779 i hlen'
                  ·
                    by_cases hcut : n < 11840
                    ·
                      by_cases hcut : n < 11800
                      ·
                        let i : Fin 20 := ⟨n - 11780, by omega⟩
                        have hval : i.val + 11780 = n := by change n - 11780 + 11780 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 11780)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_11780_11799 i hlen'
                      ·
                        by_cases hcut : n < 11820
                        ·
                          let i : Fin 20 := ⟨n - 11800, by omega⟩
                          have hval : i.val + 11800 = n := by change n - 11800 + 11800 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 11800)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_11800_11819 i hlen'
                        ·
                          let i : Fin 20 := ⟨n - 11820, by omega⟩
                          have hval : i.val + 11820 = n := by change n - 11820 + 11820 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 11820)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_11820_11839 i hlen'
                    ·
                      by_cases hcut : n < 11860
                      ·
                        let i : Fin 20 := ⟨n - 11840, by omega⟩
                        have hval : i.val + 11840 = n := by change n - 11840 + 11840 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 11840)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_11840_11859 i hlen'
                      ·
                        by_cases hcut : n < 11880
                        ·
                          let i : Fin 20 := ⟨n - 11860, by omega⟩
                          have hval : i.val + 11860 = n := by change n - 11860 + 11860 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 11860)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_11860_11879 i hlen'
                        ·
                          let i : Fin 20 := ⟨n - 11880, by omega⟩
                          have hval : i.val + 11880 = n := by change n - 11880 + 11880 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 11880)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_11880_11899 i hlen'
                ·
                  by_cases hcut : n < 12000
                  ·
                    by_cases hcut : n < 11940
                    ·
                      by_cases hcut : n < 11920
                      ·
                        let i : Fin 20 := ⟨n - 11900, by omega⟩
                        have hval : i.val + 11900 = n := by change n - 11900 + 11900 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 11900)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_11900_11919 i hlen'
                      ·
                        let i : Fin 20 := ⟨n - 11920, by omega⟩
                        have hval : i.val + 11920 = n := by change n - 11920 + 11920 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 11920)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_11920_11939 i hlen'
                    ·
                      by_cases hcut : n < 11960
                      ·
                        let i : Fin 20 := ⟨n - 11940, by omega⟩
                        have hval : i.val + 11940 = n := by change n - 11940 + 11940 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 11940)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_11940_11959 i hlen'
                      ·
                        by_cases hcut : n < 11980
                        ·
                          let i : Fin 20 := ⟨n - 11960, by omega⟩
                          have hval : i.val + 11960 = n := by change n - 11960 + 11960 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 11960)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_11960_11979 i hlen'
                        ·
                          let i : Fin 20 := ⟨n - 11980, by omega⟩
                          have hval : i.val + 11980 = n := by change n - 11980 + 11980 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 11980)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_11980_11999 i hlen'
                  ·
                    by_cases hcut : n < 12060
                    ·
                      by_cases hcut : n < 12020
                      ·
                        let i : Fin 20 := ⟨n - 12000, by omega⟩
                        have hval : i.val + 12000 = n := by change n - 12000 + 12000 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 12000)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_12000_12019 i hlen'
                      ·
                        by_cases hcut : n < 12040
                        ·
                          let i : Fin 20 := ⟨n - 12020, by omega⟩
                          have hval : i.val + 12020 = n := by change n - 12020 + 12020 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 12020)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_12020_12039 i hlen'
                        ·
                          let i : Fin 20 := ⟨n - 12040, by omega⟩
                          have hval : i.val + 12040 = n := by change n - 12040 + 12040 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 12040)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_12040_12059 i hlen'
                    ·
                      by_cases hcut : n < 12080
                      ·
                        let i : Fin 20 := ⟨n - 12060, by omega⟩
                        have hval : i.val + 12060 = n := by change n - 12060 + 12060 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 12060)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_12060_12079 i hlen'
                      ·
                        by_cases hcut : n < 12100
                        ·
                          let i : Fin 20 := ⟨n - 12080, by omega⟩
                          have hval : i.val + 12080 = n := by change n - 12080 + 12080 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 12080)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_12080_12099 i hlen'
                        ·
                          let i : Fin 20 := ⟨n - 12100, by omega⟩
                          have hval : i.val + 12100 = n := by change n - 12100 + 12100 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 12100)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_12100_12119 i hlen'
              ·
                by_cases hcut : n < 12340
                ·
                  by_cases hcut : n < 12220
                  ·
                    by_cases hcut : n < 12160
                    ·
                      by_cases hcut : n < 12140
                      ·
                        let i : Fin 20 := ⟨n - 12120, by omega⟩
                        have hval : i.val + 12120 = n := by change n - 12120 + 12120 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 12120)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_12120_12139 i hlen'
                      ·
                        let i : Fin 20 := ⟨n - 12140, by omega⟩
                        have hval : i.val + 12140 = n := by change n - 12140 + 12140 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 12140)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_12140_12159 i hlen'
                    ·
                      by_cases hcut : n < 12180
                      ·
                        let i : Fin 20 := ⟨n - 12160, by omega⟩
                        have hval : i.val + 12160 = n := by change n - 12160 + 12160 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 12160)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_12160_12179 i hlen'
                      ·
                        by_cases hcut : n < 12200
                        ·
                          let i : Fin 20 := ⟨n - 12180, by omega⟩
                          have hval : i.val + 12180 = n := by change n - 12180 + 12180 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 12180)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_12180_12199 i hlen'
                        ·
                          let i : Fin 20 := ⟨n - 12200, by omega⟩
                          have hval : i.val + 12200 = n := by change n - 12200 + 12200 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 12200)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_12200_12219 i hlen'
                  ·
                    by_cases hcut : n < 12280
                    ·
                      by_cases hcut : n < 12240
                      ·
                        let i : Fin 20 := ⟨n - 12220, by omega⟩
                        have hval : i.val + 12220 = n := by change n - 12220 + 12220 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 12220)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_12220_12239 i hlen'
                      ·
                        by_cases hcut : n < 12260
                        ·
                          let i : Fin 20 := ⟨n - 12240, by omega⟩
                          have hval : i.val + 12240 = n := by change n - 12240 + 12240 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 12240)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_12240_12259 i hlen'
                        ·
                          let i : Fin 20 := ⟨n - 12260, by omega⟩
                          have hval : i.val + 12260 = n := by change n - 12260 + 12260 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 12260)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_12260_12279 i hlen'
                    ·
                      by_cases hcut : n < 12300
                      ·
                        let i : Fin 20 := ⟨n - 12280, by omega⟩
                        have hval : i.val + 12280 = n := by change n - 12280 + 12280 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 12280)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_12280_12299 i hlen'
                      ·
                        by_cases hcut : n < 12320
                        ·
                          let i : Fin 20 := ⟨n - 12300, by omega⟩
                          have hval : i.val + 12300 = n := by change n - 12300 + 12300 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 12300)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_12300_12319 i hlen'
                        ·
                          let i : Fin 20 := ⟨n - 12320, by omega⟩
                          have hval : i.val + 12320 = n := by change n - 12320 + 12320 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 12320)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_12320_12339 i hlen'
                ·
                  by_cases hcut : n < 12460
                  ·
                    by_cases hcut : n < 12400
                    ·
                      by_cases hcut : n < 12360
                      ·
                        let i : Fin 20 := ⟨n - 12340, by omega⟩
                        have hval : i.val + 12340 = n := by change n - 12340 + 12340 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 12340)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_12340_12359 i hlen'
                      ·
                        by_cases hcut : n < 12380
                        ·
                          let i : Fin 20 := ⟨n - 12360, by omega⟩
                          have hval : i.val + 12360 = n := by change n - 12360 + 12360 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 12360)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_12360_12379 i hlen'
                        ·
                          let i : Fin 20 := ⟨n - 12380, by omega⟩
                          have hval : i.val + 12380 = n := by change n - 12380 + 12380 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 12380)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_12380_12399 i hlen'
                    ·
                      by_cases hcut : n < 12420
                      ·
                        let i : Fin 20 := ⟨n - 12400, by omega⟩
                        have hval : i.val + 12400 = n := by change n - 12400 + 12400 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 12400)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_12400_12419 i hlen'
                      ·
                        by_cases hcut : n < 12440
                        ·
                          let i : Fin 20 := ⟨n - 12420, by omega⟩
                          have hval : i.val + 12420 = n := by change n - 12420 + 12420 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 12420)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_12420_12439 i hlen'
                        ·
                          let i : Fin 20 := ⟨n - 12440, by omega⟩
                          have hval : i.val + 12440 = n := by change n - 12440 + 12440 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 12440)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_12440_12459 i hlen'
                  ·
                    by_cases hcut : n < 12520
                    ·
                      by_cases hcut : n < 12480
                      ·
                        let i : Fin 20 := ⟨n - 12460, by omega⟩
                        have hval : i.val + 12460 = n := by change n - 12460 + 12460 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 12460)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_12460_12479 i hlen'
                      ·
                        by_cases hcut : n < 12500
                        ·
                          let i : Fin 20 := ⟨n - 12480, by omega⟩
                          have hval : i.val + 12480 = n := by change n - 12480 + 12480 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 12480)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_12480_12499 i hlen'
                        ·
                          let i : Fin 20 := ⟨n - 12500, by omega⟩
                          have hval : i.val + 12500 = n := by change n - 12500 + 12500 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 12500)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_12500_12519 i hlen'
                    ·
                      by_cases hcut : n < 12540
                      ·
                        let i : Fin 20 := ⟨n - 12520, by omega⟩
                        have hval : i.val + 12520 = n := by change n - 12520 + 12520 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 12520)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_12520_12539 i hlen'
                      ·
                        by_cases hcut : n < 12560
                        ·
                          let i : Fin 20 := ⟨n - 12540, by omega⟩
                          have hval : i.val + 12540 = n := by change n - 12540 + 12540 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 12540)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_12540_12559 i hlen'
                        ·
                          let i : Fin 20 := ⟨n - 12560, by omega⟩
                          have hval : i.val + 12560 = n := by change n - 12560 + 12560 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 12560)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_12560_12579 i hlen'
          ·
            by_cases hcut : n < 13480
            ·
              by_cases hcut : n < 13020
              ·
                by_cases hcut : n < 12800
                ·
                  by_cases hcut : n < 12680
                  ·
                    by_cases hcut : n < 12620
                    ·
                      by_cases hcut : n < 12600
                      ·
                        let i : Fin 20 := ⟨n - 12580, by omega⟩
                        have hval : i.val + 12580 = n := by change n - 12580 + 12580 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 12580)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_12580_12599 i hlen'
                      ·
                        let i : Fin 20 := ⟨n - 12600, by omega⟩
                        have hval : i.val + 12600 = n := by change n - 12600 + 12600 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 12600)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_12600_12619 i hlen'
                    ·
                      by_cases hcut : n < 12640
                      ·
                        let i : Fin 20 := ⟨n - 12620, by omega⟩
                        have hval : i.val + 12620 = n := by change n - 12620 + 12620 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 12620)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_12620_12639 i hlen'
                      ·
                        by_cases hcut : n < 12660
                        ·
                          let i : Fin 20 := ⟨n - 12640, by omega⟩
                          have hval : i.val + 12640 = n := by change n - 12640 + 12640 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 12640)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_12640_12659 i hlen'
                        ·
                          let i : Fin 20 := ⟨n - 12660, by omega⟩
                          have hval : i.val + 12660 = n := by change n - 12660 + 12660 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 12660)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_12660_12679 i hlen'
                  ·
                    by_cases hcut : n < 12740
                    ·
                      by_cases hcut : n < 12700
                      ·
                        let i : Fin 20 := ⟨n - 12680, by omega⟩
                        have hval : i.val + 12680 = n := by change n - 12680 + 12680 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 12680)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_12680_12699 i hlen'
                      ·
                        by_cases hcut : n < 12720
                        ·
                          let i : Fin 20 := ⟨n - 12700, by omega⟩
                          have hval : i.val + 12700 = n := by change n - 12700 + 12700 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 12700)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_12700_12719 i hlen'
                        ·
                          let i : Fin 20 := ⟨n - 12720, by omega⟩
                          have hval : i.val + 12720 = n := by change n - 12720 + 12720 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 12720)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_12720_12739 i hlen'
                    ·
                      by_cases hcut : n < 12760
                      ·
                        let i : Fin 20 := ⟨n - 12740, by omega⟩
                        have hval : i.val + 12740 = n := by change n - 12740 + 12740 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 12740)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_12740_12759 i hlen'
                      ·
                        by_cases hcut : n < 12780
                        ·
                          let i : Fin 20 := ⟨n - 12760, by omega⟩
                          have hval : i.val + 12760 = n := by change n - 12760 + 12760 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 12760)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_12760_12779 i hlen'
                        ·
                          let i : Fin 20 := ⟨n - 12780, by omega⟩
                          have hval : i.val + 12780 = n := by change n - 12780 + 12780 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 12780)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_12780_12799 i hlen'
                ·
                  by_cases hcut : n < 12900
                  ·
                    by_cases hcut : n < 12840
                    ·
                      by_cases hcut : n < 12820
                      ·
                        let i : Fin 20 := ⟨n - 12800, by omega⟩
                        have hval : i.val + 12800 = n := by change n - 12800 + 12800 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 12800)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_12800_12819 i hlen'
                      ·
                        let i : Fin 20 := ⟨n - 12820, by omega⟩
                        have hval : i.val + 12820 = n := by change n - 12820 + 12820 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 12820)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_12820_12839 i hlen'
                    ·
                      by_cases hcut : n < 12860
                      ·
                        let i : Fin 20 := ⟨n - 12840, by omega⟩
                        have hval : i.val + 12840 = n := by change n - 12840 + 12840 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 12840)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_12840_12859 i hlen'
                      ·
                        by_cases hcut : n < 12880
                        ·
                          let i : Fin 20 := ⟨n - 12860, by omega⟩
                          have hval : i.val + 12860 = n := by change n - 12860 + 12860 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 12860)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_12860_12879 i hlen'
                        ·
                          let i : Fin 20 := ⟨n - 12880, by omega⟩
                          have hval : i.val + 12880 = n := by change n - 12880 + 12880 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 12880)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_12880_12899 i hlen'
                  ·
                    by_cases hcut : n < 12960
                    ·
                      by_cases hcut : n < 12920
                      ·
                        let i : Fin 20 := ⟨n - 12900, by omega⟩
                        have hval : i.val + 12900 = n := by change n - 12900 + 12900 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 12900)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_12900_12919 i hlen'
                      ·
                        by_cases hcut : n < 12940
                        ·
                          let i : Fin 20 := ⟨n - 12920, by omega⟩
                          have hval : i.val + 12920 = n := by change n - 12920 + 12920 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 12920)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_12920_12939 i hlen'
                        ·
                          let i : Fin 20 := ⟨n - 12940, by omega⟩
                          have hval : i.val + 12940 = n := by change n - 12940 + 12940 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 12940)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_12940_12959 i hlen'
                    ·
                      by_cases hcut : n < 12980
                      ·
                        let i : Fin 20 := ⟨n - 12960, by omega⟩
                        have hval : i.val + 12960 = n := by change n - 12960 + 12960 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 12960)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_12960_12979 i hlen'
                      ·
                        by_cases hcut : n < 13000
                        ·
                          let i : Fin 20 := ⟨n - 12980, by omega⟩
                          have hval : i.val + 12980 = n := by change n - 12980 + 12980 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 12980)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_12980_12999 i hlen'
                        ·
                          let i : Fin 20 := ⟨n - 13000, by omega⟩
                          have hval : i.val + 13000 = n := by change n - 13000 + 13000 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 13000)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_13000_13019 i hlen'
              ·
                by_cases hcut : n < 13240
                ·
                  by_cases hcut : n < 13120
                  ·
                    by_cases hcut : n < 13060
                    ·
                      by_cases hcut : n < 13040
                      ·
                        let i : Fin 20 := ⟨n - 13020, by omega⟩
                        have hval : i.val + 13020 = n := by change n - 13020 + 13020 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 13020)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_13020_13039 i hlen'
                      ·
                        let i : Fin 20 := ⟨n - 13040, by omega⟩
                        have hval : i.val + 13040 = n := by change n - 13040 + 13040 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 13040)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_13040_13059 i hlen'
                    ·
                      by_cases hcut : n < 13080
                      ·
                        let i : Fin 20 := ⟨n - 13060, by omega⟩
                        have hval : i.val + 13060 = n := by change n - 13060 + 13060 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 13060)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_13060_13079 i hlen'
                      ·
                        by_cases hcut : n < 13100
                        ·
                          let i : Fin 20 := ⟨n - 13080, by omega⟩
                          have hval : i.val + 13080 = n := by change n - 13080 + 13080 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 13080)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_13080_13099 i hlen'
                        ·
                          let i : Fin 20 := ⟨n - 13100, by omega⟩
                          have hval : i.val + 13100 = n := by change n - 13100 + 13100 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 13100)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_13100_13119 i hlen'
                  ·
                    by_cases hcut : n < 13180
                    ·
                      by_cases hcut : n < 13140
                      ·
                        let i : Fin 20 := ⟨n - 13120, by omega⟩
                        have hval : i.val + 13120 = n := by change n - 13120 + 13120 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 13120)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_13120_13139 i hlen'
                      ·
                        by_cases hcut : n < 13160
                        ·
                          let i : Fin 20 := ⟨n - 13140, by omega⟩
                          have hval : i.val + 13140 = n := by change n - 13140 + 13140 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 13140)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_13140_13159 i hlen'
                        ·
                          let i : Fin 20 := ⟨n - 13160, by omega⟩
                          have hval : i.val + 13160 = n := by change n - 13160 + 13160 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 13160)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_13160_13179 i hlen'
                    ·
                      by_cases hcut : n < 13200
                      ·
                        let i : Fin 20 := ⟨n - 13180, by omega⟩
                        have hval : i.val + 13180 = n := by change n - 13180 + 13180 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 13180)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_13180_13199 i hlen'
                      ·
                        by_cases hcut : n < 13220
                        ·
                          let i : Fin 20 := ⟨n - 13200, by omega⟩
                          have hval : i.val + 13200 = n := by change n - 13200 + 13200 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 13200)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_13200_13219 i hlen'
                        ·
                          let i : Fin 20 := ⟨n - 13220, by omega⟩
                          have hval : i.val + 13220 = n := by change n - 13220 + 13220 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 13220)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_13220_13239 i hlen'
                ·
                  by_cases hcut : n < 13360
                  ·
                    by_cases hcut : n < 13300
                    ·
                      by_cases hcut : n < 13260
                      ·
                        let i : Fin 20 := ⟨n - 13240, by omega⟩
                        have hval : i.val + 13240 = n := by change n - 13240 + 13240 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 13240)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_13240_13259 i hlen'
                      ·
                        by_cases hcut : n < 13280
                        ·
                          let i : Fin 20 := ⟨n - 13260, by omega⟩
                          have hval : i.val + 13260 = n := by change n - 13260 + 13260 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 13260)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_13260_13279 i hlen'
                        ·
                          let i : Fin 20 := ⟨n - 13280, by omega⟩
                          have hval : i.val + 13280 = n := by change n - 13280 + 13280 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 13280)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_13280_13299 i hlen'
                    ·
                      by_cases hcut : n < 13320
                      ·
                        let i : Fin 20 := ⟨n - 13300, by omega⟩
                        have hval : i.val + 13300 = n := by change n - 13300 + 13300 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 13300)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_13300_13319 i hlen'
                      ·
                        by_cases hcut : n < 13340
                        ·
                          let i : Fin 20 := ⟨n - 13320, by omega⟩
                          have hval : i.val + 13320 = n := by change n - 13320 + 13320 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 13320)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_13320_13339 i hlen'
                        ·
                          let i : Fin 20 := ⟨n - 13340, by omega⟩
                          have hval : i.val + 13340 = n := by change n - 13340 + 13340 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 13340)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_13340_13359 i hlen'
                  ·
                    by_cases hcut : n < 13420
                    ·
                      by_cases hcut : n < 13380
                      ·
                        let i : Fin 20 := ⟨n - 13360, by omega⟩
                        have hval : i.val + 13360 = n := by change n - 13360 + 13360 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 13360)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_13360_13379 i hlen'
                      ·
                        by_cases hcut : n < 13400
                        ·
                          let i : Fin 20 := ⟨n - 13380, by omega⟩
                          have hval : i.val + 13380 = n := by change n - 13380 + 13380 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 13380)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_13380_13399 i hlen'
                        ·
                          let i : Fin 20 := ⟨n - 13400, by omega⟩
                          have hval : i.val + 13400 = n := by change n - 13400 + 13400 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 13400)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_13400_13419 i hlen'
                    ·
                      by_cases hcut : n < 13440
                      ·
                        let i : Fin 20 := ⟨n - 13420, by omega⟩
                        have hval : i.val + 13420 = n := by change n - 13420 + 13420 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 13420)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_13420_13439 i hlen'
                      ·
                        by_cases hcut : n < 13460
                        ·
                          let i : Fin 20 := ⟨n - 13440, by omega⟩
                          have hval : i.val + 13440 = n := by change n - 13440 + 13440 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 13440)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_13440_13459 i hlen'
                        ·
                          let i : Fin 20 := ⟨n - 13460, by omega⟩
                          have hval : i.val + 13460 = n := by change n - 13460 + 13460 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 13460)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_13460_13479 i hlen'
            ·
              by_cases hcut : n < 13920
              ·
                by_cases hcut : n < 13700
                ·
                  by_cases hcut : n < 13580
                  ·
                    by_cases hcut : n < 13520
                    ·
                      by_cases hcut : n < 13500
                      ·
                        let i : Fin 20 := ⟨n - 13480, by omega⟩
                        have hval : i.val + 13480 = n := by change n - 13480 + 13480 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 13480)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_13480_13499 i hlen'
                      ·
                        let i : Fin 20 := ⟨n - 13500, by omega⟩
                        have hval : i.val + 13500 = n := by change n - 13500 + 13500 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 13500)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_13500_13519 i hlen'
                    ·
                      by_cases hcut : n < 13540
                      ·
                        let i : Fin 20 := ⟨n - 13520, by omega⟩
                        have hval : i.val + 13520 = n := by change n - 13520 + 13520 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 13520)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_13520_13539 i hlen'
                      ·
                        by_cases hcut : n < 13560
                        ·
                          let i : Fin 20 := ⟨n - 13540, by omega⟩
                          have hval : i.val + 13540 = n := by change n - 13540 + 13540 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 13540)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_13540_13559 i hlen'
                        ·
                          let i : Fin 20 := ⟨n - 13560, by omega⟩
                          have hval : i.val + 13560 = n := by change n - 13560 + 13560 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 13560)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_13560_13579 i hlen'
                  ·
                    by_cases hcut : n < 13640
                    ·
                      by_cases hcut : n < 13600
                      ·
                        let i : Fin 20 := ⟨n - 13580, by omega⟩
                        have hval : i.val + 13580 = n := by change n - 13580 + 13580 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 13580)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_13580_13599 i hlen'
                      ·
                        by_cases hcut : n < 13620
                        ·
                          let i : Fin 20 := ⟨n - 13600, by omega⟩
                          have hval : i.val + 13600 = n := by change n - 13600 + 13600 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 13600)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_13600_13619 i hlen'
                        ·
                          let i : Fin 20 := ⟨n - 13620, by omega⟩
                          have hval : i.val + 13620 = n := by change n - 13620 + 13620 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 13620)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_13620_13639 i hlen'
                    ·
                      by_cases hcut : n < 13660
                      ·
                        let i : Fin 20 := ⟨n - 13640, by omega⟩
                        have hval : i.val + 13640 = n := by change n - 13640 + 13640 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 13640)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_13640_13659 i hlen'
                      ·
                        by_cases hcut : n < 13680
                        ·
                          let i : Fin 20 := ⟨n - 13660, by omega⟩
                          have hval : i.val + 13660 = n := by change n - 13660 + 13660 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 13660)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_13660_13679 i hlen'
                        ·
                          let i : Fin 20 := ⟨n - 13680, by omega⟩
                          have hval : i.val + 13680 = n := by change n - 13680 + 13680 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 13680)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_13680_13699 i hlen'
                ·
                  by_cases hcut : n < 13800
                  ·
                    by_cases hcut : n < 13740
                    ·
                      by_cases hcut : n < 13720
                      ·
                        let i : Fin 20 := ⟨n - 13700, by omega⟩
                        have hval : i.val + 13700 = n := by change n - 13700 + 13700 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 13700)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_13700_13719 i hlen'
                      ·
                        let i : Fin 20 := ⟨n - 13720, by omega⟩
                        have hval : i.val + 13720 = n := by change n - 13720 + 13720 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 13720)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_13720_13739 i hlen'
                    ·
                      by_cases hcut : n < 13760
                      ·
                        let i : Fin 20 := ⟨n - 13740, by omega⟩
                        have hval : i.val + 13740 = n := by change n - 13740 + 13740 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 13740)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_13740_13759 i hlen'
                      ·
                        by_cases hcut : n < 13780
                        ·
                          let i : Fin 20 := ⟨n - 13760, by omega⟩
                          have hval : i.val + 13760 = n := by change n - 13760 + 13760 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 13760)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_13760_13779 i hlen'
                        ·
                          let i : Fin 20 := ⟨n - 13780, by omega⟩
                          have hval : i.val + 13780 = n := by change n - 13780 + 13780 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 13780)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_13780_13799 i hlen'
                  ·
                    by_cases hcut : n < 13860
                    ·
                      by_cases hcut : n < 13820
                      ·
                        let i : Fin 20 := ⟨n - 13800, by omega⟩
                        have hval : i.val + 13800 = n := by change n - 13800 + 13800 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 13800)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_13800_13819 i hlen'
                      ·
                        by_cases hcut : n < 13840
                        ·
                          let i : Fin 20 := ⟨n - 13820, by omega⟩
                          have hval : i.val + 13820 = n := by change n - 13820 + 13820 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 13820)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_13820_13839 i hlen'
                        ·
                          let i : Fin 20 := ⟨n - 13840, by omega⟩
                          have hval : i.val + 13840 = n := by change n - 13840 + 13840 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 13840)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_13840_13859 i hlen'
                    ·
                      by_cases hcut : n < 13880
                      ·
                        let i : Fin 20 := ⟨n - 13860, by omega⟩
                        have hval : i.val + 13860 = n := by change n - 13860 + 13860 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 13860)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_13860_13879 i hlen'
                      ·
                        by_cases hcut : n < 13900
                        ·
                          let i : Fin 20 := ⟨n - 13880, by omega⟩
                          have hval : i.val + 13880 = n := by change n - 13880 + 13880 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 13880)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_13880_13899 i hlen'
                        ·
                          let i : Fin 20 := ⟨n - 13900, by omega⟩
                          have hval : i.val + 13900 = n := by change n - 13900 + 13900 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 13900)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_13900_13919 i hlen'
              ·
                by_cases hcut : n < 14140
                ·
                  by_cases hcut : n < 14020
                  ·
                    by_cases hcut : n < 13960
                    ·
                      by_cases hcut : n < 13940
                      ·
                        let i : Fin 20 := ⟨n - 13920, by omega⟩
                        have hval : i.val + 13920 = n := by change n - 13920 + 13920 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 13920)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_13920_13939 i hlen'
                      ·
                        let i : Fin 20 := ⟨n - 13940, by omega⟩
                        have hval : i.val + 13940 = n := by change n - 13940 + 13940 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 13940)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_13940_13959 i hlen'
                    ·
                      by_cases hcut : n < 13980
                      ·
                        let i : Fin 20 := ⟨n - 13960, by omega⟩
                        have hval : i.val + 13960 = n := by change n - 13960 + 13960 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 13960)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_13960_13979 i hlen'
                      ·
                        by_cases hcut : n < 14000
                        ·
                          let i : Fin 20 := ⟨n - 13980, by omega⟩
                          have hval : i.val + 13980 = n := by change n - 13980 + 13980 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 13980)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_13980_13999 i hlen'
                        ·
                          let i : Fin 20 := ⟨n - 14000, by omega⟩
                          have hval : i.val + 14000 = n := by change n - 14000 + 14000 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 14000)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_14000_14019 i hlen'
                  ·
                    by_cases hcut : n < 14080
                    ·
                      by_cases hcut : n < 14040
                      ·
                        let i : Fin 20 := ⟨n - 14020, by omega⟩
                        have hval : i.val + 14020 = n := by change n - 14020 + 14020 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 14020)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_14020_14039 i hlen'
                      ·
                        by_cases hcut : n < 14060
                        ·
                          let i : Fin 20 := ⟨n - 14040, by omega⟩
                          have hval : i.val + 14040 = n := by change n - 14040 + 14040 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 14040)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_14040_14059 i hlen'
                        ·
                          let i : Fin 20 := ⟨n - 14060, by omega⟩
                          have hval : i.val + 14060 = n := by change n - 14060 + 14060 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 14060)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_14060_14079 i hlen'
                    ·
                      by_cases hcut : n < 14100
                      ·
                        let i : Fin 20 := ⟨n - 14080, by omega⟩
                        have hval : i.val + 14080 = n := by change n - 14080 + 14080 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 14080)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_14080_14099 i hlen'
                      ·
                        by_cases hcut : n < 14120
                        ·
                          let i : Fin 20 := ⟨n - 14100, by omega⟩
                          have hval : i.val + 14100 = n := by change n - 14100 + 14100 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 14100)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_14100_14119 i hlen'
                        ·
                          let i : Fin 20 := ⟨n - 14120, by omega⟩
                          have hval : i.val + 14120 = n := by change n - 14120 + 14120 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 14120)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_14120_14139 i hlen'
                ·
                  by_cases hcut : n < 14260
                  ·
                    by_cases hcut : n < 14200
                    ·
                      by_cases hcut : n < 14160
                      ·
                        let i : Fin 20 := ⟨n - 14140, by omega⟩
                        have hval : i.val + 14140 = n := by change n - 14140 + 14140 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 14140)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_14140_14159 i hlen'
                      ·
                        by_cases hcut : n < 14180
                        ·
                          let i : Fin 20 := ⟨n - 14160, by omega⟩
                          have hval : i.val + 14160 = n := by change n - 14160 + 14160 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 14160)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_14160_14179 i hlen'
                        ·
                          let i : Fin 20 := ⟨n - 14180, by omega⟩
                          have hval : i.val + 14180 = n := by change n - 14180 + 14180 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 14180)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_14180_14199 i hlen'
                    ·
                      by_cases hcut : n < 14220
                      ·
                        let i : Fin 20 := ⟨n - 14200, by omega⟩
                        have hval : i.val + 14200 = n := by change n - 14200 + 14200 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 14200)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_14200_14219 i hlen'
                      ·
                        by_cases hcut : n < 14240
                        ·
                          let i : Fin 20 := ⟨n - 14220, by omega⟩
                          have hval : i.val + 14220 = n := by change n - 14220 + 14220 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 14220)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_14220_14239 i hlen'
                        ·
                          let i : Fin 20 := ⟨n - 14240, by omega⟩
                          have hval : i.val + 14240 = n := by change n - 14240 + 14240 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 14240)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_14240_14259 i hlen'
                  ·
                    by_cases hcut : n < 14320
                    ·
                      by_cases hcut : n < 14280
                      ·
                        let i : Fin 20 := ⟨n - 14260, by omega⟩
                        have hval : i.val + 14260 = n := by change n - 14260 + 14260 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 14260)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_14260_14279 i hlen'
                      ·
                        by_cases hcut : n < 14300
                        ·
                          let i : Fin 20 := ⟨n - 14280, by omega⟩
                          have hval : i.val + 14280 = n := by change n - 14280 + 14280 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 14280)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_14280_14299 i hlen'
                        ·
                          let i : Fin 20 := ⟨n - 14300, by omega⟩
                          have hval : i.val + 14300 = n := by change n - 14300 + 14300 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 14300)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_14300_14319 i hlen'
                    ·
                      by_cases hcut : n < 14340
                      ·
                        let i : Fin 20 := ⟨n - 14320, by omega⟩
                        have hval : i.val + 14320 = n := by change n - 14320 + 14320 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 14320)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_14320_14339 i hlen'
                      ·
                        by_cases hcut : n < 14360
                        ·
                          let i : Fin 20 := ⟨n - 14340, by omega⟩
                          have hval : i.val + 14340 = n := by change n - 14340 + 14340 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 14340)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_14340_14359 i hlen'
                        ·
                          let i : Fin 20 := ⟨n - 14360, by omega⟩
                          have hval : i.val + 14360 = n := by change n - 14360 + 14360 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 14360)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_14360_14379 i hlen'
    ·
      by_cases hcut : n < 21560
      ·
        by_cases hcut : n < 17960
        ·
          by_cases hcut : n < 16160
          ·
            by_cases hcut : n < 15260
            ·
              by_cases hcut : n < 14820
              ·
                by_cases hcut : n < 14600
                ·
                  by_cases hcut : n < 14480
                  ·
                    by_cases hcut : n < 14420
                    ·
                      by_cases hcut : n < 14400
                      ·
                        let i : Fin 20 := ⟨n - 14380, by omega⟩
                        have hval : i.val + 14380 = n := by change n - 14380 + 14380 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 14380)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_14380_14399 i hlen'
                      ·
                        let i : Fin 20 := ⟨n - 14400, by omega⟩
                        have hval : i.val + 14400 = n := by change n - 14400 + 14400 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 14400)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_14400_14419 i hlen'
                    ·
                      by_cases hcut : n < 14440
                      ·
                        let i : Fin 20 := ⟨n - 14420, by omega⟩
                        have hval : i.val + 14420 = n := by change n - 14420 + 14420 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 14420)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_14420_14439 i hlen'
                      ·
                        by_cases hcut : n < 14460
                        ·
                          let i : Fin 20 := ⟨n - 14440, by omega⟩
                          have hval : i.val + 14440 = n := by change n - 14440 + 14440 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 14440)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_14440_14459 i hlen'
                        ·
                          let i : Fin 20 := ⟨n - 14460, by omega⟩
                          have hval : i.val + 14460 = n := by change n - 14460 + 14460 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 14460)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_14460_14479 i hlen'
                  ·
                    by_cases hcut : n < 14540
                    ·
                      by_cases hcut : n < 14500
                      ·
                        let i : Fin 20 := ⟨n - 14480, by omega⟩
                        have hval : i.val + 14480 = n := by change n - 14480 + 14480 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 14480)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_14480_14499 i hlen'
                      ·
                        by_cases hcut : n < 14520
                        ·
                          let i : Fin 20 := ⟨n - 14500, by omega⟩
                          have hval : i.val + 14500 = n := by change n - 14500 + 14500 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 14500)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_14500_14519 i hlen'
                        ·
                          let i : Fin 20 := ⟨n - 14520, by omega⟩
                          have hval : i.val + 14520 = n := by change n - 14520 + 14520 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 14520)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_14520_14539 i hlen'
                    ·
                      by_cases hcut : n < 14560
                      ·
                        let i : Fin 20 := ⟨n - 14540, by omega⟩
                        have hval : i.val + 14540 = n := by change n - 14540 + 14540 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 14540)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_14540_14559 i hlen'
                      ·
                        by_cases hcut : n < 14580
                        ·
                          let i : Fin 20 := ⟨n - 14560, by omega⟩
                          have hval : i.val + 14560 = n := by change n - 14560 + 14560 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 14560)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_14560_14579 i hlen'
                        ·
                          let i : Fin 20 := ⟨n - 14580, by omega⟩
                          have hval : i.val + 14580 = n := by change n - 14580 + 14580 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 14580)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_14580_14599 i hlen'
                ·
                  by_cases hcut : n < 14700
                  ·
                    by_cases hcut : n < 14640
                    ·
                      by_cases hcut : n < 14620
                      ·
                        let i : Fin 20 := ⟨n - 14600, by omega⟩
                        have hval : i.val + 14600 = n := by change n - 14600 + 14600 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 14600)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_14600_14619 i hlen'
                      ·
                        let i : Fin 20 := ⟨n - 14620, by omega⟩
                        have hval : i.val + 14620 = n := by change n - 14620 + 14620 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 14620)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_14620_14639 i hlen'
                    ·
                      by_cases hcut : n < 14660
                      ·
                        let i : Fin 20 := ⟨n - 14640, by omega⟩
                        have hval : i.val + 14640 = n := by change n - 14640 + 14640 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 14640)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_14640_14659 i hlen'
                      ·
                        by_cases hcut : n < 14680
                        ·
                          let i : Fin 20 := ⟨n - 14660, by omega⟩
                          have hval : i.val + 14660 = n := by change n - 14660 + 14660 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 14660)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_14660_14679 i hlen'
                        ·
                          let i : Fin 20 := ⟨n - 14680, by omega⟩
                          have hval : i.val + 14680 = n := by change n - 14680 + 14680 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 14680)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_14680_14699 i hlen'
                  ·
                    by_cases hcut : n < 14760
                    ·
                      by_cases hcut : n < 14720
                      ·
                        let i : Fin 20 := ⟨n - 14700, by omega⟩
                        have hval : i.val + 14700 = n := by change n - 14700 + 14700 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 14700)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_14700_14719 i hlen'
                      ·
                        by_cases hcut : n < 14740
                        ·
                          let i : Fin 20 := ⟨n - 14720, by omega⟩
                          have hval : i.val + 14720 = n := by change n - 14720 + 14720 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 14720)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_14720_14739 i hlen'
                        ·
                          let i : Fin 20 := ⟨n - 14740, by omega⟩
                          have hval : i.val + 14740 = n := by change n - 14740 + 14740 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 14740)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_14740_14759 i hlen'
                    ·
                      by_cases hcut : n < 14780
                      ·
                        let i : Fin 20 := ⟨n - 14760, by omega⟩
                        have hval : i.val + 14760 = n := by change n - 14760 + 14760 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 14760)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_14760_14779 i hlen'
                      ·
                        by_cases hcut : n < 14800
                        ·
                          let i : Fin 20 := ⟨n - 14780, by omega⟩
                          have hval : i.val + 14780 = n := by change n - 14780 + 14780 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 14780)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_14780_14799 i hlen'
                        ·
                          let i : Fin 20 := ⟨n - 14800, by omega⟩
                          have hval : i.val + 14800 = n := by change n - 14800 + 14800 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 14800)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_14800_14819 i hlen'
              ·
                by_cases hcut : n < 15040
                ·
                  by_cases hcut : n < 14920
                  ·
                    by_cases hcut : n < 14860
                    ·
                      by_cases hcut : n < 14840
                      ·
                        let i : Fin 20 := ⟨n - 14820, by omega⟩
                        have hval : i.val + 14820 = n := by change n - 14820 + 14820 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 14820)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_14820_14839 i hlen'
                      ·
                        let i : Fin 20 := ⟨n - 14840, by omega⟩
                        have hval : i.val + 14840 = n := by change n - 14840 + 14840 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 14840)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_14840_14859 i hlen'
                    ·
                      by_cases hcut : n < 14880
                      ·
                        let i : Fin 20 := ⟨n - 14860, by omega⟩
                        have hval : i.val + 14860 = n := by change n - 14860 + 14860 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 14860)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_14860_14879 i hlen'
                      ·
                        by_cases hcut : n < 14900
                        ·
                          let i : Fin 20 := ⟨n - 14880, by omega⟩
                          have hval : i.val + 14880 = n := by change n - 14880 + 14880 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 14880)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_14880_14899 i hlen'
                        ·
                          let i : Fin 20 := ⟨n - 14900, by omega⟩
                          have hval : i.val + 14900 = n := by change n - 14900 + 14900 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 14900)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_14900_14919 i hlen'
                  ·
                    by_cases hcut : n < 14980
                    ·
                      by_cases hcut : n < 14940
                      ·
                        let i : Fin 20 := ⟨n - 14920, by omega⟩
                        have hval : i.val + 14920 = n := by change n - 14920 + 14920 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 14920)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_14920_14939 i hlen'
                      ·
                        by_cases hcut : n < 14960
                        ·
                          let i : Fin 20 := ⟨n - 14940, by omega⟩
                          have hval : i.val + 14940 = n := by change n - 14940 + 14940 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 14940)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_14940_14959 i hlen'
                        ·
                          let i : Fin 20 := ⟨n - 14960, by omega⟩
                          have hval : i.val + 14960 = n := by change n - 14960 + 14960 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 14960)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_14960_14979 i hlen'
                    ·
                      by_cases hcut : n < 15000
                      ·
                        let i : Fin 20 := ⟨n - 14980, by omega⟩
                        have hval : i.val + 14980 = n := by change n - 14980 + 14980 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 14980)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_14980_14999 i hlen'
                      ·
                        by_cases hcut : n < 15020
                        ·
                          let i : Fin 20 := ⟨n - 15000, by omega⟩
                          have hval : i.val + 15000 = n := by change n - 15000 + 15000 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 15000)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_15000_15019 i hlen'
                        ·
                          let i : Fin 20 := ⟨n - 15020, by omega⟩
                          have hval : i.val + 15020 = n := by change n - 15020 + 15020 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 15020)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_15020_15039 i hlen'
                ·
                  by_cases hcut : n < 15140
                  ·
                    by_cases hcut : n < 15080
                    ·
                      by_cases hcut : n < 15060
                      ·
                        let i : Fin 20 := ⟨n - 15040, by omega⟩
                        have hval : i.val + 15040 = n := by change n - 15040 + 15040 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 15040)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_15040_15059 i hlen'
                      ·
                        let i : Fin 20 := ⟨n - 15060, by omega⟩
                        have hval : i.val + 15060 = n := by change n - 15060 + 15060 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 15060)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_15060_15079 i hlen'
                    ·
                      by_cases hcut : n < 15100
                      ·
                        let i : Fin 20 := ⟨n - 15080, by omega⟩
                        have hval : i.val + 15080 = n := by change n - 15080 + 15080 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 15080)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_15080_15099 i hlen'
                      ·
                        by_cases hcut : n < 15120
                        ·
                          let i : Fin 20 := ⟨n - 15100, by omega⟩
                          have hval : i.val + 15100 = n := by change n - 15100 + 15100 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 15100)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_15100_15119 i hlen'
                        ·
                          let i : Fin 20 := ⟨n - 15120, by omega⟩
                          have hval : i.val + 15120 = n := by change n - 15120 + 15120 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 15120)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_15120_15139 i hlen'
                  ·
                    by_cases hcut : n < 15200
                    ·
                      by_cases hcut : n < 15160
                      ·
                        let i : Fin 20 := ⟨n - 15140, by omega⟩
                        have hval : i.val + 15140 = n := by change n - 15140 + 15140 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 15140)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_15140_15159 i hlen'
                      ·
                        by_cases hcut : n < 15180
                        ·
                          let i : Fin 20 := ⟨n - 15160, by omega⟩
                          have hval : i.val + 15160 = n := by change n - 15160 + 15160 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 15160)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_15160_15179 i hlen'
                        ·
                          let i : Fin 20 := ⟨n - 15180, by omega⟩
                          have hval : i.val + 15180 = n := by change n - 15180 + 15180 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 15180)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_15180_15199 i hlen'
                    ·
                      by_cases hcut : n < 15220
                      ·
                        let i : Fin 20 := ⟨n - 15200, by omega⟩
                        have hval : i.val + 15200 = n := by change n - 15200 + 15200 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 15200)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_15200_15219 i hlen'
                      ·
                        by_cases hcut : n < 15240
                        ·
                          let i : Fin 20 := ⟨n - 15220, by omega⟩
                          have hval : i.val + 15220 = n := by change n - 15220 + 15220 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 15220)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_15220_15239 i hlen'
                        ·
                          let i : Fin 20 := ⟨n - 15240, by omega⟩
                          have hval : i.val + 15240 = n := by change n - 15240 + 15240 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 15240)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_15240_15259 i hlen'
            ·
              by_cases hcut : n < 15700
              ·
                by_cases hcut : n < 15480
                ·
                  by_cases hcut : n < 15360
                  ·
                    by_cases hcut : n < 15300
                    ·
                      by_cases hcut : n < 15280
                      ·
                        let i : Fin 20 := ⟨n - 15260, by omega⟩
                        have hval : i.val + 15260 = n := by change n - 15260 + 15260 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 15260)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_15260_15279 i hlen'
                      ·
                        let i : Fin 20 := ⟨n - 15280, by omega⟩
                        have hval : i.val + 15280 = n := by change n - 15280 + 15280 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 15280)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_15280_15299 i hlen'
                    ·
                      by_cases hcut : n < 15320
                      ·
                        let i : Fin 20 := ⟨n - 15300, by omega⟩
                        have hval : i.val + 15300 = n := by change n - 15300 + 15300 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 15300)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_15300_15319 i hlen'
                      ·
                        by_cases hcut : n < 15340
                        ·
                          let i : Fin 20 := ⟨n - 15320, by omega⟩
                          have hval : i.val + 15320 = n := by change n - 15320 + 15320 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 15320)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_15320_15339 i hlen'
                        ·
                          let i : Fin 20 := ⟨n - 15340, by omega⟩
                          have hval : i.val + 15340 = n := by change n - 15340 + 15340 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 15340)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_15340_15359 i hlen'
                  ·
                    by_cases hcut : n < 15420
                    ·
                      by_cases hcut : n < 15380
                      ·
                        let i : Fin 20 := ⟨n - 15360, by omega⟩
                        have hval : i.val + 15360 = n := by change n - 15360 + 15360 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 15360)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_15360_15379 i hlen'
                      ·
                        by_cases hcut : n < 15400
                        ·
                          let i : Fin 20 := ⟨n - 15380, by omega⟩
                          have hval : i.val + 15380 = n := by change n - 15380 + 15380 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 15380)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_15380_15399 i hlen'
                        ·
                          let i : Fin 20 := ⟨n - 15400, by omega⟩
                          have hval : i.val + 15400 = n := by change n - 15400 + 15400 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 15400)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_15400_15419 i hlen'
                    ·
                      by_cases hcut : n < 15440
                      ·
                        let i : Fin 20 := ⟨n - 15420, by omega⟩
                        have hval : i.val + 15420 = n := by change n - 15420 + 15420 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 15420)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_15420_15439 i hlen'
                      ·
                        by_cases hcut : n < 15460
                        ·
                          let i : Fin 20 := ⟨n - 15440, by omega⟩
                          have hval : i.val + 15440 = n := by change n - 15440 + 15440 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 15440)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_15440_15459 i hlen'
                        ·
                          let i : Fin 20 := ⟨n - 15460, by omega⟩
                          have hval : i.val + 15460 = n := by change n - 15460 + 15460 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 15460)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_15460_15479 i hlen'
                ·
                  by_cases hcut : n < 15580
                  ·
                    by_cases hcut : n < 15520
                    ·
                      by_cases hcut : n < 15500
                      ·
                        let i : Fin 20 := ⟨n - 15480, by omega⟩
                        have hval : i.val + 15480 = n := by change n - 15480 + 15480 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 15480)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_15480_15499 i hlen'
                      ·
                        let i : Fin 20 := ⟨n - 15500, by omega⟩
                        have hval : i.val + 15500 = n := by change n - 15500 + 15500 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 15500)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_15500_15519 i hlen'
                    ·
                      by_cases hcut : n < 15540
                      ·
                        let i : Fin 20 := ⟨n - 15520, by omega⟩
                        have hval : i.val + 15520 = n := by change n - 15520 + 15520 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 15520)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_15520_15539 i hlen'
                      ·
                        by_cases hcut : n < 15560
                        ·
                          let i : Fin 20 := ⟨n - 15540, by omega⟩
                          have hval : i.val + 15540 = n := by change n - 15540 + 15540 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 15540)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_15540_15559 i hlen'
                        ·
                          let i : Fin 20 := ⟨n - 15560, by omega⟩
                          have hval : i.val + 15560 = n := by change n - 15560 + 15560 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 15560)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_15560_15579 i hlen'
                  ·
                    by_cases hcut : n < 15640
                    ·
                      by_cases hcut : n < 15600
                      ·
                        let i : Fin 20 := ⟨n - 15580, by omega⟩
                        have hval : i.val + 15580 = n := by change n - 15580 + 15580 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 15580)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_15580_15599 i hlen'
                      ·
                        by_cases hcut : n < 15620
                        ·
                          let i : Fin 20 := ⟨n - 15600, by omega⟩
                          have hval : i.val + 15600 = n := by change n - 15600 + 15600 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 15600)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_15600_15619 i hlen'
                        ·
                          let i : Fin 20 := ⟨n - 15620, by omega⟩
                          have hval : i.val + 15620 = n := by change n - 15620 + 15620 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 15620)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_15620_15639 i hlen'
                    ·
                      by_cases hcut : n < 15660
                      ·
                        let i : Fin 20 := ⟨n - 15640, by omega⟩
                        have hval : i.val + 15640 = n := by change n - 15640 + 15640 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 15640)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_15640_15659 i hlen'
                      ·
                        by_cases hcut : n < 15680
                        ·
                          let i : Fin 20 := ⟨n - 15660, by omega⟩
                          have hval : i.val + 15660 = n := by change n - 15660 + 15660 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 15660)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_15660_15679 i hlen'
                        ·
                          let i : Fin 20 := ⟨n - 15680, by omega⟩
                          have hval : i.val + 15680 = n := by change n - 15680 + 15680 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 15680)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_15680_15699 i hlen'
              ·
                by_cases hcut : n < 15920
                ·
                  by_cases hcut : n < 15800
                  ·
                    by_cases hcut : n < 15740
                    ·
                      by_cases hcut : n < 15720
                      ·
                        let i : Fin 20 := ⟨n - 15700, by omega⟩
                        have hval : i.val + 15700 = n := by change n - 15700 + 15700 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 15700)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_15700_15719 i hlen'
                      ·
                        let i : Fin 20 := ⟨n - 15720, by omega⟩
                        have hval : i.val + 15720 = n := by change n - 15720 + 15720 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 15720)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_15720_15739 i hlen'
                    ·
                      by_cases hcut : n < 15760
                      ·
                        let i : Fin 20 := ⟨n - 15740, by omega⟩
                        have hval : i.val + 15740 = n := by change n - 15740 + 15740 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 15740)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_15740_15759 i hlen'
                      ·
                        by_cases hcut : n < 15780
                        ·
                          let i : Fin 20 := ⟨n - 15760, by omega⟩
                          have hval : i.val + 15760 = n := by change n - 15760 + 15760 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 15760)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_15760_15779 i hlen'
                        ·
                          let i : Fin 20 := ⟨n - 15780, by omega⟩
                          have hval : i.val + 15780 = n := by change n - 15780 + 15780 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 15780)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_15780_15799 i hlen'
                  ·
                    by_cases hcut : n < 15860
                    ·
                      by_cases hcut : n < 15820
                      ·
                        let i : Fin 20 := ⟨n - 15800, by omega⟩
                        have hval : i.val + 15800 = n := by change n - 15800 + 15800 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 15800)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_15800_15819 i hlen'
                      ·
                        by_cases hcut : n < 15840
                        ·
                          let i : Fin 20 := ⟨n - 15820, by omega⟩
                          have hval : i.val + 15820 = n := by change n - 15820 + 15820 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 15820)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_15820_15839 i hlen'
                        ·
                          let i : Fin 20 := ⟨n - 15840, by omega⟩
                          have hval : i.val + 15840 = n := by change n - 15840 + 15840 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 15840)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_15840_15859 i hlen'
                    ·
                      by_cases hcut : n < 15880
                      ·
                        let i : Fin 20 := ⟨n - 15860, by omega⟩
                        have hval : i.val + 15860 = n := by change n - 15860 + 15860 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 15860)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_15860_15879 i hlen'
                      ·
                        by_cases hcut : n < 15900
                        ·
                          let i : Fin 20 := ⟨n - 15880, by omega⟩
                          have hval : i.val + 15880 = n := by change n - 15880 + 15880 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 15880)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_15880_15899 i hlen'
                        ·
                          let i : Fin 20 := ⟨n - 15900, by omega⟩
                          have hval : i.val + 15900 = n := by change n - 15900 + 15900 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 15900)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_15900_15919 i hlen'
                ·
                  by_cases hcut : n < 16040
                  ·
                    by_cases hcut : n < 15980
                    ·
                      by_cases hcut : n < 15940
                      ·
                        let i : Fin 20 := ⟨n - 15920, by omega⟩
                        have hval : i.val + 15920 = n := by change n - 15920 + 15920 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 15920)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_15920_15939 i hlen'
                      ·
                        by_cases hcut : n < 15960
                        ·
                          let i : Fin 20 := ⟨n - 15940, by omega⟩
                          have hval : i.val + 15940 = n := by change n - 15940 + 15940 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 15940)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_15940_15959 i hlen'
                        ·
                          let i : Fin 20 := ⟨n - 15960, by omega⟩
                          have hval : i.val + 15960 = n := by change n - 15960 + 15960 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 15960)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_15960_15979 i hlen'
                    ·
                      by_cases hcut : n < 16000
                      ·
                        let i : Fin 20 := ⟨n - 15980, by omega⟩
                        have hval : i.val + 15980 = n := by change n - 15980 + 15980 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 15980)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_15980_15999 i hlen'
                      ·
                        by_cases hcut : n < 16020
                        ·
                          let i : Fin 20 := ⟨n - 16000, by omega⟩
                          have hval : i.val + 16000 = n := by change n - 16000 + 16000 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 16000)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_16000_16019 i hlen'
                        ·
                          let i : Fin 20 := ⟨n - 16020, by omega⟩
                          have hval : i.val + 16020 = n := by change n - 16020 + 16020 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 16020)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_16020_16039 i hlen'
                  ·
                    by_cases hcut : n < 16100
                    ·
                      by_cases hcut : n < 16060
                      ·
                        let i : Fin 20 := ⟨n - 16040, by omega⟩
                        have hval : i.val + 16040 = n := by change n - 16040 + 16040 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 16040)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_16040_16059 i hlen'
                      ·
                        by_cases hcut : n < 16080
                        ·
                          let i : Fin 20 := ⟨n - 16060, by omega⟩
                          have hval : i.val + 16060 = n := by change n - 16060 + 16060 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 16060)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_16060_16079 i hlen'
                        ·
                          let i : Fin 20 := ⟨n - 16080, by omega⟩
                          have hval : i.val + 16080 = n := by change n - 16080 + 16080 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 16080)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_16080_16099 i hlen'
                    ·
                      by_cases hcut : n < 16120
                      ·
                        let i : Fin 20 := ⟨n - 16100, by omega⟩
                        have hval : i.val + 16100 = n := by change n - 16100 + 16100 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 16100)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_16100_16119 i hlen'
                      ·
                        by_cases hcut : n < 16140
                        ·
                          let i : Fin 20 := ⟨n - 16120, by omega⟩
                          have hval : i.val + 16120 = n := by change n - 16120 + 16120 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 16120)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_16120_16139 i hlen'
                        ·
                          let i : Fin 20 := ⟨n - 16140, by omega⟩
                          have hval : i.val + 16140 = n := by change n - 16140 + 16140 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 16140)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_16140_16159 i hlen'
          ·
            by_cases hcut : n < 17060
            ·
              by_cases hcut : n < 16600
              ·
                by_cases hcut : n < 16380
                ·
                  by_cases hcut : n < 16260
                  ·
                    by_cases hcut : n < 16200
                    ·
                      by_cases hcut : n < 16180
                      ·
                        let i : Fin 20 := ⟨n - 16160, by omega⟩
                        have hval : i.val + 16160 = n := by change n - 16160 + 16160 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 16160)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_16160_16179 i hlen'
                      ·
                        let i : Fin 20 := ⟨n - 16180, by omega⟩
                        have hval : i.val + 16180 = n := by change n - 16180 + 16180 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 16180)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_16180_16199 i hlen'
                    ·
                      by_cases hcut : n < 16220
                      ·
                        let i : Fin 20 := ⟨n - 16200, by omega⟩
                        have hval : i.val + 16200 = n := by change n - 16200 + 16200 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 16200)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_16200_16219 i hlen'
                      ·
                        by_cases hcut : n < 16240
                        ·
                          let i : Fin 20 := ⟨n - 16220, by omega⟩
                          have hval : i.val + 16220 = n := by change n - 16220 + 16220 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 16220)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_16220_16239 i hlen'
                        ·
                          let i : Fin 20 := ⟨n - 16240, by omega⟩
                          have hval : i.val + 16240 = n := by change n - 16240 + 16240 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 16240)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_16240_16259 i hlen'
                  ·
                    by_cases hcut : n < 16320
                    ·
                      by_cases hcut : n < 16280
                      ·
                        let i : Fin 20 := ⟨n - 16260, by omega⟩
                        have hval : i.val + 16260 = n := by change n - 16260 + 16260 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 16260)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_16260_16279 i hlen'
                      ·
                        by_cases hcut : n < 16300
                        ·
                          let i : Fin 20 := ⟨n - 16280, by omega⟩
                          have hval : i.val + 16280 = n := by change n - 16280 + 16280 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 16280)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_16280_16299 i hlen'
                        ·
                          let i : Fin 20 := ⟨n - 16300, by omega⟩
                          have hval : i.val + 16300 = n := by change n - 16300 + 16300 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 16300)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_16300_16319 i hlen'
                    ·
                      by_cases hcut : n < 16340
                      ·
                        let i : Fin 20 := ⟨n - 16320, by omega⟩
                        have hval : i.val + 16320 = n := by change n - 16320 + 16320 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 16320)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_16320_16339 i hlen'
                      ·
                        by_cases hcut : n < 16360
                        ·
                          let i : Fin 20 := ⟨n - 16340, by omega⟩
                          have hval : i.val + 16340 = n := by change n - 16340 + 16340 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 16340)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_16340_16359 i hlen'
                        ·
                          let i : Fin 20 := ⟨n - 16360, by omega⟩
                          have hval : i.val + 16360 = n := by change n - 16360 + 16360 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 16360)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_16360_16379 i hlen'
                ·
                  by_cases hcut : n < 16480
                  ·
                    by_cases hcut : n < 16420
                    ·
                      by_cases hcut : n < 16400
                      ·
                        let i : Fin 20 := ⟨n - 16380, by omega⟩
                        have hval : i.val + 16380 = n := by change n - 16380 + 16380 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 16380)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_16380_16399 i hlen'
                      ·
                        let i : Fin 20 := ⟨n - 16400, by omega⟩
                        have hval : i.val + 16400 = n := by change n - 16400 + 16400 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 16400)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_16400_16419 i hlen'
                    ·
                      by_cases hcut : n < 16440
                      ·
                        let i : Fin 20 := ⟨n - 16420, by omega⟩
                        have hval : i.val + 16420 = n := by change n - 16420 + 16420 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 16420)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_16420_16439 i hlen'
                      ·
                        by_cases hcut : n < 16460
                        ·
                          let i : Fin 20 := ⟨n - 16440, by omega⟩
                          have hval : i.val + 16440 = n := by change n - 16440 + 16440 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 16440)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_16440_16459 i hlen'
                        ·
                          let i : Fin 20 := ⟨n - 16460, by omega⟩
                          have hval : i.val + 16460 = n := by change n - 16460 + 16460 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 16460)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_16460_16479 i hlen'
                  ·
                    by_cases hcut : n < 16540
                    ·
                      by_cases hcut : n < 16500
                      ·
                        let i : Fin 20 := ⟨n - 16480, by omega⟩
                        have hval : i.val + 16480 = n := by change n - 16480 + 16480 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 16480)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_16480_16499 i hlen'
                      ·
                        by_cases hcut : n < 16520
                        ·
                          let i : Fin 20 := ⟨n - 16500, by omega⟩
                          have hval : i.val + 16500 = n := by change n - 16500 + 16500 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 16500)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_16500_16519 i hlen'
                        ·
                          let i : Fin 20 := ⟨n - 16520, by omega⟩
                          have hval : i.val + 16520 = n := by change n - 16520 + 16520 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 16520)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_16520_16539 i hlen'
                    ·
                      by_cases hcut : n < 16560
                      ·
                        let i : Fin 20 := ⟨n - 16540, by omega⟩
                        have hval : i.val + 16540 = n := by change n - 16540 + 16540 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 16540)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_16540_16559 i hlen'
                      ·
                        by_cases hcut : n < 16580
                        ·
                          let i : Fin 20 := ⟨n - 16560, by omega⟩
                          have hval : i.val + 16560 = n := by change n - 16560 + 16560 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 16560)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_16560_16579 i hlen'
                        ·
                          let i : Fin 20 := ⟨n - 16580, by omega⟩
                          have hval : i.val + 16580 = n := by change n - 16580 + 16580 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 16580)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_16580_16599 i hlen'
              ·
                by_cases hcut : n < 16820
                ·
                  by_cases hcut : n < 16700
                  ·
                    by_cases hcut : n < 16640
                    ·
                      by_cases hcut : n < 16620
                      ·
                        let i : Fin 20 := ⟨n - 16600, by omega⟩
                        have hval : i.val + 16600 = n := by change n - 16600 + 16600 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 16600)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_16600_16619 i hlen'
                      ·
                        let i : Fin 20 := ⟨n - 16620, by omega⟩
                        have hval : i.val + 16620 = n := by change n - 16620 + 16620 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 16620)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_16620_16639 i hlen'
                    ·
                      by_cases hcut : n < 16660
                      ·
                        let i : Fin 20 := ⟨n - 16640, by omega⟩
                        have hval : i.val + 16640 = n := by change n - 16640 + 16640 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 16640)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_16640_16659 i hlen'
                      ·
                        by_cases hcut : n < 16680
                        ·
                          let i : Fin 20 := ⟨n - 16660, by omega⟩
                          have hval : i.val + 16660 = n := by change n - 16660 + 16660 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 16660)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_16660_16679 i hlen'
                        ·
                          let i : Fin 20 := ⟨n - 16680, by omega⟩
                          have hval : i.val + 16680 = n := by change n - 16680 + 16680 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 16680)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_16680_16699 i hlen'
                  ·
                    by_cases hcut : n < 16760
                    ·
                      by_cases hcut : n < 16720
                      ·
                        let i : Fin 20 := ⟨n - 16700, by omega⟩
                        have hval : i.val + 16700 = n := by change n - 16700 + 16700 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 16700)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_16700_16719 i hlen'
                      ·
                        by_cases hcut : n < 16740
                        ·
                          let i : Fin 20 := ⟨n - 16720, by omega⟩
                          have hval : i.val + 16720 = n := by change n - 16720 + 16720 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 16720)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_16720_16739 i hlen'
                        ·
                          let i : Fin 20 := ⟨n - 16740, by omega⟩
                          have hval : i.val + 16740 = n := by change n - 16740 + 16740 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 16740)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_16740_16759 i hlen'
                    ·
                      by_cases hcut : n < 16780
                      ·
                        let i : Fin 20 := ⟨n - 16760, by omega⟩
                        have hval : i.val + 16760 = n := by change n - 16760 + 16760 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 16760)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_16760_16779 i hlen'
                      ·
                        by_cases hcut : n < 16800
                        ·
                          let i : Fin 20 := ⟨n - 16780, by omega⟩
                          have hval : i.val + 16780 = n := by change n - 16780 + 16780 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 16780)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_16780_16799 i hlen'
                        ·
                          let i : Fin 20 := ⟨n - 16800, by omega⟩
                          have hval : i.val + 16800 = n := by change n - 16800 + 16800 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 16800)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_16800_16819 i hlen'
                ·
                  by_cases hcut : n < 16940
                  ·
                    by_cases hcut : n < 16880
                    ·
                      by_cases hcut : n < 16840
                      ·
                        let i : Fin 20 := ⟨n - 16820, by omega⟩
                        have hval : i.val + 16820 = n := by change n - 16820 + 16820 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 16820)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_16820_16839 i hlen'
                      ·
                        by_cases hcut : n < 16860
                        ·
                          let i : Fin 20 := ⟨n - 16840, by omega⟩
                          have hval : i.val + 16840 = n := by change n - 16840 + 16840 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 16840)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_16840_16859 i hlen'
                        ·
                          let i : Fin 20 := ⟨n - 16860, by omega⟩
                          have hval : i.val + 16860 = n := by change n - 16860 + 16860 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 16860)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_16860_16879 i hlen'
                    ·
                      by_cases hcut : n < 16900
                      ·
                        let i : Fin 20 := ⟨n - 16880, by omega⟩
                        have hval : i.val + 16880 = n := by change n - 16880 + 16880 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 16880)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_16880_16899 i hlen'
                      ·
                        by_cases hcut : n < 16920
                        ·
                          let i : Fin 20 := ⟨n - 16900, by omega⟩
                          have hval : i.val + 16900 = n := by change n - 16900 + 16900 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 16900)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_16900_16919 i hlen'
                        ·
                          let i : Fin 20 := ⟨n - 16920, by omega⟩
                          have hval : i.val + 16920 = n := by change n - 16920 + 16920 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 16920)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_16920_16939 i hlen'
                  ·
                    by_cases hcut : n < 17000
                    ·
                      by_cases hcut : n < 16960
                      ·
                        let i : Fin 20 := ⟨n - 16940, by omega⟩
                        have hval : i.val + 16940 = n := by change n - 16940 + 16940 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 16940)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_16940_16959 i hlen'
                      ·
                        by_cases hcut : n < 16980
                        ·
                          let i : Fin 20 := ⟨n - 16960, by omega⟩
                          have hval : i.val + 16960 = n := by change n - 16960 + 16960 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 16960)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_16960_16979 i hlen'
                        ·
                          let i : Fin 20 := ⟨n - 16980, by omega⟩
                          have hval : i.val + 16980 = n := by change n - 16980 + 16980 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 16980)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_16980_16999 i hlen'
                    ·
                      by_cases hcut : n < 17020
                      ·
                        let i : Fin 20 := ⟨n - 17000, by omega⟩
                        have hval : i.val + 17000 = n := by change n - 17000 + 17000 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 17000)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_17000_17019 i hlen'
                      ·
                        by_cases hcut : n < 17040
                        ·
                          let i : Fin 20 := ⟨n - 17020, by omega⟩
                          have hval : i.val + 17020 = n := by change n - 17020 + 17020 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 17020)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_17020_17039 i hlen'
                        ·
                          let i : Fin 20 := ⟨n - 17040, by omega⟩
                          have hval : i.val + 17040 = n := by change n - 17040 + 17040 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 17040)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_17040_17059 i hlen'
            ·
              by_cases hcut : n < 17500
              ·
                by_cases hcut : n < 17280
                ·
                  by_cases hcut : n < 17160
                  ·
                    by_cases hcut : n < 17100
                    ·
                      by_cases hcut : n < 17080
                      ·
                        let i : Fin 20 := ⟨n - 17060, by omega⟩
                        have hval : i.val + 17060 = n := by change n - 17060 + 17060 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 17060)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_17060_17079 i hlen'
                      ·
                        let i : Fin 20 := ⟨n - 17080, by omega⟩
                        have hval : i.val + 17080 = n := by change n - 17080 + 17080 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 17080)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_17080_17099 i hlen'
                    ·
                      by_cases hcut : n < 17120
                      ·
                        let i : Fin 20 := ⟨n - 17100, by omega⟩
                        have hval : i.val + 17100 = n := by change n - 17100 + 17100 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 17100)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_17100_17119 i hlen'
                      ·
                        by_cases hcut : n < 17140
                        ·
                          let i : Fin 20 := ⟨n - 17120, by omega⟩
                          have hval : i.val + 17120 = n := by change n - 17120 + 17120 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 17120)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_17120_17139 i hlen'
                        ·
                          let i : Fin 20 := ⟨n - 17140, by omega⟩
                          have hval : i.val + 17140 = n := by change n - 17140 + 17140 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 17140)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_17140_17159 i hlen'
                  ·
                    by_cases hcut : n < 17220
                    ·
                      by_cases hcut : n < 17180
                      ·
                        let i : Fin 20 := ⟨n - 17160, by omega⟩
                        have hval : i.val + 17160 = n := by change n - 17160 + 17160 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 17160)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_17160_17179 i hlen'
                      ·
                        by_cases hcut : n < 17200
                        ·
                          let i : Fin 20 := ⟨n - 17180, by omega⟩
                          have hval : i.val + 17180 = n := by change n - 17180 + 17180 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 17180)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_17180_17199 i hlen'
                        ·
                          let i : Fin 20 := ⟨n - 17200, by omega⟩
                          have hval : i.val + 17200 = n := by change n - 17200 + 17200 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 17200)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_17200_17219 i hlen'
                    ·
                      by_cases hcut : n < 17240
                      ·
                        let i : Fin 20 := ⟨n - 17220, by omega⟩
                        have hval : i.val + 17220 = n := by change n - 17220 + 17220 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 17220)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_17220_17239 i hlen'
                      ·
                        by_cases hcut : n < 17260
                        ·
                          let i : Fin 20 := ⟨n - 17240, by omega⟩
                          have hval : i.val + 17240 = n := by change n - 17240 + 17240 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 17240)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_17240_17259 i hlen'
                        ·
                          let i : Fin 20 := ⟨n - 17260, by omega⟩
                          have hval : i.val + 17260 = n := by change n - 17260 + 17260 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 17260)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_17260_17279 i hlen'
                ·
                  by_cases hcut : n < 17380
                  ·
                    by_cases hcut : n < 17320
                    ·
                      by_cases hcut : n < 17300
                      ·
                        let i : Fin 20 := ⟨n - 17280, by omega⟩
                        have hval : i.val + 17280 = n := by change n - 17280 + 17280 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 17280)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_17280_17299 i hlen'
                      ·
                        let i : Fin 20 := ⟨n - 17300, by omega⟩
                        have hval : i.val + 17300 = n := by change n - 17300 + 17300 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 17300)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_17300_17319 i hlen'
                    ·
                      by_cases hcut : n < 17340
                      ·
                        let i : Fin 20 := ⟨n - 17320, by omega⟩
                        have hval : i.val + 17320 = n := by change n - 17320 + 17320 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 17320)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_17320_17339 i hlen'
                      ·
                        by_cases hcut : n < 17360
                        ·
                          let i : Fin 20 := ⟨n - 17340, by omega⟩
                          have hval : i.val + 17340 = n := by change n - 17340 + 17340 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 17340)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_17340_17359 i hlen'
                        ·
                          let i : Fin 20 := ⟨n - 17360, by omega⟩
                          have hval : i.val + 17360 = n := by change n - 17360 + 17360 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 17360)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_17360_17379 i hlen'
                  ·
                    by_cases hcut : n < 17440
                    ·
                      by_cases hcut : n < 17400
                      ·
                        let i : Fin 20 := ⟨n - 17380, by omega⟩
                        have hval : i.val + 17380 = n := by change n - 17380 + 17380 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 17380)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_17380_17399 i hlen'
                      ·
                        by_cases hcut : n < 17420
                        ·
                          let i : Fin 20 := ⟨n - 17400, by omega⟩
                          have hval : i.val + 17400 = n := by change n - 17400 + 17400 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 17400)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_17400_17419 i hlen'
                        ·
                          let i : Fin 20 := ⟨n - 17420, by omega⟩
                          have hval : i.val + 17420 = n := by change n - 17420 + 17420 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 17420)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_17420_17439 i hlen'
                    ·
                      by_cases hcut : n < 17460
                      ·
                        let i : Fin 20 := ⟨n - 17440, by omega⟩
                        have hval : i.val + 17440 = n := by change n - 17440 + 17440 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 17440)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_17440_17459 i hlen'
                      ·
                        by_cases hcut : n < 17480
                        ·
                          let i : Fin 20 := ⟨n - 17460, by omega⟩
                          have hval : i.val + 17460 = n := by change n - 17460 + 17460 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 17460)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_17460_17479 i hlen'
                        ·
                          let i : Fin 20 := ⟨n - 17480, by omega⟩
                          have hval : i.val + 17480 = n := by change n - 17480 + 17480 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 17480)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_17480_17499 i hlen'
              ·
                by_cases hcut : n < 17720
                ·
                  by_cases hcut : n < 17600
                  ·
                    by_cases hcut : n < 17540
                    ·
                      by_cases hcut : n < 17520
                      ·
                        let i : Fin 20 := ⟨n - 17500, by omega⟩
                        have hval : i.val + 17500 = n := by change n - 17500 + 17500 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 17500)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_17500_17519 i hlen'
                      ·
                        let i : Fin 20 := ⟨n - 17520, by omega⟩
                        have hval : i.val + 17520 = n := by change n - 17520 + 17520 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 17520)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_17520_17539 i hlen'
                    ·
                      by_cases hcut : n < 17560
                      ·
                        let i : Fin 20 := ⟨n - 17540, by omega⟩
                        have hval : i.val + 17540 = n := by change n - 17540 + 17540 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 17540)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_17540_17559 i hlen'
                      ·
                        by_cases hcut : n < 17580
                        ·
                          let i : Fin 20 := ⟨n - 17560, by omega⟩
                          have hval : i.val + 17560 = n := by change n - 17560 + 17560 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 17560)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_17560_17579 i hlen'
                        ·
                          let i : Fin 20 := ⟨n - 17580, by omega⟩
                          have hval : i.val + 17580 = n := by change n - 17580 + 17580 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 17580)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_17580_17599 i hlen'
                  ·
                    by_cases hcut : n < 17660
                    ·
                      by_cases hcut : n < 17620
                      ·
                        let i : Fin 20 := ⟨n - 17600, by omega⟩
                        have hval : i.val + 17600 = n := by change n - 17600 + 17600 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 17600)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_17600_17619 i hlen'
                      ·
                        by_cases hcut : n < 17640
                        ·
                          let i : Fin 20 := ⟨n - 17620, by omega⟩
                          have hval : i.val + 17620 = n := by change n - 17620 + 17620 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 17620)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_17620_17639 i hlen'
                        ·
                          let i : Fin 20 := ⟨n - 17640, by omega⟩
                          have hval : i.val + 17640 = n := by change n - 17640 + 17640 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 17640)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_17640_17659 i hlen'
                    ·
                      by_cases hcut : n < 17680
                      ·
                        let i : Fin 20 := ⟨n - 17660, by omega⟩
                        have hval : i.val + 17660 = n := by change n - 17660 + 17660 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 17660)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_17660_17679 i hlen'
                      ·
                        by_cases hcut : n < 17700
                        ·
                          let i : Fin 20 := ⟨n - 17680, by omega⟩
                          have hval : i.val + 17680 = n := by change n - 17680 + 17680 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 17680)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_17680_17699 i hlen'
                        ·
                          let i : Fin 20 := ⟨n - 17700, by omega⟩
                          have hval : i.val + 17700 = n := by change n - 17700 + 17700 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 17700)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_17700_17719 i hlen'
                ·
                  by_cases hcut : n < 17840
                  ·
                    by_cases hcut : n < 17780
                    ·
                      by_cases hcut : n < 17740
                      ·
                        let i : Fin 20 := ⟨n - 17720, by omega⟩
                        have hval : i.val + 17720 = n := by change n - 17720 + 17720 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 17720)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_17720_17739 i hlen'
                      ·
                        by_cases hcut : n < 17760
                        ·
                          let i : Fin 20 := ⟨n - 17740, by omega⟩
                          have hval : i.val + 17740 = n := by change n - 17740 + 17740 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 17740)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_17740_17759 i hlen'
                        ·
                          let i : Fin 20 := ⟨n - 17760, by omega⟩
                          have hval : i.val + 17760 = n := by change n - 17760 + 17760 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 17760)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_17760_17779 i hlen'
                    ·
                      by_cases hcut : n < 17800
                      ·
                        let i : Fin 20 := ⟨n - 17780, by omega⟩
                        have hval : i.val + 17780 = n := by change n - 17780 + 17780 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 17780)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_17780_17799 i hlen'
                      ·
                        by_cases hcut : n < 17820
                        ·
                          let i : Fin 20 := ⟨n - 17800, by omega⟩
                          have hval : i.val + 17800 = n := by change n - 17800 + 17800 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 17800)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_17800_17819 i hlen'
                        ·
                          let i : Fin 20 := ⟨n - 17820, by omega⟩
                          have hval : i.val + 17820 = n := by change n - 17820 + 17820 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 17820)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_17820_17839 i hlen'
                  ·
                    by_cases hcut : n < 17900
                    ·
                      by_cases hcut : n < 17860
                      ·
                        let i : Fin 20 := ⟨n - 17840, by omega⟩
                        have hval : i.val + 17840 = n := by change n - 17840 + 17840 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 17840)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_17840_17859 i hlen'
                      ·
                        by_cases hcut : n < 17880
                        ·
                          let i : Fin 20 := ⟨n - 17860, by omega⟩
                          have hval : i.val + 17860 = n := by change n - 17860 + 17860 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 17860)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_17860_17879 i hlen'
                        ·
                          let i : Fin 20 := ⟨n - 17880, by omega⟩
                          have hval : i.val + 17880 = n := by change n - 17880 + 17880 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 17880)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_17880_17899 i hlen'
                    ·
                      by_cases hcut : n < 17920
                      ·
                        let i : Fin 20 := ⟨n - 17900, by omega⟩
                        have hval : i.val + 17900 = n := by change n - 17900 + 17900 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 17900)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_17900_17919 i hlen'
                      ·
                        by_cases hcut : n < 17940
                        ·
                          let i : Fin 20 := ⟨n - 17920, by omega⟩
                          have hval : i.val + 17920 = n := by change n - 17920 + 17920 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 17920)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_17920_17939 i hlen'
                        ·
                          let i : Fin 20 := ⟨n - 17940, by omega⟩
                          have hval : i.val + 17940 = n := by change n - 17940 + 17940 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 17940)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_17940_17959 i hlen'
        ·
          by_cases hcut : n < 19760
          ·
            by_cases hcut : n < 18860
            ·
              by_cases hcut : n < 18400
              ·
                by_cases hcut : n < 18180
                ·
                  by_cases hcut : n < 18060
                  ·
                    by_cases hcut : n < 18000
                    ·
                      by_cases hcut : n < 17980
                      ·
                        let i : Fin 20 := ⟨n - 17960, by omega⟩
                        have hval : i.val + 17960 = n := by change n - 17960 + 17960 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 17960)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_17960_17979 i hlen'
                      ·
                        let i : Fin 20 := ⟨n - 17980, by omega⟩
                        have hval : i.val + 17980 = n := by change n - 17980 + 17980 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 17980)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_17980_17999 i hlen'
                    ·
                      by_cases hcut : n < 18020
                      ·
                        let i : Fin 20 := ⟨n - 18000, by omega⟩
                        have hval : i.val + 18000 = n := by change n - 18000 + 18000 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 18000)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_18000_18019 i hlen'
                      ·
                        by_cases hcut : n < 18040
                        ·
                          let i : Fin 20 := ⟨n - 18020, by omega⟩
                          have hval : i.val + 18020 = n := by change n - 18020 + 18020 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 18020)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_18020_18039 i hlen'
                        ·
                          let i : Fin 20 := ⟨n - 18040, by omega⟩
                          have hval : i.val + 18040 = n := by change n - 18040 + 18040 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 18040)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_18040_18059 i hlen'
                  ·
                    by_cases hcut : n < 18120
                    ·
                      by_cases hcut : n < 18080
                      ·
                        let i : Fin 20 := ⟨n - 18060, by omega⟩
                        have hval : i.val + 18060 = n := by change n - 18060 + 18060 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 18060)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_18060_18079 i hlen'
                      ·
                        by_cases hcut : n < 18100
                        ·
                          let i : Fin 20 := ⟨n - 18080, by omega⟩
                          have hval : i.val + 18080 = n := by change n - 18080 + 18080 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 18080)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_18080_18099 i hlen'
                        ·
                          let i : Fin 20 := ⟨n - 18100, by omega⟩
                          have hval : i.val + 18100 = n := by change n - 18100 + 18100 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 18100)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_18100_18119 i hlen'
                    ·
                      by_cases hcut : n < 18140
                      ·
                        let i : Fin 20 := ⟨n - 18120, by omega⟩
                        have hval : i.val + 18120 = n := by change n - 18120 + 18120 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 18120)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_18120_18139 i hlen'
                      ·
                        by_cases hcut : n < 18160
                        ·
                          let i : Fin 20 := ⟨n - 18140, by omega⟩
                          have hval : i.val + 18140 = n := by change n - 18140 + 18140 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 18140)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_18140_18159 i hlen'
                        ·
                          let i : Fin 20 := ⟨n - 18160, by omega⟩
                          have hval : i.val + 18160 = n := by change n - 18160 + 18160 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 18160)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_18160_18179 i hlen'
                ·
                  by_cases hcut : n < 18280
                  ·
                    by_cases hcut : n < 18220
                    ·
                      by_cases hcut : n < 18200
                      ·
                        let i : Fin 20 := ⟨n - 18180, by omega⟩
                        have hval : i.val + 18180 = n := by change n - 18180 + 18180 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 18180)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_18180_18199 i hlen'
                      ·
                        let i : Fin 20 := ⟨n - 18200, by omega⟩
                        have hval : i.val + 18200 = n := by change n - 18200 + 18200 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 18200)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_18200_18219 i hlen'
                    ·
                      by_cases hcut : n < 18240
                      ·
                        let i : Fin 20 := ⟨n - 18220, by omega⟩
                        have hval : i.val + 18220 = n := by change n - 18220 + 18220 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 18220)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_18220_18239 i hlen'
                      ·
                        by_cases hcut : n < 18260
                        ·
                          let i : Fin 20 := ⟨n - 18240, by omega⟩
                          have hval : i.val + 18240 = n := by change n - 18240 + 18240 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 18240)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_18240_18259 i hlen'
                        ·
                          let i : Fin 20 := ⟨n - 18260, by omega⟩
                          have hval : i.val + 18260 = n := by change n - 18260 + 18260 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 18260)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_18260_18279 i hlen'
                  ·
                    by_cases hcut : n < 18340
                    ·
                      by_cases hcut : n < 18300
                      ·
                        let i : Fin 20 := ⟨n - 18280, by omega⟩
                        have hval : i.val + 18280 = n := by change n - 18280 + 18280 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 18280)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_18280_18299 i hlen'
                      ·
                        by_cases hcut : n < 18320
                        ·
                          let i : Fin 20 := ⟨n - 18300, by omega⟩
                          have hval : i.val + 18300 = n := by change n - 18300 + 18300 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 18300)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_18300_18319 i hlen'
                        ·
                          let i : Fin 20 := ⟨n - 18320, by omega⟩
                          have hval : i.val + 18320 = n := by change n - 18320 + 18320 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 18320)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_18320_18339 i hlen'
                    ·
                      by_cases hcut : n < 18360
                      ·
                        let i : Fin 20 := ⟨n - 18340, by omega⟩
                        have hval : i.val + 18340 = n := by change n - 18340 + 18340 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 18340)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_18340_18359 i hlen'
                      ·
                        by_cases hcut : n < 18380
                        ·
                          let i : Fin 20 := ⟨n - 18360, by omega⟩
                          have hval : i.val + 18360 = n := by change n - 18360 + 18360 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 18360)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_18360_18379 i hlen'
                        ·
                          let i : Fin 20 := ⟨n - 18380, by omega⟩
                          have hval : i.val + 18380 = n := by change n - 18380 + 18380 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 18380)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_18380_18399 i hlen'
              ·
                by_cases hcut : n < 18620
                ·
                  by_cases hcut : n < 18500
                  ·
                    by_cases hcut : n < 18440
                    ·
                      by_cases hcut : n < 18420
                      ·
                        let i : Fin 20 := ⟨n - 18400, by omega⟩
                        have hval : i.val + 18400 = n := by change n - 18400 + 18400 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 18400)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_18400_18419 i hlen'
                      ·
                        let i : Fin 20 := ⟨n - 18420, by omega⟩
                        have hval : i.val + 18420 = n := by change n - 18420 + 18420 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 18420)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_18420_18439 i hlen'
                    ·
                      by_cases hcut : n < 18460
                      ·
                        let i : Fin 20 := ⟨n - 18440, by omega⟩
                        have hval : i.val + 18440 = n := by change n - 18440 + 18440 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 18440)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_18440_18459 i hlen'
                      ·
                        by_cases hcut : n < 18480
                        ·
                          let i : Fin 20 := ⟨n - 18460, by omega⟩
                          have hval : i.val + 18460 = n := by change n - 18460 + 18460 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 18460)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_18460_18479 i hlen'
                        ·
                          let i : Fin 20 := ⟨n - 18480, by omega⟩
                          have hval : i.val + 18480 = n := by change n - 18480 + 18480 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 18480)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_18480_18499 i hlen'
                  ·
                    by_cases hcut : n < 18560
                    ·
                      by_cases hcut : n < 18520
                      ·
                        let i : Fin 20 := ⟨n - 18500, by omega⟩
                        have hval : i.val + 18500 = n := by change n - 18500 + 18500 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 18500)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_18500_18519 i hlen'
                      ·
                        by_cases hcut : n < 18540
                        ·
                          let i : Fin 20 := ⟨n - 18520, by omega⟩
                          have hval : i.val + 18520 = n := by change n - 18520 + 18520 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 18520)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_18520_18539 i hlen'
                        ·
                          let i : Fin 20 := ⟨n - 18540, by omega⟩
                          have hval : i.val + 18540 = n := by change n - 18540 + 18540 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 18540)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_18540_18559 i hlen'
                    ·
                      by_cases hcut : n < 18580
                      ·
                        let i : Fin 20 := ⟨n - 18560, by omega⟩
                        have hval : i.val + 18560 = n := by change n - 18560 + 18560 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 18560)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_18560_18579 i hlen'
                      ·
                        by_cases hcut : n < 18600
                        ·
                          let i : Fin 20 := ⟨n - 18580, by omega⟩
                          have hval : i.val + 18580 = n := by change n - 18580 + 18580 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 18580)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_18580_18599 i hlen'
                        ·
                          let i : Fin 20 := ⟨n - 18600, by omega⟩
                          have hval : i.val + 18600 = n := by change n - 18600 + 18600 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 18600)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_18600_18619 i hlen'
                ·
                  by_cases hcut : n < 18740
                  ·
                    by_cases hcut : n < 18680
                    ·
                      by_cases hcut : n < 18640
                      ·
                        let i : Fin 20 := ⟨n - 18620, by omega⟩
                        have hval : i.val + 18620 = n := by change n - 18620 + 18620 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 18620)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_18620_18639 i hlen'
                      ·
                        by_cases hcut : n < 18660
                        ·
                          let i : Fin 20 := ⟨n - 18640, by omega⟩
                          have hval : i.val + 18640 = n := by change n - 18640 + 18640 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 18640)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_18640_18659 i hlen'
                        ·
                          let i : Fin 20 := ⟨n - 18660, by omega⟩
                          have hval : i.val + 18660 = n := by change n - 18660 + 18660 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 18660)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_18660_18679 i hlen'
                    ·
                      by_cases hcut : n < 18700
                      ·
                        let i : Fin 20 := ⟨n - 18680, by omega⟩
                        have hval : i.val + 18680 = n := by change n - 18680 + 18680 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 18680)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_18680_18699 i hlen'
                      ·
                        by_cases hcut : n < 18720
                        ·
                          let i : Fin 20 := ⟨n - 18700, by omega⟩
                          have hval : i.val + 18700 = n := by change n - 18700 + 18700 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 18700)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_18700_18719 i hlen'
                        ·
                          let i : Fin 20 := ⟨n - 18720, by omega⟩
                          have hval : i.val + 18720 = n := by change n - 18720 + 18720 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 18720)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_18720_18739 i hlen'
                  ·
                    by_cases hcut : n < 18800
                    ·
                      by_cases hcut : n < 18760
                      ·
                        let i : Fin 20 := ⟨n - 18740, by omega⟩
                        have hval : i.val + 18740 = n := by change n - 18740 + 18740 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 18740)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_18740_18759 i hlen'
                      ·
                        by_cases hcut : n < 18780
                        ·
                          let i : Fin 20 := ⟨n - 18760, by omega⟩
                          have hval : i.val + 18760 = n := by change n - 18760 + 18760 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 18760)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_18760_18779 i hlen'
                        ·
                          let i : Fin 20 := ⟨n - 18780, by omega⟩
                          have hval : i.val + 18780 = n := by change n - 18780 + 18780 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 18780)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_18780_18799 i hlen'
                    ·
                      by_cases hcut : n < 18820
                      ·
                        let i : Fin 20 := ⟨n - 18800, by omega⟩
                        have hval : i.val + 18800 = n := by change n - 18800 + 18800 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 18800)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_18800_18819 i hlen'
                      ·
                        by_cases hcut : n < 18840
                        ·
                          let i : Fin 20 := ⟨n - 18820, by omega⟩
                          have hval : i.val + 18820 = n := by change n - 18820 + 18820 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 18820)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_18820_18839 i hlen'
                        ·
                          let i : Fin 20 := ⟨n - 18840, by omega⟩
                          have hval : i.val + 18840 = n := by change n - 18840 + 18840 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 18840)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_18840_18859 i hlen'
            ·
              by_cases hcut : n < 19300
              ·
                by_cases hcut : n < 19080
                ·
                  by_cases hcut : n < 18960
                  ·
                    by_cases hcut : n < 18900
                    ·
                      by_cases hcut : n < 18880
                      ·
                        let i : Fin 20 := ⟨n - 18860, by omega⟩
                        have hval : i.val + 18860 = n := by change n - 18860 + 18860 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 18860)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_18860_18879 i hlen'
                      ·
                        let i : Fin 20 := ⟨n - 18880, by omega⟩
                        have hval : i.val + 18880 = n := by change n - 18880 + 18880 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 18880)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_18880_18899 i hlen'
                    ·
                      by_cases hcut : n < 18920
                      ·
                        let i : Fin 20 := ⟨n - 18900, by omega⟩
                        have hval : i.val + 18900 = n := by change n - 18900 + 18900 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 18900)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_18900_18919 i hlen'
                      ·
                        by_cases hcut : n < 18940
                        ·
                          let i : Fin 20 := ⟨n - 18920, by omega⟩
                          have hval : i.val + 18920 = n := by change n - 18920 + 18920 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 18920)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_18920_18939 i hlen'
                        ·
                          let i : Fin 20 := ⟨n - 18940, by omega⟩
                          have hval : i.val + 18940 = n := by change n - 18940 + 18940 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 18940)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_18940_18959 i hlen'
                  ·
                    by_cases hcut : n < 19020
                    ·
                      by_cases hcut : n < 18980
                      ·
                        let i : Fin 20 := ⟨n - 18960, by omega⟩
                        have hval : i.val + 18960 = n := by change n - 18960 + 18960 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 18960)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_18960_18979 i hlen'
                      ·
                        by_cases hcut : n < 19000
                        ·
                          let i : Fin 20 := ⟨n - 18980, by omega⟩
                          have hval : i.val + 18980 = n := by change n - 18980 + 18980 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 18980)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_18980_18999 i hlen'
                        ·
                          let i : Fin 20 := ⟨n - 19000, by omega⟩
                          have hval : i.val + 19000 = n := by change n - 19000 + 19000 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 19000)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_19000_19019 i hlen'
                    ·
                      by_cases hcut : n < 19040
                      ·
                        let i : Fin 20 := ⟨n - 19020, by omega⟩
                        have hval : i.val + 19020 = n := by change n - 19020 + 19020 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 19020)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_19020_19039 i hlen'
                      ·
                        by_cases hcut : n < 19060
                        ·
                          let i : Fin 20 := ⟨n - 19040, by omega⟩
                          have hval : i.val + 19040 = n := by change n - 19040 + 19040 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 19040)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_19040_19059 i hlen'
                        ·
                          let i : Fin 20 := ⟨n - 19060, by omega⟩
                          have hval : i.val + 19060 = n := by change n - 19060 + 19060 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 19060)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_19060_19079 i hlen'
                ·
                  by_cases hcut : n < 19180
                  ·
                    by_cases hcut : n < 19120
                    ·
                      by_cases hcut : n < 19100
                      ·
                        let i : Fin 20 := ⟨n - 19080, by omega⟩
                        have hval : i.val + 19080 = n := by change n - 19080 + 19080 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 19080)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_19080_19099 i hlen'
                      ·
                        let i : Fin 20 := ⟨n - 19100, by omega⟩
                        have hval : i.val + 19100 = n := by change n - 19100 + 19100 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 19100)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_19100_19119 i hlen'
                    ·
                      by_cases hcut : n < 19140
                      ·
                        let i : Fin 20 := ⟨n - 19120, by omega⟩
                        have hval : i.val + 19120 = n := by change n - 19120 + 19120 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 19120)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_19120_19139 i hlen'
                      ·
                        by_cases hcut : n < 19160
                        ·
                          let i : Fin 20 := ⟨n - 19140, by omega⟩
                          have hval : i.val + 19140 = n := by change n - 19140 + 19140 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 19140)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_19140_19159 i hlen'
                        ·
                          let i : Fin 20 := ⟨n - 19160, by omega⟩
                          have hval : i.val + 19160 = n := by change n - 19160 + 19160 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 19160)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_19160_19179 i hlen'
                  ·
                    by_cases hcut : n < 19240
                    ·
                      by_cases hcut : n < 19200
                      ·
                        let i : Fin 20 := ⟨n - 19180, by omega⟩
                        have hval : i.val + 19180 = n := by change n - 19180 + 19180 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 19180)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_19180_19199 i hlen'
                      ·
                        by_cases hcut : n < 19220
                        ·
                          let i : Fin 20 := ⟨n - 19200, by omega⟩
                          have hval : i.val + 19200 = n := by change n - 19200 + 19200 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 19200)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_19200_19219 i hlen'
                        ·
                          let i : Fin 20 := ⟨n - 19220, by omega⟩
                          have hval : i.val + 19220 = n := by change n - 19220 + 19220 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 19220)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_19220_19239 i hlen'
                    ·
                      by_cases hcut : n < 19260
                      ·
                        let i : Fin 20 := ⟨n - 19240, by omega⟩
                        have hval : i.val + 19240 = n := by change n - 19240 + 19240 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 19240)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_19240_19259 i hlen'
                      ·
                        by_cases hcut : n < 19280
                        ·
                          let i : Fin 20 := ⟨n - 19260, by omega⟩
                          have hval : i.val + 19260 = n := by change n - 19260 + 19260 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 19260)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_19260_19279 i hlen'
                        ·
                          let i : Fin 20 := ⟨n - 19280, by omega⟩
                          have hval : i.val + 19280 = n := by change n - 19280 + 19280 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 19280)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_19280_19299 i hlen'
              ·
                by_cases hcut : n < 19520
                ·
                  by_cases hcut : n < 19400
                  ·
                    by_cases hcut : n < 19340
                    ·
                      by_cases hcut : n < 19320
                      ·
                        let i : Fin 20 := ⟨n - 19300, by omega⟩
                        have hval : i.val + 19300 = n := by change n - 19300 + 19300 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 19300)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_19300_19319 i hlen'
                      ·
                        let i : Fin 20 := ⟨n - 19320, by omega⟩
                        have hval : i.val + 19320 = n := by change n - 19320 + 19320 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 19320)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_19320_19339 i hlen'
                    ·
                      by_cases hcut : n < 19360
                      ·
                        let i : Fin 20 := ⟨n - 19340, by omega⟩
                        have hval : i.val + 19340 = n := by change n - 19340 + 19340 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 19340)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_19340_19359 i hlen'
                      ·
                        by_cases hcut : n < 19380
                        ·
                          let i : Fin 20 := ⟨n - 19360, by omega⟩
                          have hval : i.val + 19360 = n := by change n - 19360 + 19360 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 19360)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_19360_19379 i hlen'
                        ·
                          let i : Fin 20 := ⟨n - 19380, by omega⟩
                          have hval : i.val + 19380 = n := by change n - 19380 + 19380 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 19380)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_19380_19399 i hlen'
                  ·
                    by_cases hcut : n < 19460
                    ·
                      by_cases hcut : n < 19420
                      ·
                        let i : Fin 20 := ⟨n - 19400, by omega⟩
                        have hval : i.val + 19400 = n := by change n - 19400 + 19400 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 19400)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_19400_19419 i hlen'
                      ·
                        by_cases hcut : n < 19440
                        ·
                          let i : Fin 20 := ⟨n - 19420, by omega⟩
                          have hval : i.val + 19420 = n := by change n - 19420 + 19420 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 19420)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_19420_19439 i hlen'
                        ·
                          let i : Fin 20 := ⟨n - 19440, by omega⟩
                          have hval : i.val + 19440 = n := by change n - 19440 + 19440 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 19440)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_19440_19459 i hlen'
                    ·
                      by_cases hcut : n < 19480
                      ·
                        let i : Fin 20 := ⟨n - 19460, by omega⟩
                        have hval : i.val + 19460 = n := by change n - 19460 + 19460 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 19460)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_19460_19479 i hlen'
                      ·
                        by_cases hcut : n < 19500
                        ·
                          let i : Fin 20 := ⟨n - 19480, by omega⟩
                          have hval : i.val + 19480 = n := by change n - 19480 + 19480 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 19480)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_19480_19499 i hlen'
                        ·
                          let i : Fin 20 := ⟨n - 19500, by omega⟩
                          have hval : i.val + 19500 = n := by change n - 19500 + 19500 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 19500)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_19500_19519 i hlen'
                ·
                  by_cases hcut : n < 19640
                  ·
                    by_cases hcut : n < 19580
                    ·
                      by_cases hcut : n < 19540
                      ·
                        let i : Fin 20 := ⟨n - 19520, by omega⟩
                        have hval : i.val + 19520 = n := by change n - 19520 + 19520 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 19520)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_19520_19539 i hlen'
                      ·
                        by_cases hcut : n < 19560
                        ·
                          let i : Fin 20 := ⟨n - 19540, by omega⟩
                          have hval : i.val + 19540 = n := by change n - 19540 + 19540 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 19540)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_19540_19559 i hlen'
                        ·
                          let i : Fin 20 := ⟨n - 19560, by omega⟩
                          have hval : i.val + 19560 = n := by change n - 19560 + 19560 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 19560)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_19560_19579 i hlen'
                    ·
                      by_cases hcut : n < 19600
                      ·
                        let i : Fin 20 := ⟨n - 19580, by omega⟩
                        have hval : i.val + 19580 = n := by change n - 19580 + 19580 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 19580)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_19580_19599 i hlen'
                      ·
                        by_cases hcut : n < 19620
                        ·
                          let i : Fin 20 := ⟨n - 19600, by omega⟩
                          have hval : i.val + 19600 = n := by change n - 19600 + 19600 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 19600)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_19600_19619 i hlen'
                        ·
                          let i : Fin 20 := ⟨n - 19620, by omega⟩
                          have hval : i.val + 19620 = n := by change n - 19620 + 19620 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 19620)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_19620_19639 i hlen'
                  ·
                    by_cases hcut : n < 19700
                    ·
                      by_cases hcut : n < 19660
                      ·
                        let i : Fin 20 := ⟨n - 19640, by omega⟩
                        have hval : i.val + 19640 = n := by change n - 19640 + 19640 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 19640)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_19640_19659 i hlen'
                      ·
                        by_cases hcut : n < 19680
                        ·
                          let i : Fin 20 := ⟨n - 19660, by omega⟩
                          have hval : i.val + 19660 = n := by change n - 19660 + 19660 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 19660)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_19660_19679 i hlen'
                        ·
                          let i : Fin 20 := ⟨n - 19680, by omega⟩
                          have hval : i.val + 19680 = n := by change n - 19680 + 19680 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 19680)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_19680_19699 i hlen'
                    ·
                      by_cases hcut : n < 19720
                      ·
                        let i : Fin 20 := ⟨n - 19700, by omega⟩
                        have hval : i.val + 19700 = n := by change n - 19700 + 19700 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 19700)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_19700_19719 i hlen'
                      ·
                        by_cases hcut : n < 19740
                        ·
                          let i : Fin 20 := ⟨n - 19720, by omega⟩
                          have hval : i.val + 19720 = n := by change n - 19720 + 19720 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 19720)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_19720_19739 i hlen'
                        ·
                          let i : Fin 20 := ⟨n - 19740, by omega⟩
                          have hval : i.val + 19740 = n := by change n - 19740 + 19740 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 19740)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_19740_19759 i hlen'
          ·
            by_cases hcut : n < 20660
            ·
              by_cases hcut : n < 20200
              ·
                by_cases hcut : n < 19980
                ·
                  by_cases hcut : n < 19860
                  ·
                    by_cases hcut : n < 19800
                    ·
                      by_cases hcut : n < 19780
                      ·
                        let i : Fin 20 := ⟨n - 19760, by omega⟩
                        have hval : i.val + 19760 = n := by change n - 19760 + 19760 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 19760)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_19760_19779 i hlen'
                      ·
                        let i : Fin 20 := ⟨n - 19780, by omega⟩
                        have hval : i.val + 19780 = n := by change n - 19780 + 19780 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 19780)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_19780_19799 i hlen'
                    ·
                      by_cases hcut : n < 19820
                      ·
                        let i : Fin 20 := ⟨n - 19800, by omega⟩
                        have hval : i.val + 19800 = n := by change n - 19800 + 19800 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 19800)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_19800_19819 i hlen'
                      ·
                        by_cases hcut : n < 19840
                        ·
                          let i : Fin 20 := ⟨n - 19820, by omega⟩
                          have hval : i.val + 19820 = n := by change n - 19820 + 19820 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 19820)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_19820_19839 i hlen'
                        ·
                          let i : Fin 20 := ⟨n - 19840, by omega⟩
                          have hval : i.val + 19840 = n := by change n - 19840 + 19840 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 19840)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_19840_19859 i hlen'
                  ·
                    by_cases hcut : n < 19920
                    ·
                      by_cases hcut : n < 19880
                      ·
                        let i : Fin 20 := ⟨n - 19860, by omega⟩
                        have hval : i.val + 19860 = n := by change n - 19860 + 19860 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 19860)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_19860_19879 i hlen'
                      ·
                        by_cases hcut : n < 19900
                        ·
                          let i : Fin 20 := ⟨n - 19880, by omega⟩
                          have hval : i.val + 19880 = n := by change n - 19880 + 19880 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 19880)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_19880_19899 i hlen'
                        ·
                          let i : Fin 20 := ⟨n - 19900, by omega⟩
                          have hval : i.val + 19900 = n := by change n - 19900 + 19900 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 19900)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_19900_19919 i hlen'
                    ·
                      by_cases hcut : n < 19940
                      ·
                        let i : Fin 20 := ⟨n - 19920, by omega⟩
                        have hval : i.val + 19920 = n := by change n - 19920 + 19920 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 19920)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_19920_19939 i hlen'
                      ·
                        by_cases hcut : n < 19960
                        ·
                          let i : Fin 20 := ⟨n - 19940, by omega⟩
                          have hval : i.val + 19940 = n := by change n - 19940 + 19940 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 19940)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_19940_19959 i hlen'
                        ·
                          let i : Fin 20 := ⟨n - 19960, by omega⟩
                          have hval : i.val + 19960 = n := by change n - 19960 + 19960 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 19960)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_19960_19979 i hlen'
                ·
                  by_cases hcut : n < 20080
                  ·
                    by_cases hcut : n < 20020
                    ·
                      by_cases hcut : n < 20000
                      ·
                        let i : Fin 20 := ⟨n - 19980, by omega⟩
                        have hval : i.val + 19980 = n := by change n - 19980 + 19980 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 19980)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_19980_19999 i hlen'
                      ·
                        let i : Fin 20 := ⟨n - 20000, by omega⟩
                        have hval : i.val + 20000 = n := by change n - 20000 + 20000 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 20000)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_20000_20019 i hlen'
                    ·
                      by_cases hcut : n < 20040
                      ·
                        let i : Fin 20 := ⟨n - 20020, by omega⟩
                        have hval : i.val + 20020 = n := by change n - 20020 + 20020 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 20020)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_20020_20039 i hlen'
                      ·
                        by_cases hcut : n < 20060
                        ·
                          let i : Fin 20 := ⟨n - 20040, by omega⟩
                          have hval : i.val + 20040 = n := by change n - 20040 + 20040 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 20040)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_20040_20059 i hlen'
                        ·
                          let i : Fin 20 := ⟨n - 20060, by omega⟩
                          have hval : i.val + 20060 = n := by change n - 20060 + 20060 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 20060)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_20060_20079 i hlen'
                  ·
                    by_cases hcut : n < 20140
                    ·
                      by_cases hcut : n < 20100
                      ·
                        let i : Fin 20 := ⟨n - 20080, by omega⟩
                        have hval : i.val + 20080 = n := by change n - 20080 + 20080 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 20080)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_20080_20099 i hlen'
                      ·
                        by_cases hcut : n < 20120
                        ·
                          let i : Fin 20 := ⟨n - 20100, by omega⟩
                          have hval : i.val + 20100 = n := by change n - 20100 + 20100 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 20100)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_20100_20119 i hlen'
                        ·
                          let i : Fin 20 := ⟨n - 20120, by omega⟩
                          have hval : i.val + 20120 = n := by change n - 20120 + 20120 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 20120)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_20120_20139 i hlen'
                    ·
                      by_cases hcut : n < 20160
                      ·
                        let i : Fin 20 := ⟨n - 20140, by omega⟩
                        have hval : i.val + 20140 = n := by change n - 20140 + 20140 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 20140)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_20140_20159 i hlen'
                      ·
                        by_cases hcut : n < 20180
                        ·
                          let i : Fin 20 := ⟨n - 20160, by omega⟩
                          have hval : i.val + 20160 = n := by change n - 20160 + 20160 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 20160)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_20160_20179 i hlen'
                        ·
                          let i : Fin 20 := ⟨n - 20180, by omega⟩
                          have hval : i.val + 20180 = n := by change n - 20180 + 20180 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 20180)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_20180_20199 i hlen'
              ·
                by_cases hcut : n < 20420
                ·
                  by_cases hcut : n < 20300
                  ·
                    by_cases hcut : n < 20240
                    ·
                      by_cases hcut : n < 20220
                      ·
                        let i : Fin 20 := ⟨n - 20200, by omega⟩
                        have hval : i.val + 20200 = n := by change n - 20200 + 20200 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 20200)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_20200_20219 i hlen'
                      ·
                        let i : Fin 20 := ⟨n - 20220, by omega⟩
                        have hval : i.val + 20220 = n := by change n - 20220 + 20220 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 20220)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_20220_20239 i hlen'
                    ·
                      by_cases hcut : n < 20260
                      ·
                        let i : Fin 20 := ⟨n - 20240, by omega⟩
                        have hval : i.val + 20240 = n := by change n - 20240 + 20240 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 20240)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_20240_20259 i hlen'
                      ·
                        by_cases hcut : n < 20280
                        ·
                          let i : Fin 20 := ⟨n - 20260, by omega⟩
                          have hval : i.val + 20260 = n := by change n - 20260 + 20260 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 20260)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_20260_20279 i hlen'
                        ·
                          let i : Fin 20 := ⟨n - 20280, by omega⟩
                          have hval : i.val + 20280 = n := by change n - 20280 + 20280 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 20280)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_20280_20299 i hlen'
                  ·
                    by_cases hcut : n < 20360
                    ·
                      by_cases hcut : n < 20320
                      ·
                        let i : Fin 20 := ⟨n - 20300, by omega⟩
                        have hval : i.val + 20300 = n := by change n - 20300 + 20300 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 20300)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_20300_20319 i hlen'
                      ·
                        by_cases hcut : n < 20340
                        ·
                          let i : Fin 20 := ⟨n - 20320, by omega⟩
                          have hval : i.val + 20320 = n := by change n - 20320 + 20320 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 20320)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_20320_20339 i hlen'
                        ·
                          let i : Fin 20 := ⟨n - 20340, by omega⟩
                          have hval : i.val + 20340 = n := by change n - 20340 + 20340 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 20340)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_20340_20359 i hlen'
                    ·
                      by_cases hcut : n < 20380
                      ·
                        let i : Fin 20 := ⟨n - 20360, by omega⟩
                        have hval : i.val + 20360 = n := by change n - 20360 + 20360 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 20360)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_20360_20379 i hlen'
                      ·
                        by_cases hcut : n < 20400
                        ·
                          let i : Fin 20 := ⟨n - 20380, by omega⟩
                          have hval : i.val + 20380 = n := by change n - 20380 + 20380 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 20380)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_20380_20399 i hlen'
                        ·
                          let i : Fin 20 := ⟨n - 20400, by omega⟩
                          have hval : i.val + 20400 = n := by change n - 20400 + 20400 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 20400)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_20400_20419 i hlen'
                ·
                  by_cases hcut : n < 20540
                  ·
                    by_cases hcut : n < 20480
                    ·
                      by_cases hcut : n < 20440
                      ·
                        let i : Fin 20 := ⟨n - 20420, by omega⟩
                        have hval : i.val + 20420 = n := by change n - 20420 + 20420 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 20420)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_20420_20439 i hlen'
                      ·
                        by_cases hcut : n < 20460
                        ·
                          let i : Fin 20 := ⟨n - 20440, by omega⟩
                          have hval : i.val + 20440 = n := by change n - 20440 + 20440 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 20440)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_20440_20459 i hlen'
                        ·
                          let i : Fin 20 := ⟨n - 20460, by omega⟩
                          have hval : i.val + 20460 = n := by change n - 20460 + 20460 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 20460)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_20460_20479 i hlen'
                    ·
                      by_cases hcut : n < 20500
                      ·
                        let i : Fin 20 := ⟨n - 20480, by omega⟩
                        have hval : i.val + 20480 = n := by change n - 20480 + 20480 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 20480)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_20480_20499 i hlen'
                      ·
                        by_cases hcut : n < 20520
                        ·
                          let i : Fin 20 := ⟨n - 20500, by omega⟩
                          have hval : i.val + 20500 = n := by change n - 20500 + 20500 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 20500)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_20500_20519 i hlen'
                        ·
                          let i : Fin 20 := ⟨n - 20520, by omega⟩
                          have hval : i.val + 20520 = n := by change n - 20520 + 20520 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 20520)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_20520_20539 i hlen'
                  ·
                    by_cases hcut : n < 20600
                    ·
                      by_cases hcut : n < 20560
                      ·
                        let i : Fin 20 := ⟨n - 20540, by omega⟩
                        have hval : i.val + 20540 = n := by change n - 20540 + 20540 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 20540)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_20540_20559 i hlen'
                      ·
                        by_cases hcut : n < 20580
                        ·
                          let i : Fin 20 := ⟨n - 20560, by omega⟩
                          have hval : i.val + 20560 = n := by change n - 20560 + 20560 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 20560)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_20560_20579 i hlen'
                        ·
                          let i : Fin 20 := ⟨n - 20580, by omega⟩
                          have hval : i.val + 20580 = n := by change n - 20580 + 20580 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 20580)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_20580_20599 i hlen'
                    ·
                      by_cases hcut : n < 20620
                      ·
                        let i : Fin 20 := ⟨n - 20600, by omega⟩
                        have hval : i.val + 20600 = n := by change n - 20600 + 20600 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 20600)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_20600_20619 i hlen'
                      ·
                        by_cases hcut : n < 20640
                        ·
                          let i : Fin 20 := ⟨n - 20620, by omega⟩
                          have hval : i.val + 20620 = n := by change n - 20620 + 20620 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 20620)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_20620_20639 i hlen'
                        ·
                          let i : Fin 20 := ⟨n - 20640, by omega⟩
                          have hval : i.val + 20640 = n := by change n - 20640 + 20640 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 20640)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_20640_20659 i hlen'
            ·
              by_cases hcut : n < 21100
              ·
                by_cases hcut : n < 20880
                ·
                  by_cases hcut : n < 20760
                  ·
                    by_cases hcut : n < 20700
                    ·
                      by_cases hcut : n < 20680
                      ·
                        let i : Fin 20 := ⟨n - 20660, by omega⟩
                        have hval : i.val + 20660 = n := by change n - 20660 + 20660 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 20660)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_20660_20679 i hlen'
                      ·
                        let i : Fin 20 := ⟨n - 20680, by omega⟩
                        have hval : i.val + 20680 = n := by change n - 20680 + 20680 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 20680)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_20680_20699 i hlen'
                    ·
                      by_cases hcut : n < 20720
                      ·
                        let i : Fin 20 := ⟨n - 20700, by omega⟩
                        have hval : i.val + 20700 = n := by change n - 20700 + 20700 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 20700)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_20700_20719 i hlen'
                      ·
                        by_cases hcut : n < 20740
                        ·
                          let i : Fin 20 := ⟨n - 20720, by omega⟩
                          have hval : i.val + 20720 = n := by change n - 20720 + 20720 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 20720)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_20720_20739 i hlen'
                        ·
                          let i : Fin 20 := ⟨n - 20740, by omega⟩
                          have hval : i.val + 20740 = n := by change n - 20740 + 20740 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 20740)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_20740_20759 i hlen'
                  ·
                    by_cases hcut : n < 20820
                    ·
                      by_cases hcut : n < 20780
                      ·
                        let i : Fin 20 := ⟨n - 20760, by omega⟩
                        have hval : i.val + 20760 = n := by change n - 20760 + 20760 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 20760)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_20760_20779 i hlen'
                      ·
                        by_cases hcut : n < 20800
                        ·
                          let i : Fin 20 := ⟨n - 20780, by omega⟩
                          have hval : i.val + 20780 = n := by change n - 20780 + 20780 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 20780)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_20780_20799 i hlen'
                        ·
                          let i : Fin 20 := ⟨n - 20800, by omega⟩
                          have hval : i.val + 20800 = n := by change n - 20800 + 20800 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 20800)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_20800_20819 i hlen'
                    ·
                      by_cases hcut : n < 20840
                      ·
                        let i : Fin 20 := ⟨n - 20820, by omega⟩
                        have hval : i.val + 20820 = n := by change n - 20820 + 20820 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 20820)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_20820_20839 i hlen'
                      ·
                        by_cases hcut : n < 20860
                        ·
                          let i : Fin 20 := ⟨n - 20840, by omega⟩
                          have hval : i.val + 20840 = n := by change n - 20840 + 20840 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 20840)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_20840_20859 i hlen'
                        ·
                          let i : Fin 20 := ⟨n - 20860, by omega⟩
                          have hval : i.val + 20860 = n := by change n - 20860 + 20860 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 20860)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_20860_20879 i hlen'
                ·
                  by_cases hcut : n < 20980
                  ·
                    by_cases hcut : n < 20920
                    ·
                      by_cases hcut : n < 20900
                      ·
                        let i : Fin 20 := ⟨n - 20880, by omega⟩
                        have hval : i.val + 20880 = n := by change n - 20880 + 20880 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 20880)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_20880_20899 i hlen'
                      ·
                        let i : Fin 20 := ⟨n - 20900, by omega⟩
                        have hval : i.val + 20900 = n := by change n - 20900 + 20900 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 20900)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_20900_20919 i hlen'
                    ·
                      by_cases hcut : n < 20940
                      ·
                        let i : Fin 20 := ⟨n - 20920, by omega⟩
                        have hval : i.val + 20920 = n := by change n - 20920 + 20920 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 20920)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_20920_20939 i hlen'
                      ·
                        by_cases hcut : n < 20960
                        ·
                          let i : Fin 20 := ⟨n - 20940, by omega⟩
                          have hval : i.val + 20940 = n := by change n - 20940 + 20940 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 20940)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_20940_20959 i hlen'
                        ·
                          let i : Fin 20 := ⟨n - 20960, by omega⟩
                          have hval : i.val + 20960 = n := by change n - 20960 + 20960 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 20960)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_20960_20979 i hlen'
                  ·
                    by_cases hcut : n < 21040
                    ·
                      by_cases hcut : n < 21000
                      ·
                        let i : Fin 20 := ⟨n - 20980, by omega⟩
                        have hval : i.val + 20980 = n := by change n - 20980 + 20980 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 20980)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_20980_20999 i hlen'
                      ·
                        by_cases hcut : n < 21020
                        ·
                          let i : Fin 20 := ⟨n - 21000, by omega⟩
                          have hval : i.val + 21000 = n := by change n - 21000 + 21000 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 21000)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_21000_21019 i hlen'
                        ·
                          let i : Fin 20 := ⟨n - 21020, by omega⟩
                          have hval : i.val + 21020 = n := by change n - 21020 + 21020 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 21020)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_21020_21039 i hlen'
                    ·
                      by_cases hcut : n < 21060
                      ·
                        let i : Fin 20 := ⟨n - 21040, by omega⟩
                        have hval : i.val + 21040 = n := by change n - 21040 + 21040 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 21040)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_21040_21059 i hlen'
                      ·
                        by_cases hcut : n < 21080
                        ·
                          let i : Fin 20 := ⟨n - 21060, by omega⟩
                          have hval : i.val + 21060 = n := by change n - 21060 + 21060 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 21060)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_21060_21079 i hlen'
                        ·
                          let i : Fin 20 := ⟨n - 21080, by omega⟩
                          have hval : i.val + 21080 = n := by change n - 21080 + 21080 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 21080)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_21080_21099 i hlen'
              ·
                by_cases hcut : n < 21320
                ·
                  by_cases hcut : n < 21200
                  ·
                    by_cases hcut : n < 21140
                    ·
                      by_cases hcut : n < 21120
                      ·
                        let i : Fin 20 := ⟨n - 21100, by omega⟩
                        have hval : i.val + 21100 = n := by change n - 21100 + 21100 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 21100)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_21100_21119 i hlen'
                      ·
                        let i : Fin 20 := ⟨n - 21120, by omega⟩
                        have hval : i.val + 21120 = n := by change n - 21120 + 21120 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 21120)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_21120_21139 i hlen'
                    ·
                      by_cases hcut : n < 21160
                      ·
                        let i : Fin 20 := ⟨n - 21140, by omega⟩
                        have hval : i.val + 21140 = n := by change n - 21140 + 21140 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 21140)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_21140_21159 i hlen'
                      ·
                        by_cases hcut : n < 21180
                        ·
                          let i : Fin 20 := ⟨n - 21160, by omega⟩
                          have hval : i.val + 21160 = n := by change n - 21160 + 21160 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 21160)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_21160_21179 i hlen'
                        ·
                          let i : Fin 20 := ⟨n - 21180, by omega⟩
                          have hval : i.val + 21180 = n := by change n - 21180 + 21180 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 21180)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_21180_21199 i hlen'
                  ·
                    by_cases hcut : n < 21260
                    ·
                      by_cases hcut : n < 21220
                      ·
                        let i : Fin 20 := ⟨n - 21200, by omega⟩
                        have hval : i.val + 21200 = n := by change n - 21200 + 21200 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 21200)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_21200_21219 i hlen'
                      ·
                        by_cases hcut : n < 21240
                        ·
                          let i : Fin 20 := ⟨n - 21220, by omega⟩
                          have hval : i.val + 21220 = n := by change n - 21220 + 21220 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 21220)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_21220_21239 i hlen'
                        ·
                          let i : Fin 20 := ⟨n - 21240, by omega⟩
                          have hval : i.val + 21240 = n := by change n - 21240 + 21240 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 21240)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_21240_21259 i hlen'
                    ·
                      by_cases hcut : n < 21280
                      ·
                        let i : Fin 20 := ⟨n - 21260, by omega⟩
                        have hval : i.val + 21260 = n := by change n - 21260 + 21260 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 21260)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_21260_21279 i hlen'
                      ·
                        by_cases hcut : n < 21300
                        ·
                          let i : Fin 20 := ⟨n - 21280, by omega⟩
                          have hval : i.val + 21280 = n := by change n - 21280 + 21280 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 21280)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_21280_21299 i hlen'
                        ·
                          let i : Fin 20 := ⟨n - 21300, by omega⟩
                          have hval : i.val + 21300 = n := by change n - 21300 + 21300 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 21300)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_21300_21319 i hlen'
                ·
                  by_cases hcut : n < 21440
                  ·
                    by_cases hcut : n < 21380
                    ·
                      by_cases hcut : n < 21340
                      ·
                        let i : Fin 20 := ⟨n - 21320, by omega⟩
                        have hval : i.val + 21320 = n := by change n - 21320 + 21320 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 21320)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_21320_21339 i hlen'
                      ·
                        by_cases hcut : n < 21360
                        ·
                          let i : Fin 20 := ⟨n - 21340, by omega⟩
                          have hval : i.val + 21340 = n := by change n - 21340 + 21340 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 21340)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_21340_21359 i hlen'
                        ·
                          let i : Fin 20 := ⟨n - 21360, by omega⟩
                          have hval : i.val + 21360 = n := by change n - 21360 + 21360 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 21360)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_21360_21379 i hlen'
                    ·
                      by_cases hcut : n < 21400
                      ·
                        let i : Fin 20 := ⟨n - 21380, by omega⟩
                        have hval : i.val + 21380 = n := by change n - 21380 + 21380 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 21380)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_21380_21399 i hlen'
                      ·
                        by_cases hcut : n < 21420
                        ·
                          let i : Fin 20 := ⟨n - 21400, by omega⟩
                          have hval : i.val + 21400 = n := by change n - 21400 + 21400 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 21400)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_21400_21419 i hlen'
                        ·
                          let i : Fin 20 := ⟨n - 21420, by omega⟩
                          have hval : i.val + 21420 = n := by change n - 21420 + 21420 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 21420)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_21420_21439 i hlen'
                  ·
                    by_cases hcut : n < 21500
                    ·
                      by_cases hcut : n < 21460
                      ·
                        let i : Fin 20 := ⟨n - 21440, by omega⟩
                        have hval : i.val + 21440 = n := by change n - 21440 + 21440 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 21440)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_21440_21459 i hlen'
                      ·
                        by_cases hcut : n < 21480
                        ·
                          let i : Fin 20 := ⟨n - 21460, by omega⟩
                          have hval : i.val + 21460 = n := by change n - 21460 + 21460 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 21460)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_21460_21479 i hlen'
                        ·
                          let i : Fin 20 := ⟨n - 21480, by omega⟩
                          have hval : i.val + 21480 = n := by change n - 21480 + 21480 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 21480)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_21480_21499 i hlen'
                    ·
                      by_cases hcut : n < 21520
                      ·
                        let i : Fin 20 := ⟨n - 21500, by omega⟩
                        have hval : i.val + 21500 = n := by change n - 21500 + 21500 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 21500)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_21500_21519 i hlen'
                      ·
                        by_cases hcut : n < 21540
                        ·
                          let i : Fin 20 := ⟨n - 21520, by omega⟩
                          have hval : i.val + 21520 = n := by change n - 21520 + 21520 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 21520)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_21520_21539 i hlen'
                        ·
                          let i : Fin 20 := ⟨n - 21540, by omega⟩
                          have hval : i.val + 21540 = n := by change n - 21540 + 21540 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 21540)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_21540_21559 i hlen'
      ·
        by_cases hcut : n < 25160
        ·
          by_cases hcut : n < 23360
          ·
            by_cases hcut : n < 22460
            ·
              by_cases hcut : n < 22000
              ·
                by_cases hcut : n < 21780
                ·
                  by_cases hcut : n < 21660
                  ·
                    by_cases hcut : n < 21600
                    ·
                      by_cases hcut : n < 21580
                      ·
                        let i : Fin 20 := ⟨n - 21560, by omega⟩
                        have hval : i.val + 21560 = n := by change n - 21560 + 21560 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 21560)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_21560_21579 i hlen'
                      ·
                        let i : Fin 20 := ⟨n - 21580, by omega⟩
                        have hval : i.val + 21580 = n := by change n - 21580 + 21580 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 21580)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_21580_21599 i hlen'
                    ·
                      by_cases hcut : n < 21620
                      ·
                        let i : Fin 20 := ⟨n - 21600, by omega⟩
                        have hval : i.val + 21600 = n := by change n - 21600 + 21600 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 21600)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_21600_21619 i hlen'
                      ·
                        by_cases hcut : n < 21640
                        ·
                          let i : Fin 20 := ⟨n - 21620, by omega⟩
                          have hval : i.val + 21620 = n := by change n - 21620 + 21620 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 21620)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_21620_21639 i hlen'
                        ·
                          let i : Fin 20 := ⟨n - 21640, by omega⟩
                          have hval : i.val + 21640 = n := by change n - 21640 + 21640 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 21640)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_21640_21659 i hlen'
                  ·
                    by_cases hcut : n < 21720
                    ·
                      by_cases hcut : n < 21680
                      ·
                        let i : Fin 20 := ⟨n - 21660, by omega⟩
                        have hval : i.val + 21660 = n := by change n - 21660 + 21660 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 21660)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_21660_21679 i hlen'
                      ·
                        by_cases hcut : n < 21700
                        ·
                          let i : Fin 20 := ⟨n - 21680, by omega⟩
                          have hval : i.val + 21680 = n := by change n - 21680 + 21680 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 21680)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_21680_21699 i hlen'
                        ·
                          let i : Fin 20 := ⟨n - 21700, by omega⟩
                          have hval : i.val + 21700 = n := by change n - 21700 + 21700 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 21700)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_21700_21719 i hlen'
                    ·
                      by_cases hcut : n < 21740
                      ·
                        let i : Fin 20 := ⟨n - 21720, by omega⟩
                        have hval : i.val + 21720 = n := by change n - 21720 + 21720 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 21720)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_21720_21739 i hlen'
                      ·
                        by_cases hcut : n < 21760
                        ·
                          let i : Fin 20 := ⟨n - 21740, by omega⟩
                          have hval : i.val + 21740 = n := by change n - 21740 + 21740 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 21740)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_21740_21759 i hlen'
                        ·
                          let i : Fin 20 := ⟨n - 21760, by omega⟩
                          have hval : i.val + 21760 = n := by change n - 21760 + 21760 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 21760)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_21760_21779 i hlen'
                ·
                  by_cases hcut : n < 21880
                  ·
                    by_cases hcut : n < 21820
                    ·
                      by_cases hcut : n < 21800
                      ·
                        let i : Fin 20 := ⟨n - 21780, by omega⟩
                        have hval : i.val + 21780 = n := by change n - 21780 + 21780 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 21780)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_21780_21799 i hlen'
                      ·
                        let i : Fin 20 := ⟨n - 21800, by omega⟩
                        have hval : i.val + 21800 = n := by change n - 21800 + 21800 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 21800)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_21800_21819 i hlen'
                    ·
                      by_cases hcut : n < 21840
                      ·
                        let i : Fin 20 := ⟨n - 21820, by omega⟩
                        have hval : i.val + 21820 = n := by change n - 21820 + 21820 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 21820)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_21820_21839 i hlen'
                      ·
                        by_cases hcut : n < 21860
                        ·
                          let i : Fin 20 := ⟨n - 21840, by omega⟩
                          have hval : i.val + 21840 = n := by change n - 21840 + 21840 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 21840)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_21840_21859 i hlen'
                        ·
                          let i : Fin 20 := ⟨n - 21860, by omega⟩
                          have hval : i.val + 21860 = n := by change n - 21860 + 21860 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 21860)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_21860_21879 i hlen'
                  ·
                    by_cases hcut : n < 21940
                    ·
                      by_cases hcut : n < 21900
                      ·
                        let i : Fin 20 := ⟨n - 21880, by omega⟩
                        have hval : i.val + 21880 = n := by change n - 21880 + 21880 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 21880)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_21880_21899 i hlen'
                      ·
                        by_cases hcut : n < 21920
                        ·
                          let i : Fin 20 := ⟨n - 21900, by omega⟩
                          have hval : i.val + 21900 = n := by change n - 21900 + 21900 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 21900)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_21900_21919 i hlen'
                        ·
                          let i : Fin 20 := ⟨n - 21920, by omega⟩
                          have hval : i.val + 21920 = n := by change n - 21920 + 21920 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 21920)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_21920_21939 i hlen'
                    ·
                      by_cases hcut : n < 21960
                      ·
                        let i : Fin 20 := ⟨n - 21940, by omega⟩
                        have hval : i.val + 21940 = n := by change n - 21940 + 21940 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 21940)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_21940_21959 i hlen'
                      ·
                        by_cases hcut : n < 21980
                        ·
                          let i : Fin 20 := ⟨n - 21960, by omega⟩
                          have hval : i.val + 21960 = n := by change n - 21960 + 21960 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 21960)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_21960_21979 i hlen'
                        ·
                          let i : Fin 20 := ⟨n - 21980, by omega⟩
                          have hval : i.val + 21980 = n := by change n - 21980 + 21980 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 21980)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_21980_21999 i hlen'
              ·
                by_cases hcut : n < 22220
                ·
                  by_cases hcut : n < 22100
                  ·
                    by_cases hcut : n < 22040
                    ·
                      by_cases hcut : n < 22020
                      ·
                        let i : Fin 20 := ⟨n - 22000, by omega⟩
                        have hval : i.val + 22000 = n := by change n - 22000 + 22000 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 22000)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_22000_22019 i hlen'
                      ·
                        let i : Fin 20 := ⟨n - 22020, by omega⟩
                        have hval : i.val + 22020 = n := by change n - 22020 + 22020 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 22020)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_22020_22039 i hlen'
                    ·
                      by_cases hcut : n < 22060
                      ·
                        let i : Fin 20 := ⟨n - 22040, by omega⟩
                        have hval : i.val + 22040 = n := by change n - 22040 + 22040 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 22040)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_22040_22059 i hlen'
                      ·
                        by_cases hcut : n < 22080
                        ·
                          let i : Fin 20 := ⟨n - 22060, by omega⟩
                          have hval : i.val + 22060 = n := by change n - 22060 + 22060 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 22060)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_22060_22079 i hlen'
                        ·
                          let i : Fin 20 := ⟨n - 22080, by omega⟩
                          have hval : i.val + 22080 = n := by change n - 22080 + 22080 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 22080)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_22080_22099 i hlen'
                  ·
                    by_cases hcut : n < 22160
                    ·
                      by_cases hcut : n < 22120
                      ·
                        let i : Fin 20 := ⟨n - 22100, by omega⟩
                        have hval : i.val + 22100 = n := by change n - 22100 + 22100 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 22100)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_22100_22119 i hlen'
                      ·
                        by_cases hcut : n < 22140
                        ·
                          let i : Fin 20 := ⟨n - 22120, by omega⟩
                          have hval : i.val + 22120 = n := by change n - 22120 + 22120 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 22120)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_22120_22139 i hlen'
                        ·
                          let i : Fin 20 := ⟨n - 22140, by omega⟩
                          have hval : i.val + 22140 = n := by change n - 22140 + 22140 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 22140)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_22140_22159 i hlen'
                    ·
                      by_cases hcut : n < 22180
                      ·
                        let i : Fin 20 := ⟨n - 22160, by omega⟩
                        have hval : i.val + 22160 = n := by change n - 22160 + 22160 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 22160)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_22160_22179 i hlen'
                      ·
                        by_cases hcut : n < 22200
                        ·
                          let i : Fin 20 := ⟨n - 22180, by omega⟩
                          have hval : i.val + 22180 = n := by change n - 22180 + 22180 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 22180)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_22180_22199 i hlen'
                        ·
                          let i : Fin 20 := ⟨n - 22200, by omega⟩
                          have hval : i.val + 22200 = n := by change n - 22200 + 22200 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 22200)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_22200_22219 i hlen'
                ·
                  by_cases hcut : n < 22340
                  ·
                    by_cases hcut : n < 22280
                    ·
                      by_cases hcut : n < 22240
                      ·
                        let i : Fin 20 := ⟨n - 22220, by omega⟩
                        have hval : i.val + 22220 = n := by change n - 22220 + 22220 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 22220)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_22220_22239 i hlen'
                      ·
                        by_cases hcut : n < 22260
                        ·
                          let i : Fin 20 := ⟨n - 22240, by omega⟩
                          have hval : i.val + 22240 = n := by change n - 22240 + 22240 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 22240)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_22240_22259 i hlen'
                        ·
                          let i : Fin 20 := ⟨n - 22260, by omega⟩
                          have hval : i.val + 22260 = n := by change n - 22260 + 22260 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 22260)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_22260_22279 i hlen'
                    ·
                      by_cases hcut : n < 22300
                      ·
                        let i : Fin 20 := ⟨n - 22280, by omega⟩
                        have hval : i.val + 22280 = n := by change n - 22280 + 22280 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 22280)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_22280_22299 i hlen'
                      ·
                        by_cases hcut : n < 22320
                        ·
                          let i : Fin 20 := ⟨n - 22300, by omega⟩
                          have hval : i.val + 22300 = n := by change n - 22300 + 22300 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 22300)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_22300_22319 i hlen'
                        ·
                          let i : Fin 20 := ⟨n - 22320, by omega⟩
                          have hval : i.val + 22320 = n := by change n - 22320 + 22320 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 22320)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_22320_22339 i hlen'
                  ·
                    by_cases hcut : n < 22400
                    ·
                      by_cases hcut : n < 22360
                      ·
                        let i : Fin 20 := ⟨n - 22340, by omega⟩
                        have hval : i.val + 22340 = n := by change n - 22340 + 22340 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 22340)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_22340_22359 i hlen'
                      ·
                        by_cases hcut : n < 22380
                        ·
                          let i : Fin 20 := ⟨n - 22360, by omega⟩
                          have hval : i.val + 22360 = n := by change n - 22360 + 22360 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 22360)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_22360_22379 i hlen'
                        ·
                          let i : Fin 20 := ⟨n - 22380, by omega⟩
                          have hval : i.val + 22380 = n := by change n - 22380 + 22380 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 22380)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_22380_22399 i hlen'
                    ·
                      by_cases hcut : n < 22420
                      ·
                        let i : Fin 20 := ⟨n - 22400, by omega⟩
                        have hval : i.val + 22400 = n := by change n - 22400 + 22400 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 22400)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_22400_22419 i hlen'
                      ·
                        by_cases hcut : n < 22440
                        ·
                          let i : Fin 20 := ⟨n - 22420, by omega⟩
                          have hval : i.val + 22420 = n := by change n - 22420 + 22420 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 22420)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_22420_22439 i hlen'
                        ·
                          let i : Fin 20 := ⟨n - 22440, by omega⟩
                          have hval : i.val + 22440 = n := by change n - 22440 + 22440 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 22440)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_22440_22459 i hlen'
            ·
              by_cases hcut : n < 22900
              ·
                by_cases hcut : n < 22680
                ·
                  by_cases hcut : n < 22560
                  ·
                    by_cases hcut : n < 22500
                    ·
                      by_cases hcut : n < 22480
                      ·
                        let i : Fin 20 := ⟨n - 22460, by omega⟩
                        have hval : i.val + 22460 = n := by change n - 22460 + 22460 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 22460)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_22460_22479 i hlen'
                      ·
                        let i : Fin 20 := ⟨n - 22480, by omega⟩
                        have hval : i.val + 22480 = n := by change n - 22480 + 22480 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 22480)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_22480_22499 i hlen'
                    ·
                      by_cases hcut : n < 22520
                      ·
                        let i : Fin 20 := ⟨n - 22500, by omega⟩
                        have hval : i.val + 22500 = n := by change n - 22500 + 22500 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 22500)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_22500_22519 i hlen'
                      ·
                        by_cases hcut : n < 22540
                        ·
                          let i : Fin 20 := ⟨n - 22520, by omega⟩
                          have hval : i.val + 22520 = n := by change n - 22520 + 22520 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 22520)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_22520_22539 i hlen'
                        ·
                          let i : Fin 20 := ⟨n - 22540, by omega⟩
                          have hval : i.val + 22540 = n := by change n - 22540 + 22540 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 22540)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_22540_22559 i hlen'
                  ·
                    by_cases hcut : n < 22620
                    ·
                      by_cases hcut : n < 22580
                      ·
                        let i : Fin 20 := ⟨n - 22560, by omega⟩
                        have hval : i.val + 22560 = n := by change n - 22560 + 22560 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 22560)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_22560_22579 i hlen'
                      ·
                        by_cases hcut : n < 22600
                        ·
                          let i : Fin 20 := ⟨n - 22580, by omega⟩
                          have hval : i.val + 22580 = n := by change n - 22580 + 22580 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 22580)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_22580_22599 i hlen'
                        ·
                          let i : Fin 20 := ⟨n - 22600, by omega⟩
                          have hval : i.val + 22600 = n := by change n - 22600 + 22600 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 22600)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_22600_22619 i hlen'
                    ·
                      by_cases hcut : n < 22640
                      ·
                        let i : Fin 20 := ⟨n - 22620, by omega⟩
                        have hval : i.val + 22620 = n := by change n - 22620 + 22620 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 22620)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_22620_22639 i hlen'
                      ·
                        by_cases hcut : n < 22660
                        ·
                          let i : Fin 20 := ⟨n - 22640, by omega⟩
                          have hval : i.val + 22640 = n := by change n - 22640 + 22640 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 22640)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_22640_22659 i hlen'
                        ·
                          let i : Fin 20 := ⟨n - 22660, by omega⟩
                          have hval : i.val + 22660 = n := by change n - 22660 + 22660 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 22660)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_22660_22679 i hlen'
                ·
                  by_cases hcut : n < 22780
                  ·
                    by_cases hcut : n < 22720
                    ·
                      by_cases hcut : n < 22700
                      ·
                        let i : Fin 20 := ⟨n - 22680, by omega⟩
                        have hval : i.val + 22680 = n := by change n - 22680 + 22680 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 22680)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_22680_22699 i hlen'
                      ·
                        let i : Fin 20 := ⟨n - 22700, by omega⟩
                        have hval : i.val + 22700 = n := by change n - 22700 + 22700 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 22700)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_22700_22719 i hlen'
                    ·
                      by_cases hcut : n < 22740
                      ·
                        let i : Fin 20 := ⟨n - 22720, by omega⟩
                        have hval : i.val + 22720 = n := by change n - 22720 + 22720 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 22720)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_22720_22739 i hlen'
                      ·
                        by_cases hcut : n < 22760
                        ·
                          let i : Fin 20 := ⟨n - 22740, by omega⟩
                          have hval : i.val + 22740 = n := by change n - 22740 + 22740 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 22740)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_22740_22759 i hlen'
                        ·
                          let i : Fin 20 := ⟨n - 22760, by omega⟩
                          have hval : i.val + 22760 = n := by change n - 22760 + 22760 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 22760)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_22760_22779 i hlen'
                  ·
                    by_cases hcut : n < 22840
                    ·
                      by_cases hcut : n < 22800
                      ·
                        let i : Fin 20 := ⟨n - 22780, by omega⟩
                        have hval : i.val + 22780 = n := by change n - 22780 + 22780 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 22780)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_22780_22799 i hlen'
                      ·
                        by_cases hcut : n < 22820
                        ·
                          let i : Fin 20 := ⟨n - 22800, by omega⟩
                          have hval : i.val + 22800 = n := by change n - 22800 + 22800 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 22800)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_22800_22819 i hlen'
                        ·
                          let i : Fin 20 := ⟨n - 22820, by omega⟩
                          have hval : i.val + 22820 = n := by change n - 22820 + 22820 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 22820)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_22820_22839 i hlen'
                    ·
                      by_cases hcut : n < 22860
                      ·
                        let i : Fin 20 := ⟨n - 22840, by omega⟩
                        have hval : i.val + 22840 = n := by change n - 22840 + 22840 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 22840)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_22840_22859 i hlen'
                      ·
                        by_cases hcut : n < 22880
                        ·
                          let i : Fin 20 := ⟨n - 22860, by omega⟩
                          have hval : i.val + 22860 = n := by change n - 22860 + 22860 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 22860)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_22860_22879 i hlen'
                        ·
                          let i : Fin 20 := ⟨n - 22880, by omega⟩
                          have hval : i.val + 22880 = n := by change n - 22880 + 22880 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 22880)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_22880_22899 i hlen'
              ·
                by_cases hcut : n < 23120
                ·
                  by_cases hcut : n < 23000
                  ·
                    by_cases hcut : n < 22940
                    ·
                      by_cases hcut : n < 22920
                      ·
                        let i : Fin 20 := ⟨n - 22900, by omega⟩
                        have hval : i.val + 22900 = n := by change n - 22900 + 22900 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 22900)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_22900_22919 i hlen'
                      ·
                        let i : Fin 20 := ⟨n - 22920, by omega⟩
                        have hval : i.val + 22920 = n := by change n - 22920 + 22920 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 22920)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_22920_22939 i hlen'
                    ·
                      by_cases hcut : n < 22960
                      ·
                        let i : Fin 20 := ⟨n - 22940, by omega⟩
                        have hval : i.val + 22940 = n := by change n - 22940 + 22940 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 22940)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_22940_22959 i hlen'
                      ·
                        by_cases hcut : n < 22980
                        ·
                          let i : Fin 20 := ⟨n - 22960, by omega⟩
                          have hval : i.val + 22960 = n := by change n - 22960 + 22960 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 22960)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_22960_22979 i hlen'
                        ·
                          let i : Fin 20 := ⟨n - 22980, by omega⟩
                          have hval : i.val + 22980 = n := by change n - 22980 + 22980 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 22980)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_22980_22999 i hlen'
                  ·
                    by_cases hcut : n < 23060
                    ·
                      by_cases hcut : n < 23020
                      ·
                        let i : Fin 20 := ⟨n - 23000, by omega⟩
                        have hval : i.val + 23000 = n := by change n - 23000 + 23000 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 23000)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_23000_23019 i hlen'
                      ·
                        by_cases hcut : n < 23040
                        ·
                          let i : Fin 20 := ⟨n - 23020, by omega⟩
                          have hval : i.val + 23020 = n := by change n - 23020 + 23020 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 23020)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_23020_23039 i hlen'
                        ·
                          let i : Fin 20 := ⟨n - 23040, by omega⟩
                          have hval : i.val + 23040 = n := by change n - 23040 + 23040 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 23040)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_23040_23059 i hlen'
                    ·
                      by_cases hcut : n < 23080
                      ·
                        let i : Fin 20 := ⟨n - 23060, by omega⟩
                        have hval : i.val + 23060 = n := by change n - 23060 + 23060 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 23060)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_23060_23079 i hlen'
                      ·
                        by_cases hcut : n < 23100
                        ·
                          let i : Fin 20 := ⟨n - 23080, by omega⟩
                          have hval : i.val + 23080 = n := by change n - 23080 + 23080 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 23080)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_23080_23099 i hlen'
                        ·
                          let i : Fin 20 := ⟨n - 23100, by omega⟩
                          have hval : i.val + 23100 = n := by change n - 23100 + 23100 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 23100)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_23100_23119 i hlen'
                ·
                  by_cases hcut : n < 23240
                  ·
                    by_cases hcut : n < 23180
                    ·
                      by_cases hcut : n < 23140
                      ·
                        let i : Fin 20 := ⟨n - 23120, by omega⟩
                        have hval : i.val + 23120 = n := by change n - 23120 + 23120 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 23120)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_23120_23139 i hlen'
                      ·
                        by_cases hcut : n < 23160
                        ·
                          let i : Fin 20 := ⟨n - 23140, by omega⟩
                          have hval : i.val + 23140 = n := by change n - 23140 + 23140 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 23140)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_23140_23159 i hlen'
                        ·
                          let i : Fin 20 := ⟨n - 23160, by omega⟩
                          have hval : i.val + 23160 = n := by change n - 23160 + 23160 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 23160)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_23160_23179 i hlen'
                    ·
                      by_cases hcut : n < 23200
                      ·
                        let i : Fin 20 := ⟨n - 23180, by omega⟩
                        have hval : i.val + 23180 = n := by change n - 23180 + 23180 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 23180)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_23180_23199 i hlen'
                      ·
                        by_cases hcut : n < 23220
                        ·
                          let i : Fin 20 := ⟨n - 23200, by omega⟩
                          have hval : i.val + 23200 = n := by change n - 23200 + 23200 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 23200)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_23200_23219 i hlen'
                        ·
                          let i : Fin 20 := ⟨n - 23220, by omega⟩
                          have hval : i.val + 23220 = n := by change n - 23220 + 23220 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 23220)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_23220_23239 i hlen'
                  ·
                    by_cases hcut : n < 23300
                    ·
                      by_cases hcut : n < 23260
                      ·
                        let i : Fin 20 := ⟨n - 23240, by omega⟩
                        have hval : i.val + 23240 = n := by change n - 23240 + 23240 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 23240)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_23240_23259 i hlen'
                      ·
                        by_cases hcut : n < 23280
                        ·
                          let i : Fin 20 := ⟨n - 23260, by omega⟩
                          have hval : i.val + 23260 = n := by change n - 23260 + 23260 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 23260)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_23260_23279 i hlen'
                        ·
                          let i : Fin 20 := ⟨n - 23280, by omega⟩
                          have hval : i.val + 23280 = n := by change n - 23280 + 23280 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 23280)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_23280_23299 i hlen'
                    ·
                      by_cases hcut : n < 23320
                      ·
                        let i : Fin 20 := ⟨n - 23300, by omega⟩
                        have hval : i.val + 23300 = n := by change n - 23300 + 23300 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 23300)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_23300_23319 i hlen'
                      ·
                        by_cases hcut : n < 23340
                        ·
                          let i : Fin 20 := ⟨n - 23320, by omega⟩
                          have hval : i.val + 23320 = n := by change n - 23320 + 23320 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 23320)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_23320_23339 i hlen'
                        ·
                          let i : Fin 20 := ⟨n - 23340, by omega⟩
                          have hval : i.val + 23340 = n := by change n - 23340 + 23340 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 23340)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_23340_23359 i hlen'
          ·
            by_cases hcut : n < 24260
            ·
              by_cases hcut : n < 23800
              ·
                by_cases hcut : n < 23580
                ·
                  by_cases hcut : n < 23460
                  ·
                    by_cases hcut : n < 23400
                    ·
                      by_cases hcut : n < 23380
                      ·
                        let i : Fin 20 := ⟨n - 23360, by omega⟩
                        have hval : i.val + 23360 = n := by change n - 23360 + 23360 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 23360)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_23360_23379 i hlen'
                      ·
                        let i : Fin 20 := ⟨n - 23380, by omega⟩
                        have hval : i.val + 23380 = n := by change n - 23380 + 23380 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 23380)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_23380_23399 i hlen'
                    ·
                      by_cases hcut : n < 23420
                      ·
                        let i : Fin 20 := ⟨n - 23400, by omega⟩
                        have hval : i.val + 23400 = n := by change n - 23400 + 23400 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 23400)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_23400_23419 i hlen'
                      ·
                        by_cases hcut : n < 23440
                        ·
                          let i : Fin 20 := ⟨n - 23420, by omega⟩
                          have hval : i.val + 23420 = n := by change n - 23420 + 23420 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 23420)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_23420_23439 i hlen'
                        ·
                          let i : Fin 20 := ⟨n - 23440, by omega⟩
                          have hval : i.val + 23440 = n := by change n - 23440 + 23440 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 23440)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_23440_23459 i hlen'
                  ·
                    by_cases hcut : n < 23520
                    ·
                      by_cases hcut : n < 23480
                      ·
                        let i : Fin 20 := ⟨n - 23460, by omega⟩
                        have hval : i.val + 23460 = n := by change n - 23460 + 23460 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 23460)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_23460_23479 i hlen'
                      ·
                        by_cases hcut : n < 23500
                        ·
                          let i : Fin 20 := ⟨n - 23480, by omega⟩
                          have hval : i.val + 23480 = n := by change n - 23480 + 23480 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 23480)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_23480_23499 i hlen'
                        ·
                          let i : Fin 20 := ⟨n - 23500, by omega⟩
                          have hval : i.val + 23500 = n := by change n - 23500 + 23500 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 23500)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_23500_23519 i hlen'
                    ·
                      by_cases hcut : n < 23540
                      ·
                        let i : Fin 20 := ⟨n - 23520, by omega⟩
                        have hval : i.val + 23520 = n := by change n - 23520 + 23520 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 23520)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_23520_23539 i hlen'
                      ·
                        by_cases hcut : n < 23560
                        ·
                          let i : Fin 20 := ⟨n - 23540, by omega⟩
                          have hval : i.val + 23540 = n := by change n - 23540 + 23540 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 23540)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_23540_23559 i hlen'
                        ·
                          let i : Fin 20 := ⟨n - 23560, by omega⟩
                          have hval : i.val + 23560 = n := by change n - 23560 + 23560 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 23560)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_23560_23579 i hlen'
                ·
                  by_cases hcut : n < 23680
                  ·
                    by_cases hcut : n < 23620
                    ·
                      by_cases hcut : n < 23600
                      ·
                        let i : Fin 20 := ⟨n - 23580, by omega⟩
                        have hval : i.val + 23580 = n := by change n - 23580 + 23580 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 23580)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_23580_23599 i hlen'
                      ·
                        let i : Fin 20 := ⟨n - 23600, by omega⟩
                        have hval : i.val + 23600 = n := by change n - 23600 + 23600 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 23600)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_23600_23619 i hlen'
                    ·
                      by_cases hcut : n < 23640
                      ·
                        let i : Fin 20 := ⟨n - 23620, by omega⟩
                        have hval : i.val + 23620 = n := by change n - 23620 + 23620 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 23620)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_23620_23639 i hlen'
                      ·
                        by_cases hcut : n < 23660
                        ·
                          let i : Fin 20 := ⟨n - 23640, by omega⟩
                          have hval : i.val + 23640 = n := by change n - 23640 + 23640 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 23640)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_23640_23659 i hlen'
                        ·
                          let i : Fin 20 := ⟨n - 23660, by omega⟩
                          have hval : i.val + 23660 = n := by change n - 23660 + 23660 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 23660)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_23660_23679 i hlen'
                  ·
                    by_cases hcut : n < 23740
                    ·
                      by_cases hcut : n < 23700
                      ·
                        let i : Fin 20 := ⟨n - 23680, by omega⟩
                        have hval : i.val + 23680 = n := by change n - 23680 + 23680 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 23680)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_23680_23699 i hlen'
                      ·
                        by_cases hcut : n < 23720
                        ·
                          let i : Fin 20 := ⟨n - 23700, by omega⟩
                          have hval : i.val + 23700 = n := by change n - 23700 + 23700 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 23700)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_23700_23719 i hlen'
                        ·
                          let i : Fin 20 := ⟨n - 23720, by omega⟩
                          have hval : i.val + 23720 = n := by change n - 23720 + 23720 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 23720)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_23720_23739 i hlen'
                    ·
                      by_cases hcut : n < 23760
                      ·
                        let i : Fin 20 := ⟨n - 23740, by omega⟩
                        have hval : i.val + 23740 = n := by change n - 23740 + 23740 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 23740)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_23740_23759 i hlen'
                      ·
                        by_cases hcut : n < 23780
                        ·
                          let i : Fin 20 := ⟨n - 23760, by omega⟩
                          have hval : i.val + 23760 = n := by change n - 23760 + 23760 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 23760)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_23760_23779 i hlen'
                        ·
                          let i : Fin 20 := ⟨n - 23780, by omega⟩
                          have hval : i.val + 23780 = n := by change n - 23780 + 23780 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 23780)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_23780_23799 i hlen'
              ·
                by_cases hcut : n < 24020
                ·
                  by_cases hcut : n < 23900
                  ·
                    by_cases hcut : n < 23840
                    ·
                      by_cases hcut : n < 23820
                      ·
                        let i : Fin 20 := ⟨n - 23800, by omega⟩
                        have hval : i.val + 23800 = n := by change n - 23800 + 23800 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 23800)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_23800_23819 i hlen'
                      ·
                        let i : Fin 20 := ⟨n - 23820, by omega⟩
                        have hval : i.val + 23820 = n := by change n - 23820 + 23820 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 23820)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_23820_23839 i hlen'
                    ·
                      by_cases hcut : n < 23860
                      ·
                        let i : Fin 20 := ⟨n - 23840, by omega⟩
                        have hval : i.val + 23840 = n := by change n - 23840 + 23840 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 23840)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_23840_23859 i hlen'
                      ·
                        by_cases hcut : n < 23880
                        ·
                          let i : Fin 20 := ⟨n - 23860, by omega⟩
                          have hval : i.val + 23860 = n := by change n - 23860 + 23860 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 23860)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_23860_23879 i hlen'
                        ·
                          let i : Fin 20 := ⟨n - 23880, by omega⟩
                          have hval : i.val + 23880 = n := by change n - 23880 + 23880 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 23880)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_23880_23899 i hlen'
                  ·
                    by_cases hcut : n < 23960
                    ·
                      by_cases hcut : n < 23920
                      ·
                        let i : Fin 20 := ⟨n - 23900, by omega⟩
                        have hval : i.val + 23900 = n := by change n - 23900 + 23900 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 23900)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_23900_23919 i hlen'
                      ·
                        by_cases hcut : n < 23940
                        ·
                          let i : Fin 20 := ⟨n - 23920, by omega⟩
                          have hval : i.val + 23920 = n := by change n - 23920 + 23920 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 23920)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_23920_23939 i hlen'
                        ·
                          let i : Fin 20 := ⟨n - 23940, by omega⟩
                          have hval : i.val + 23940 = n := by change n - 23940 + 23940 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 23940)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_23940_23959 i hlen'
                    ·
                      by_cases hcut : n < 23980
                      ·
                        let i : Fin 20 := ⟨n - 23960, by omega⟩
                        have hval : i.val + 23960 = n := by change n - 23960 + 23960 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 23960)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_23960_23979 i hlen'
                      ·
                        by_cases hcut : n < 24000
                        ·
                          let i : Fin 20 := ⟨n - 23980, by omega⟩
                          have hval : i.val + 23980 = n := by change n - 23980 + 23980 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 23980)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_23980_23999 i hlen'
                        ·
                          let i : Fin 20 := ⟨n - 24000, by omega⟩
                          have hval : i.val + 24000 = n := by change n - 24000 + 24000 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 24000)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_24000_24019 i hlen'
                ·
                  by_cases hcut : n < 24140
                  ·
                    by_cases hcut : n < 24080
                    ·
                      by_cases hcut : n < 24040
                      ·
                        let i : Fin 20 := ⟨n - 24020, by omega⟩
                        have hval : i.val + 24020 = n := by change n - 24020 + 24020 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 24020)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_24020_24039 i hlen'
                      ·
                        by_cases hcut : n < 24060
                        ·
                          let i : Fin 20 := ⟨n - 24040, by omega⟩
                          have hval : i.val + 24040 = n := by change n - 24040 + 24040 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 24040)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_24040_24059 i hlen'
                        ·
                          let i : Fin 20 := ⟨n - 24060, by omega⟩
                          have hval : i.val + 24060 = n := by change n - 24060 + 24060 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 24060)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_24060_24079 i hlen'
                    ·
                      by_cases hcut : n < 24100
                      ·
                        let i : Fin 20 := ⟨n - 24080, by omega⟩
                        have hval : i.val + 24080 = n := by change n - 24080 + 24080 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 24080)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_24080_24099 i hlen'
                      ·
                        by_cases hcut : n < 24120
                        ·
                          let i : Fin 20 := ⟨n - 24100, by omega⟩
                          have hval : i.val + 24100 = n := by change n - 24100 + 24100 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 24100)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_24100_24119 i hlen'
                        ·
                          let i : Fin 20 := ⟨n - 24120, by omega⟩
                          have hval : i.val + 24120 = n := by change n - 24120 + 24120 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 24120)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_24120_24139 i hlen'
                  ·
                    by_cases hcut : n < 24200
                    ·
                      by_cases hcut : n < 24160
                      ·
                        let i : Fin 20 := ⟨n - 24140, by omega⟩
                        have hval : i.val + 24140 = n := by change n - 24140 + 24140 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 24140)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_24140_24159 i hlen'
                      ·
                        by_cases hcut : n < 24180
                        ·
                          let i : Fin 20 := ⟨n - 24160, by omega⟩
                          have hval : i.val + 24160 = n := by change n - 24160 + 24160 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 24160)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_24160_24179 i hlen'
                        ·
                          let i : Fin 20 := ⟨n - 24180, by omega⟩
                          have hval : i.val + 24180 = n := by change n - 24180 + 24180 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 24180)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_24180_24199 i hlen'
                    ·
                      by_cases hcut : n < 24220
                      ·
                        let i : Fin 20 := ⟨n - 24200, by omega⟩
                        have hval : i.val + 24200 = n := by change n - 24200 + 24200 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 24200)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_24200_24219 i hlen'
                      ·
                        by_cases hcut : n < 24240
                        ·
                          let i : Fin 20 := ⟨n - 24220, by omega⟩
                          have hval : i.val + 24220 = n := by change n - 24220 + 24220 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 24220)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_24220_24239 i hlen'
                        ·
                          let i : Fin 20 := ⟨n - 24240, by omega⟩
                          have hval : i.val + 24240 = n := by change n - 24240 + 24240 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 24240)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_24240_24259 i hlen'
            ·
              by_cases hcut : n < 24700
              ·
                by_cases hcut : n < 24480
                ·
                  by_cases hcut : n < 24360
                  ·
                    by_cases hcut : n < 24300
                    ·
                      by_cases hcut : n < 24280
                      ·
                        let i : Fin 20 := ⟨n - 24260, by omega⟩
                        have hval : i.val + 24260 = n := by change n - 24260 + 24260 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 24260)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_24260_24279 i hlen'
                      ·
                        let i : Fin 20 := ⟨n - 24280, by omega⟩
                        have hval : i.val + 24280 = n := by change n - 24280 + 24280 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 24280)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_24280_24299 i hlen'
                    ·
                      by_cases hcut : n < 24320
                      ·
                        let i : Fin 20 := ⟨n - 24300, by omega⟩
                        have hval : i.val + 24300 = n := by change n - 24300 + 24300 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 24300)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_24300_24319 i hlen'
                      ·
                        by_cases hcut : n < 24340
                        ·
                          let i : Fin 20 := ⟨n - 24320, by omega⟩
                          have hval : i.val + 24320 = n := by change n - 24320 + 24320 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 24320)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_24320_24339 i hlen'
                        ·
                          let i : Fin 20 := ⟨n - 24340, by omega⟩
                          have hval : i.val + 24340 = n := by change n - 24340 + 24340 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 24340)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_24340_24359 i hlen'
                  ·
                    by_cases hcut : n < 24420
                    ·
                      by_cases hcut : n < 24380
                      ·
                        let i : Fin 20 := ⟨n - 24360, by omega⟩
                        have hval : i.val + 24360 = n := by change n - 24360 + 24360 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 24360)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_24360_24379 i hlen'
                      ·
                        by_cases hcut : n < 24400
                        ·
                          let i : Fin 20 := ⟨n - 24380, by omega⟩
                          have hval : i.val + 24380 = n := by change n - 24380 + 24380 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 24380)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_24380_24399 i hlen'
                        ·
                          let i : Fin 20 := ⟨n - 24400, by omega⟩
                          have hval : i.val + 24400 = n := by change n - 24400 + 24400 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 24400)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_24400_24419 i hlen'
                    ·
                      by_cases hcut : n < 24440
                      ·
                        let i : Fin 20 := ⟨n - 24420, by omega⟩
                        have hval : i.val + 24420 = n := by change n - 24420 + 24420 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 24420)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_24420_24439 i hlen'
                      ·
                        by_cases hcut : n < 24460
                        ·
                          let i : Fin 20 := ⟨n - 24440, by omega⟩
                          have hval : i.val + 24440 = n := by change n - 24440 + 24440 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 24440)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_24440_24459 i hlen'
                        ·
                          let i : Fin 20 := ⟨n - 24460, by omega⟩
                          have hval : i.val + 24460 = n := by change n - 24460 + 24460 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 24460)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_24460_24479 i hlen'
                ·
                  by_cases hcut : n < 24580
                  ·
                    by_cases hcut : n < 24520
                    ·
                      by_cases hcut : n < 24500
                      ·
                        let i : Fin 20 := ⟨n - 24480, by omega⟩
                        have hval : i.val + 24480 = n := by change n - 24480 + 24480 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 24480)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_24480_24499 i hlen'
                      ·
                        let i : Fin 20 := ⟨n - 24500, by omega⟩
                        have hval : i.val + 24500 = n := by change n - 24500 + 24500 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 24500)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_24500_24519 i hlen'
                    ·
                      by_cases hcut : n < 24540
                      ·
                        let i : Fin 20 := ⟨n - 24520, by omega⟩
                        have hval : i.val + 24520 = n := by change n - 24520 + 24520 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 24520)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_24520_24539 i hlen'
                      ·
                        by_cases hcut : n < 24560
                        ·
                          let i : Fin 20 := ⟨n - 24540, by omega⟩
                          have hval : i.val + 24540 = n := by change n - 24540 + 24540 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 24540)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_24540_24559 i hlen'
                        ·
                          let i : Fin 20 := ⟨n - 24560, by omega⟩
                          have hval : i.val + 24560 = n := by change n - 24560 + 24560 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 24560)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_24560_24579 i hlen'
                  ·
                    by_cases hcut : n < 24640
                    ·
                      by_cases hcut : n < 24600
                      ·
                        let i : Fin 20 := ⟨n - 24580, by omega⟩
                        have hval : i.val + 24580 = n := by change n - 24580 + 24580 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 24580)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_24580_24599 i hlen'
                      ·
                        by_cases hcut : n < 24620
                        ·
                          let i : Fin 20 := ⟨n - 24600, by omega⟩
                          have hval : i.val + 24600 = n := by change n - 24600 + 24600 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 24600)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_24600_24619 i hlen'
                        ·
                          let i : Fin 20 := ⟨n - 24620, by omega⟩
                          have hval : i.val + 24620 = n := by change n - 24620 + 24620 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 24620)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_24620_24639 i hlen'
                    ·
                      by_cases hcut : n < 24660
                      ·
                        let i : Fin 20 := ⟨n - 24640, by omega⟩
                        have hval : i.val + 24640 = n := by change n - 24640 + 24640 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 24640)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_24640_24659 i hlen'
                      ·
                        by_cases hcut : n < 24680
                        ·
                          let i : Fin 20 := ⟨n - 24660, by omega⟩
                          have hval : i.val + 24660 = n := by change n - 24660 + 24660 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 24660)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_24660_24679 i hlen'
                        ·
                          let i : Fin 20 := ⟨n - 24680, by omega⟩
                          have hval : i.val + 24680 = n := by change n - 24680 + 24680 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 24680)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_24680_24699 i hlen'
              ·
                by_cases hcut : n < 24920
                ·
                  by_cases hcut : n < 24800
                  ·
                    by_cases hcut : n < 24740
                    ·
                      by_cases hcut : n < 24720
                      ·
                        let i : Fin 20 := ⟨n - 24700, by omega⟩
                        have hval : i.val + 24700 = n := by change n - 24700 + 24700 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 24700)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_24700_24719 i hlen'
                      ·
                        let i : Fin 20 := ⟨n - 24720, by omega⟩
                        have hval : i.val + 24720 = n := by change n - 24720 + 24720 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 24720)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_24720_24739 i hlen'
                    ·
                      by_cases hcut : n < 24760
                      ·
                        let i : Fin 20 := ⟨n - 24740, by omega⟩
                        have hval : i.val + 24740 = n := by change n - 24740 + 24740 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 24740)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_24740_24759 i hlen'
                      ·
                        by_cases hcut : n < 24780
                        ·
                          let i : Fin 20 := ⟨n - 24760, by omega⟩
                          have hval : i.val + 24760 = n := by change n - 24760 + 24760 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 24760)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_24760_24779 i hlen'
                        ·
                          let i : Fin 20 := ⟨n - 24780, by omega⟩
                          have hval : i.val + 24780 = n := by change n - 24780 + 24780 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 24780)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_24780_24799 i hlen'
                  ·
                    by_cases hcut : n < 24860
                    ·
                      by_cases hcut : n < 24820
                      ·
                        let i : Fin 20 := ⟨n - 24800, by omega⟩
                        have hval : i.val + 24800 = n := by change n - 24800 + 24800 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 24800)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_24800_24819 i hlen'
                      ·
                        by_cases hcut : n < 24840
                        ·
                          let i : Fin 20 := ⟨n - 24820, by omega⟩
                          have hval : i.val + 24820 = n := by change n - 24820 + 24820 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 24820)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_24820_24839 i hlen'
                        ·
                          let i : Fin 20 := ⟨n - 24840, by omega⟩
                          have hval : i.val + 24840 = n := by change n - 24840 + 24840 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 24840)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_24840_24859 i hlen'
                    ·
                      by_cases hcut : n < 24880
                      ·
                        let i : Fin 20 := ⟨n - 24860, by omega⟩
                        have hval : i.val + 24860 = n := by change n - 24860 + 24860 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 24860)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_24860_24879 i hlen'
                      ·
                        by_cases hcut : n < 24900
                        ·
                          let i : Fin 20 := ⟨n - 24880, by omega⟩
                          have hval : i.val + 24880 = n := by change n - 24880 + 24880 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 24880)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_24880_24899 i hlen'
                        ·
                          let i : Fin 20 := ⟨n - 24900, by omega⟩
                          have hval : i.val + 24900 = n := by change n - 24900 + 24900 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 24900)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_24900_24919 i hlen'
                ·
                  by_cases hcut : n < 25040
                  ·
                    by_cases hcut : n < 24980
                    ·
                      by_cases hcut : n < 24940
                      ·
                        let i : Fin 20 := ⟨n - 24920, by omega⟩
                        have hval : i.val + 24920 = n := by change n - 24920 + 24920 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 24920)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_24920_24939 i hlen'
                      ·
                        by_cases hcut : n < 24960
                        ·
                          let i : Fin 20 := ⟨n - 24940, by omega⟩
                          have hval : i.val + 24940 = n := by change n - 24940 + 24940 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 24940)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_24940_24959 i hlen'
                        ·
                          let i : Fin 20 := ⟨n - 24960, by omega⟩
                          have hval : i.val + 24960 = n := by change n - 24960 + 24960 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 24960)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_24960_24979 i hlen'
                    ·
                      by_cases hcut : n < 25000
                      ·
                        let i : Fin 20 := ⟨n - 24980, by omega⟩
                        have hval : i.val + 24980 = n := by change n - 24980 + 24980 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 24980)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_24980_24999 i hlen'
                      ·
                        by_cases hcut : n < 25020
                        ·
                          let i : Fin 20 := ⟨n - 25000, by omega⟩
                          have hval : i.val + 25000 = n := by change n - 25000 + 25000 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 25000)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_25000_25019 i hlen'
                        ·
                          let i : Fin 20 := ⟨n - 25020, by omega⟩
                          have hval : i.val + 25020 = n := by change n - 25020 + 25020 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 25020)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_25020_25039 i hlen'
                  ·
                    by_cases hcut : n < 25100
                    ·
                      by_cases hcut : n < 25060
                      ·
                        let i : Fin 20 := ⟨n - 25040, by omega⟩
                        have hval : i.val + 25040 = n := by change n - 25040 + 25040 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 25040)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_25040_25059 i hlen'
                      ·
                        by_cases hcut : n < 25080
                        ·
                          let i : Fin 20 := ⟨n - 25060, by omega⟩
                          have hval : i.val + 25060 = n := by change n - 25060 + 25060 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 25060)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_25060_25079 i hlen'
                        ·
                          let i : Fin 20 := ⟨n - 25080, by omega⟩
                          have hval : i.val + 25080 = n := by change n - 25080 + 25080 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 25080)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_25080_25099 i hlen'
                    ·
                      by_cases hcut : n < 25120
                      ·
                        let i : Fin 20 := ⟨n - 25100, by omega⟩
                        have hval : i.val + 25100 = n := by change n - 25100 + 25100 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 25100)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_25100_25119 i hlen'
                      ·
                        by_cases hcut : n < 25140
                        ·
                          let i : Fin 20 := ⟨n - 25120, by omega⟩
                          have hval : i.val + 25120 = n := by change n - 25120 + 25120 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 25120)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_25120_25139 i hlen'
                        ·
                          let i : Fin 20 := ⟨n - 25140, by omega⟩
                          have hval : i.val + 25140 = n := by change n - 25140 + 25140 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 25140)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_25140_25159 i hlen'
        ·
          by_cases hcut : n < 26960
          ·
            by_cases hcut : n < 26060
            ·
              by_cases hcut : n < 25600
              ·
                by_cases hcut : n < 25380
                ·
                  by_cases hcut : n < 25260
                  ·
                    by_cases hcut : n < 25200
                    ·
                      by_cases hcut : n < 25180
                      ·
                        let i : Fin 20 := ⟨n - 25160, by omega⟩
                        have hval : i.val + 25160 = n := by change n - 25160 + 25160 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 25160)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_25160_25179 i hlen'
                      ·
                        let i : Fin 20 := ⟨n - 25180, by omega⟩
                        have hval : i.val + 25180 = n := by change n - 25180 + 25180 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 25180)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_25180_25199 i hlen'
                    ·
                      by_cases hcut : n < 25220
                      ·
                        let i : Fin 20 := ⟨n - 25200, by omega⟩
                        have hval : i.val + 25200 = n := by change n - 25200 + 25200 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 25200)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_25200_25219 i hlen'
                      ·
                        by_cases hcut : n < 25240
                        ·
                          let i : Fin 20 := ⟨n - 25220, by omega⟩
                          have hval : i.val + 25220 = n := by change n - 25220 + 25220 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 25220)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_25220_25239 i hlen'
                        ·
                          let i : Fin 20 := ⟨n - 25240, by omega⟩
                          have hval : i.val + 25240 = n := by change n - 25240 + 25240 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 25240)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_25240_25259 i hlen'
                  ·
                    by_cases hcut : n < 25320
                    ·
                      by_cases hcut : n < 25280
                      ·
                        let i : Fin 20 := ⟨n - 25260, by omega⟩
                        have hval : i.val + 25260 = n := by change n - 25260 + 25260 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 25260)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_25260_25279 i hlen'
                      ·
                        by_cases hcut : n < 25300
                        ·
                          let i : Fin 20 := ⟨n - 25280, by omega⟩
                          have hval : i.val + 25280 = n := by change n - 25280 + 25280 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 25280)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_25280_25299 i hlen'
                        ·
                          let i : Fin 20 := ⟨n - 25300, by omega⟩
                          have hval : i.val + 25300 = n := by change n - 25300 + 25300 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 25300)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_25300_25319 i hlen'
                    ·
                      by_cases hcut : n < 25340
                      ·
                        let i : Fin 20 := ⟨n - 25320, by omega⟩
                        have hval : i.val + 25320 = n := by change n - 25320 + 25320 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 25320)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_25320_25339 i hlen'
                      ·
                        by_cases hcut : n < 25360
                        ·
                          let i : Fin 20 := ⟨n - 25340, by omega⟩
                          have hval : i.val + 25340 = n := by change n - 25340 + 25340 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 25340)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_25340_25359 i hlen'
                        ·
                          let i : Fin 20 := ⟨n - 25360, by omega⟩
                          have hval : i.val + 25360 = n := by change n - 25360 + 25360 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 25360)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_25360_25379 i hlen'
                ·
                  by_cases hcut : n < 25480
                  ·
                    by_cases hcut : n < 25420
                    ·
                      by_cases hcut : n < 25400
                      ·
                        let i : Fin 20 := ⟨n - 25380, by omega⟩
                        have hval : i.val + 25380 = n := by change n - 25380 + 25380 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 25380)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_25380_25399 i hlen'
                      ·
                        let i : Fin 20 := ⟨n - 25400, by omega⟩
                        have hval : i.val + 25400 = n := by change n - 25400 + 25400 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 25400)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_25400_25419 i hlen'
                    ·
                      by_cases hcut : n < 25440
                      ·
                        let i : Fin 20 := ⟨n - 25420, by omega⟩
                        have hval : i.val + 25420 = n := by change n - 25420 + 25420 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 25420)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_25420_25439 i hlen'
                      ·
                        by_cases hcut : n < 25460
                        ·
                          let i : Fin 20 := ⟨n - 25440, by omega⟩
                          have hval : i.val + 25440 = n := by change n - 25440 + 25440 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 25440)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_25440_25459 i hlen'
                        ·
                          let i : Fin 20 := ⟨n - 25460, by omega⟩
                          have hval : i.val + 25460 = n := by change n - 25460 + 25460 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 25460)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_25460_25479 i hlen'
                  ·
                    by_cases hcut : n < 25540
                    ·
                      by_cases hcut : n < 25500
                      ·
                        let i : Fin 20 := ⟨n - 25480, by omega⟩
                        have hval : i.val + 25480 = n := by change n - 25480 + 25480 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 25480)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_25480_25499 i hlen'
                      ·
                        by_cases hcut : n < 25520
                        ·
                          let i : Fin 20 := ⟨n - 25500, by omega⟩
                          have hval : i.val + 25500 = n := by change n - 25500 + 25500 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 25500)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_25500_25519 i hlen'
                        ·
                          let i : Fin 20 := ⟨n - 25520, by omega⟩
                          have hval : i.val + 25520 = n := by change n - 25520 + 25520 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 25520)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_25520_25539 i hlen'
                    ·
                      by_cases hcut : n < 25560
                      ·
                        let i : Fin 20 := ⟨n - 25540, by omega⟩
                        have hval : i.val + 25540 = n := by change n - 25540 + 25540 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 25540)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_25540_25559 i hlen'
                      ·
                        by_cases hcut : n < 25580
                        ·
                          let i : Fin 20 := ⟨n - 25560, by omega⟩
                          have hval : i.val + 25560 = n := by change n - 25560 + 25560 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 25560)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_25560_25579 i hlen'
                        ·
                          let i : Fin 20 := ⟨n - 25580, by omega⟩
                          have hval : i.val + 25580 = n := by change n - 25580 + 25580 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 25580)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_25580_25599 i hlen'
              ·
                by_cases hcut : n < 25820
                ·
                  by_cases hcut : n < 25700
                  ·
                    by_cases hcut : n < 25640
                    ·
                      by_cases hcut : n < 25620
                      ·
                        let i : Fin 20 := ⟨n - 25600, by omega⟩
                        have hval : i.val + 25600 = n := by change n - 25600 + 25600 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 25600)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_25600_25619 i hlen'
                      ·
                        let i : Fin 20 := ⟨n - 25620, by omega⟩
                        have hval : i.val + 25620 = n := by change n - 25620 + 25620 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 25620)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_25620_25639 i hlen'
                    ·
                      by_cases hcut : n < 25660
                      ·
                        let i : Fin 20 := ⟨n - 25640, by omega⟩
                        have hval : i.val + 25640 = n := by change n - 25640 + 25640 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 25640)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_25640_25659 i hlen'
                      ·
                        by_cases hcut : n < 25680
                        ·
                          let i : Fin 20 := ⟨n - 25660, by omega⟩
                          have hval : i.val + 25660 = n := by change n - 25660 + 25660 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 25660)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_25660_25679 i hlen'
                        ·
                          let i : Fin 20 := ⟨n - 25680, by omega⟩
                          have hval : i.val + 25680 = n := by change n - 25680 + 25680 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 25680)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_25680_25699 i hlen'
                  ·
                    by_cases hcut : n < 25760
                    ·
                      by_cases hcut : n < 25720
                      ·
                        let i : Fin 20 := ⟨n - 25700, by omega⟩
                        have hval : i.val + 25700 = n := by change n - 25700 + 25700 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 25700)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_25700_25719 i hlen'
                      ·
                        by_cases hcut : n < 25740
                        ·
                          let i : Fin 20 := ⟨n - 25720, by omega⟩
                          have hval : i.val + 25720 = n := by change n - 25720 + 25720 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 25720)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_25720_25739 i hlen'
                        ·
                          let i : Fin 20 := ⟨n - 25740, by omega⟩
                          have hval : i.val + 25740 = n := by change n - 25740 + 25740 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 25740)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_25740_25759 i hlen'
                    ·
                      by_cases hcut : n < 25780
                      ·
                        let i : Fin 20 := ⟨n - 25760, by omega⟩
                        have hval : i.val + 25760 = n := by change n - 25760 + 25760 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 25760)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_25760_25779 i hlen'
                      ·
                        by_cases hcut : n < 25800
                        ·
                          let i : Fin 20 := ⟨n - 25780, by omega⟩
                          have hval : i.val + 25780 = n := by change n - 25780 + 25780 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 25780)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_25780_25799 i hlen'
                        ·
                          let i : Fin 20 := ⟨n - 25800, by omega⟩
                          have hval : i.val + 25800 = n := by change n - 25800 + 25800 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 25800)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_25800_25819 i hlen'
                ·
                  by_cases hcut : n < 25940
                  ·
                    by_cases hcut : n < 25880
                    ·
                      by_cases hcut : n < 25840
                      ·
                        let i : Fin 20 := ⟨n - 25820, by omega⟩
                        have hval : i.val + 25820 = n := by change n - 25820 + 25820 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 25820)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_25820_25839 i hlen'
                      ·
                        by_cases hcut : n < 25860
                        ·
                          let i : Fin 20 := ⟨n - 25840, by omega⟩
                          have hval : i.val + 25840 = n := by change n - 25840 + 25840 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 25840)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_25840_25859 i hlen'
                        ·
                          let i : Fin 20 := ⟨n - 25860, by omega⟩
                          have hval : i.val + 25860 = n := by change n - 25860 + 25860 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 25860)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_25860_25879 i hlen'
                    ·
                      by_cases hcut : n < 25900
                      ·
                        let i : Fin 20 := ⟨n - 25880, by omega⟩
                        have hval : i.val + 25880 = n := by change n - 25880 + 25880 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 25880)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_25880_25899 i hlen'
                      ·
                        by_cases hcut : n < 25920
                        ·
                          let i : Fin 20 := ⟨n - 25900, by omega⟩
                          have hval : i.val + 25900 = n := by change n - 25900 + 25900 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 25900)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_25900_25919 i hlen'
                        ·
                          let i : Fin 20 := ⟨n - 25920, by omega⟩
                          have hval : i.val + 25920 = n := by change n - 25920 + 25920 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 25920)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_25920_25939 i hlen'
                  ·
                    by_cases hcut : n < 26000
                    ·
                      by_cases hcut : n < 25960
                      ·
                        let i : Fin 20 := ⟨n - 25940, by omega⟩
                        have hval : i.val + 25940 = n := by change n - 25940 + 25940 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 25940)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_25940_25959 i hlen'
                      ·
                        by_cases hcut : n < 25980
                        ·
                          let i : Fin 20 := ⟨n - 25960, by omega⟩
                          have hval : i.val + 25960 = n := by change n - 25960 + 25960 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 25960)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_25960_25979 i hlen'
                        ·
                          let i : Fin 20 := ⟨n - 25980, by omega⟩
                          have hval : i.val + 25980 = n := by change n - 25980 + 25980 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 25980)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_25980_25999 i hlen'
                    ·
                      by_cases hcut : n < 26020
                      ·
                        let i : Fin 20 := ⟨n - 26000, by omega⟩
                        have hval : i.val + 26000 = n := by change n - 26000 + 26000 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 26000)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_26000_26019 i hlen'
                      ·
                        by_cases hcut : n < 26040
                        ·
                          let i : Fin 20 := ⟨n - 26020, by omega⟩
                          have hval : i.val + 26020 = n := by change n - 26020 + 26020 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 26020)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_26020_26039 i hlen'
                        ·
                          let i : Fin 20 := ⟨n - 26040, by omega⟩
                          have hval : i.val + 26040 = n := by change n - 26040 + 26040 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 26040)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_26040_26059 i hlen'
            ·
              by_cases hcut : n < 26500
              ·
                by_cases hcut : n < 26280
                ·
                  by_cases hcut : n < 26160
                  ·
                    by_cases hcut : n < 26100
                    ·
                      by_cases hcut : n < 26080
                      ·
                        let i : Fin 20 := ⟨n - 26060, by omega⟩
                        have hval : i.val + 26060 = n := by change n - 26060 + 26060 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 26060)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_26060_26079 i hlen'
                      ·
                        let i : Fin 20 := ⟨n - 26080, by omega⟩
                        have hval : i.val + 26080 = n := by change n - 26080 + 26080 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 26080)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_26080_26099 i hlen'
                    ·
                      by_cases hcut : n < 26120
                      ·
                        let i : Fin 20 := ⟨n - 26100, by omega⟩
                        have hval : i.val + 26100 = n := by change n - 26100 + 26100 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 26100)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_26100_26119 i hlen'
                      ·
                        by_cases hcut : n < 26140
                        ·
                          let i : Fin 20 := ⟨n - 26120, by omega⟩
                          have hval : i.val + 26120 = n := by change n - 26120 + 26120 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 26120)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_26120_26139 i hlen'
                        ·
                          let i : Fin 20 := ⟨n - 26140, by omega⟩
                          have hval : i.val + 26140 = n := by change n - 26140 + 26140 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 26140)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_26140_26159 i hlen'
                  ·
                    by_cases hcut : n < 26220
                    ·
                      by_cases hcut : n < 26180
                      ·
                        let i : Fin 20 := ⟨n - 26160, by omega⟩
                        have hval : i.val + 26160 = n := by change n - 26160 + 26160 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 26160)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_26160_26179 i hlen'
                      ·
                        by_cases hcut : n < 26200
                        ·
                          let i : Fin 20 := ⟨n - 26180, by omega⟩
                          have hval : i.val + 26180 = n := by change n - 26180 + 26180 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 26180)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_26180_26199 i hlen'
                        ·
                          let i : Fin 20 := ⟨n - 26200, by omega⟩
                          have hval : i.val + 26200 = n := by change n - 26200 + 26200 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 26200)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_26200_26219 i hlen'
                    ·
                      by_cases hcut : n < 26240
                      ·
                        let i : Fin 20 := ⟨n - 26220, by omega⟩
                        have hval : i.val + 26220 = n := by change n - 26220 + 26220 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 26220)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_26220_26239 i hlen'
                      ·
                        by_cases hcut : n < 26260
                        ·
                          let i : Fin 20 := ⟨n - 26240, by omega⟩
                          have hval : i.val + 26240 = n := by change n - 26240 + 26240 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 26240)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_26240_26259 i hlen'
                        ·
                          let i : Fin 20 := ⟨n - 26260, by omega⟩
                          have hval : i.val + 26260 = n := by change n - 26260 + 26260 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 26260)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_26260_26279 i hlen'
                ·
                  by_cases hcut : n < 26380
                  ·
                    by_cases hcut : n < 26320
                    ·
                      by_cases hcut : n < 26300
                      ·
                        let i : Fin 20 := ⟨n - 26280, by omega⟩
                        have hval : i.val + 26280 = n := by change n - 26280 + 26280 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 26280)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_26280_26299 i hlen'
                      ·
                        let i : Fin 20 := ⟨n - 26300, by omega⟩
                        have hval : i.val + 26300 = n := by change n - 26300 + 26300 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 26300)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_26300_26319 i hlen'
                    ·
                      by_cases hcut : n < 26340
                      ·
                        let i : Fin 20 := ⟨n - 26320, by omega⟩
                        have hval : i.val + 26320 = n := by change n - 26320 + 26320 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 26320)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_26320_26339 i hlen'
                      ·
                        by_cases hcut : n < 26360
                        ·
                          let i : Fin 20 := ⟨n - 26340, by omega⟩
                          have hval : i.val + 26340 = n := by change n - 26340 + 26340 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 26340)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_26340_26359 i hlen'
                        ·
                          let i : Fin 20 := ⟨n - 26360, by omega⟩
                          have hval : i.val + 26360 = n := by change n - 26360 + 26360 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 26360)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_26360_26379 i hlen'
                  ·
                    by_cases hcut : n < 26440
                    ·
                      by_cases hcut : n < 26400
                      ·
                        let i : Fin 20 := ⟨n - 26380, by omega⟩
                        have hval : i.val + 26380 = n := by change n - 26380 + 26380 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 26380)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_26380_26399 i hlen'
                      ·
                        by_cases hcut : n < 26420
                        ·
                          let i : Fin 20 := ⟨n - 26400, by omega⟩
                          have hval : i.val + 26400 = n := by change n - 26400 + 26400 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 26400)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_26400_26419 i hlen'
                        ·
                          let i : Fin 20 := ⟨n - 26420, by omega⟩
                          have hval : i.val + 26420 = n := by change n - 26420 + 26420 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 26420)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_26420_26439 i hlen'
                    ·
                      by_cases hcut : n < 26460
                      ·
                        let i : Fin 20 := ⟨n - 26440, by omega⟩
                        have hval : i.val + 26440 = n := by change n - 26440 + 26440 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 26440)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_26440_26459 i hlen'
                      ·
                        by_cases hcut : n < 26480
                        ·
                          let i : Fin 20 := ⟨n - 26460, by omega⟩
                          have hval : i.val + 26460 = n := by change n - 26460 + 26460 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 26460)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_26460_26479 i hlen'
                        ·
                          let i : Fin 20 := ⟨n - 26480, by omega⟩
                          have hval : i.val + 26480 = n := by change n - 26480 + 26480 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 26480)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_26480_26499 i hlen'
              ·
                by_cases hcut : n < 26720
                ·
                  by_cases hcut : n < 26600
                  ·
                    by_cases hcut : n < 26540
                    ·
                      by_cases hcut : n < 26520
                      ·
                        let i : Fin 20 := ⟨n - 26500, by omega⟩
                        have hval : i.val + 26500 = n := by change n - 26500 + 26500 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 26500)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_26500_26519 i hlen'
                      ·
                        let i : Fin 20 := ⟨n - 26520, by omega⟩
                        have hval : i.val + 26520 = n := by change n - 26520 + 26520 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 26520)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_26520_26539 i hlen'
                    ·
                      by_cases hcut : n < 26560
                      ·
                        let i : Fin 20 := ⟨n - 26540, by omega⟩
                        have hval : i.val + 26540 = n := by change n - 26540 + 26540 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 26540)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_26540_26559 i hlen'
                      ·
                        by_cases hcut : n < 26580
                        ·
                          let i : Fin 20 := ⟨n - 26560, by omega⟩
                          have hval : i.val + 26560 = n := by change n - 26560 + 26560 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 26560)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_26560_26579 i hlen'
                        ·
                          let i : Fin 20 := ⟨n - 26580, by omega⟩
                          have hval : i.val + 26580 = n := by change n - 26580 + 26580 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 26580)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_26580_26599 i hlen'
                  ·
                    by_cases hcut : n < 26660
                    ·
                      by_cases hcut : n < 26620
                      ·
                        let i : Fin 20 := ⟨n - 26600, by omega⟩
                        have hval : i.val + 26600 = n := by change n - 26600 + 26600 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 26600)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_26600_26619 i hlen'
                      ·
                        by_cases hcut : n < 26640
                        ·
                          let i : Fin 20 := ⟨n - 26620, by omega⟩
                          have hval : i.val + 26620 = n := by change n - 26620 + 26620 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 26620)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_26620_26639 i hlen'
                        ·
                          let i : Fin 20 := ⟨n - 26640, by omega⟩
                          have hval : i.val + 26640 = n := by change n - 26640 + 26640 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 26640)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_26640_26659 i hlen'
                    ·
                      by_cases hcut : n < 26680
                      ·
                        let i : Fin 20 := ⟨n - 26660, by omega⟩
                        have hval : i.val + 26660 = n := by change n - 26660 + 26660 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 26660)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_26660_26679 i hlen'
                      ·
                        by_cases hcut : n < 26700
                        ·
                          let i : Fin 20 := ⟨n - 26680, by omega⟩
                          have hval : i.val + 26680 = n := by change n - 26680 + 26680 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 26680)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_26680_26699 i hlen'
                        ·
                          let i : Fin 20 := ⟨n - 26700, by omega⟩
                          have hval : i.val + 26700 = n := by change n - 26700 + 26700 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 26700)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_26700_26719 i hlen'
                ·
                  by_cases hcut : n < 26840
                  ·
                    by_cases hcut : n < 26780
                    ·
                      by_cases hcut : n < 26740
                      ·
                        let i : Fin 20 := ⟨n - 26720, by omega⟩
                        have hval : i.val + 26720 = n := by change n - 26720 + 26720 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 26720)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_26720_26739 i hlen'
                      ·
                        by_cases hcut : n < 26760
                        ·
                          let i : Fin 20 := ⟨n - 26740, by omega⟩
                          have hval : i.val + 26740 = n := by change n - 26740 + 26740 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 26740)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_26740_26759 i hlen'
                        ·
                          let i : Fin 20 := ⟨n - 26760, by omega⟩
                          have hval : i.val + 26760 = n := by change n - 26760 + 26760 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 26760)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_26760_26779 i hlen'
                    ·
                      by_cases hcut : n < 26800
                      ·
                        let i : Fin 20 := ⟨n - 26780, by omega⟩
                        have hval : i.val + 26780 = n := by change n - 26780 + 26780 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 26780)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_26780_26799 i hlen'
                      ·
                        by_cases hcut : n < 26820
                        ·
                          let i : Fin 20 := ⟨n - 26800, by omega⟩
                          have hval : i.val + 26800 = n := by change n - 26800 + 26800 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 26800)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_26800_26819 i hlen'
                        ·
                          let i : Fin 20 := ⟨n - 26820, by omega⟩
                          have hval : i.val + 26820 = n := by change n - 26820 + 26820 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 26820)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_26820_26839 i hlen'
                  ·
                    by_cases hcut : n < 26900
                    ·
                      by_cases hcut : n < 26860
                      ·
                        let i : Fin 20 := ⟨n - 26840, by omega⟩
                        have hval : i.val + 26840 = n := by change n - 26840 + 26840 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 26840)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_26840_26859 i hlen'
                      ·
                        by_cases hcut : n < 26880
                        ·
                          let i : Fin 20 := ⟨n - 26860, by omega⟩
                          have hval : i.val + 26860 = n := by change n - 26860 + 26860 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 26860)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_26860_26879 i hlen'
                        ·
                          let i : Fin 20 := ⟨n - 26880, by omega⟩
                          have hval : i.val + 26880 = n := by change n - 26880 + 26880 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 26880)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_26880_26899 i hlen'
                    ·
                      by_cases hcut : n < 26920
                      ·
                        let i : Fin 20 := ⟨n - 26900, by omega⟩
                        have hval : i.val + 26900 = n := by change n - 26900 + 26900 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 26900)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_26900_26919 i hlen'
                      ·
                        by_cases hcut : n < 26940
                        ·
                          let i : Fin 20 := ⟨n - 26920, by omega⟩
                          have hval : i.val + 26920 = n := by change n - 26920 + 26920 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 26920)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_26920_26939 i hlen'
                        ·
                          let i : Fin 20 := ⟨n - 26940, by omega⟩
                          have hval : i.val + 26940 = n := by change n - 26940 + 26940 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 26940)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_26940_26959 i hlen'
          ·
            by_cases hcut : n < 27860
            ·
              by_cases hcut : n < 27400
              ·
                by_cases hcut : n < 27180
                ·
                  by_cases hcut : n < 27060
                  ·
                    by_cases hcut : n < 27000
                    ·
                      by_cases hcut : n < 26980
                      ·
                        let i : Fin 20 := ⟨n - 26960, by omega⟩
                        have hval : i.val + 26960 = n := by change n - 26960 + 26960 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 26960)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_26960_26979 i hlen'
                      ·
                        let i : Fin 20 := ⟨n - 26980, by omega⟩
                        have hval : i.val + 26980 = n := by change n - 26980 + 26980 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 26980)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_26980_26999 i hlen'
                    ·
                      by_cases hcut : n < 27020
                      ·
                        let i : Fin 20 := ⟨n - 27000, by omega⟩
                        have hval : i.val + 27000 = n := by change n - 27000 + 27000 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 27000)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_27000_27019 i hlen'
                      ·
                        by_cases hcut : n < 27040
                        ·
                          let i : Fin 20 := ⟨n - 27020, by omega⟩
                          have hval : i.val + 27020 = n := by change n - 27020 + 27020 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 27020)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_27020_27039 i hlen'
                        ·
                          let i : Fin 20 := ⟨n - 27040, by omega⟩
                          have hval : i.val + 27040 = n := by change n - 27040 + 27040 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 27040)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_27040_27059 i hlen'
                  ·
                    by_cases hcut : n < 27120
                    ·
                      by_cases hcut : n < 27080
                      ·
                        let i : Fin 20 := ⟨n - 27060, by omega⟩
                        have hval : i.val + 27060 = n := by change n - 27060 + 27060 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 27060)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_27060_27079 i hlen'
                      ·
                        by_cases hcut : n < 27100
                        ·
                          let i : Fin 20 := ⟨n - 27080, by omega⟩
                          have hval : i.val + 27080 = n := by change n - 27080 + 27080 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 27080)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_27080_27099 i hlen'
                        ·
                          let i : Fin 20 := ⟨n - 27100, by omega⟩
                          have hval : i.val + 27100 = n := by change n - 27100 + 27100 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 27100)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_27100_27119 i hlen'
                    ·
                      by_cases hcut : n < 27140
                      ·
                        let i : Fin 20 := ⟨n - 27120, by omega⟩
                        have hval : i.val + 27120 = n := by change n - 27120 + 27120 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 27120)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_27120_27139 i hlen'
                      ·
                        by_cases hcut : n < 27160
                        ·
                          let i : Fin 20 := ⟨n - 27140, by omega⟩
                          have hval : i.val + 27140 = n := by change n - 27140 + 27140 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 27140)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_27140_27159 i hlen'
                        ·
                          let i : Fin 20 := ⟨n - 27160, by omega⟩
                          have hval : i.val + 27160 = n := by change n - 27160 + 27160 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 27160)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_27160_27179 i hlen'
                ·
                  by_cases hcut : n < 27280
                  ·
                    by_cases hcut : n < 27220
                    ·
                      by_cases hcut : n < 27200
                      ·
                        let i : Fin 20 := ⟨n - 27180, by omega⟩
                        have hval : i.val + 27180 = n := by change n - 27180 + 27180 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 27180)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_27180_27199 i hlen'
                      ·
                        let i : Fin 20 := ⟨n - 27200, by omega⟩
                        have hval : i.val + 27200 = n := by change n - 27200 + 27200 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 27200)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_27200_27219 i hlen'
                    ·
                      by_cases hcut : n < 27240
                      ·
                        let i : Fin 20 := ⟨n - 27220, by omega⟩
                        have hval : i.val + 27220 = n := by change n - 27220 + 27220 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 27220)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_27220_27239 i hlen'
                      ·
                        by_cases hcut : n < 27260
                        ·
                          let i : Fin 20 := ⟨n - 27240, by omega⟩
                          have hval : i.val + 27240 = n := by change n - 27240 + 27240 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 27240)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_27240_27259 i hlen'
                        ·
                          let i : Fin 20 := ⟨n - 27260, by omega⟩
                          have hval : i.val + 27260 = n := by change n - 27260 + 27260 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 27260)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_27260_27279 i hlen'
                  ·
                    by_cases hcut : n < 27340
                    ·
                      by_cases hcut : n < 27300
                      ·
                        let i : Fin 20 := ⟨n - 27280, by omega⟩
                        have hval : i.val + 27280 = n := by change n - 27280 + 27280 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 27280)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_27280_27299 i hlen'
                      ·
                        by_cases hcut : n < 27320
                        ·
                          let i : Fin 20 := ⟨n - 27300, by omega⟩
                          have hval : i.val + 27300 = n := by change n - 27300 + 27300 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 27300)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_27300_27319 i hlen'
                        ·
                          let i : Fin 20 := ⟨n - 27320, by omega⟩
                          have hval : i.val + 27320 = n := by change n - 27320 + 27320 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 27320)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_27320_27339 i hlen'
                    ·
                      by_cases hcut : n < 27360
                      ·
                        let i : Fin 20 := ⟨n - 27340, by omega⟩
                        have hval : i.val + 27340 = n := by change n - 27340 + 27340 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 27340)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_27340_27359 i hlen'
                      ·
                        by_cases hcut : n < 27380
                        ·
                          let i : Fin 20 := ⟨n - 27360, by omega⟩
                          have hval : i.val + 27360 = n := by change n - 27360 + 27360 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 27360)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_27360_27379 i hlen'
                        ·
                          let i : Fin 20 := ⟨n - 27380, by omega⟩
                          have hval : i.val + 27380 = n := by change n - 27380 + 27380 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 27380)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_27380_27399 i hlen'
              ·
                by_cases hcut : n < 27620
                ·
                  by_cases hcut : n < 27500
                  ·
                    by_cases hcut : n < 27440
                    ·
                      by_cases hcut : n < 27420
                      ·
                        let i : Fin 20 := ⟨n - 27400, by omega⟩
                        have hval : i.val + 27400 = n := by change n - 27400 + 27400 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 27400)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_27400_27419 i hlen'
                      ·
                        let i : Fin 20 := ⟨n - 27420, by omega⟩
                        have hval : i.val + 27420 = n := by change n - 27420 + 27420 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 27420)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_27420_27439 i hlen'
                    ·
                      by_cases hcut : n < 27460
                      ·
                        let i : Fin 20 := ⟨n - 27440, by omega⟩
                        have hval : i.val + 27440 = n := by change n - 27440 + 27440 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 27440)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_27440_27459 i hlen'
                      ·
                        by_cases hcut : n < 27480
                        ·
                          let i : Fin 20 := ⟨n - 27460, by omega⟩
                          have hval : i.val + 27460 = n := by change n - 27460 + 27460 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 27460)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_27460_27479 i hlen'
                        ·
                          let i : Fin 20 := ⟨n - 27480, by omega⟩
                          have hval : i.val + 27480 = n := by change n - 27480 + 27480 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 27480)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_27480_27499 i hlen'
                  ·
                    by_cases hcut : n < 27560
                    ·
                      by_cases hcut : n < 27520
                      ·
                        let i : Fin 20 := ⟨n - 27500, by omega⟩
                        have hval : i.val + 27500 = n := by change n - 27500 + 27500 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 27500)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_27500_27519 i hlen'
                      ·
                        by_cases hcut : n < 27540
                        ·
                          let i : Fin 20 := ⟨n - 27520, by omega⟩
                          have hval : i.val + 27520 = n := by change n - 27520 + 27520 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 27520)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_27520_27539 i hlen'
                        ·
                          let i : Fin 20 := ⟨n - 27540, by omega⟩
                          have hval : i.val + 27540 = n := by change n - 27540 + 27540 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 27540)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_27540_27559 i hlen'
                    ·
                      by_cases hcut : n < 27580
                      ·
                        let i : Fin 20 := ⟨n - 27560, by omega⟩
                        have hval : i.val + 27560 = n := by change n - 27560 + 27560 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 27560)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_27560_27579 i hlen'
                      ·
                        by_cases hcut : n < 27600
                        ·
                          let i : Fin 20 := ⟨n - 27580, by omega⟩
                          have hval : i.val + 27580 = n := by change n - 27580 + 27580 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 27580)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_27580_27599 i hlen'
                        ·
                          let i : Fin 20 := ⟨n - 27600, by omega⟩
                          have hval : i.val + 27600 = n := by change n - 27600 + 27600 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 27600)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_27600_27619 i hlen'
                ·
                  by_cases hcut : n < 27740
                  ·
                    by_cases hcut : n < 27680
                    ·
                      by_cases hcut : n < 27640
                      ·
                        let i : Fin 20 := ⟨n - 27620, by omega⟩
                        have hval : i.val + 27620 = n := by change n - 27620 + 27620 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 27620)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_27620_27639 i hlen'
                      ·
                        by_cases hcut : n < 27660
                        ·
                          let i : Fin 20 := ⟨n - 27640, by omega⟩
                          have hval : i.val + 27640 = n := by change n - 27640 + 27640 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 27640)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_27640_27659 i hlen'
                        ·
                          let i : Fin 20 := ⟨n - 27660, by omega⟩
                          have hval : i.val + 27660 = n := by change n - 27660 + 27660 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 27660)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_27660_27679 i hlen'
                    ·
                      by_cases hcut : n < 27700
                      ·
                        let i : Fin 20 := ⟨n - 27680, by omega⟩
                        have hval : i.val + 27680 = n := by change n - 27680 + 27680 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 27680)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_27680_27699 i hlen'
                      ·
                        by_cases hcut : n < 27720
                        ·
                          let i : Fin 20 := ⟨n - 27700, by omega⟩
                          have hval : i.val + 27700 = n := by change n - 27700 + 27700 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 27700)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_27700_27719 i hlen'
                        ·
                          let i : Fin 20 := ⟨n - 27720, by omega⟩
                          have hval : i.val + 27720 = n := by change n - 27720 + 27720 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 27720)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_27720_27739 i hlen'
                  ·
                    by_cases hcut : n < 27800
                    ·
                      by_cases hcut : n < 27760
                      ·
                        let i : Fin 20 := ⟨n - 27740, by omega⟩
                        have hval : i.val + 27740 = n := by change n - 27740 + 27740 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 27740)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_27740_27759 i hlen'
                      ·
                        by_cases hcut : n < 27780
                        ·
                          let i : Fin 20 := ⟨n - 27760, by omega⟩
                          have hval : i.val + 27760 = n := by change n - 27760 + 27760 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 27760)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_27760_27779 i hlen'
                        ·
                          let i : Fin 20 := ⟨n - 27780, by omega⟩
                          have hval : i.val + 27780 = n := by change n - 27780 + 27780 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 27780)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_27780_27799 i hlen'
                    ·
                      by_cases hcut : n < 27820
                      ·
                        let i : Fin 20 := ⟨n - 27800, by omega⟩
                        have hval : i.val + 27800 = n := by change n - 27800 + 27800 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 27800)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_27800_27819 i hlen'
                      ·
                        by_cases hcut : n < 27840
                        ·
                          let i : Fin 20 := ⟨n - 27820, by omega⟩
                          have hval : i.val + 27820 = n := by change n - 27820 + 27820 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 27820)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_27820_27839 i hlen'
                        ·
                          let i : Fin 20 := ⟨n - 27840, by omega⟩
                          have hval : i.val + 27840 = n := by change n - 27840 + 27840 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 27840)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_27840_27859 i hlen'
            ·
              by_cases hcut : n < 28300
              ·
                by_cases hcut : n < 28080
                ·
                  by_cases hcut : n < 27960
                  ·
                    by_cases hcut : n < 27900
                    ·
                      by_cases hcut : n < 27880
                      ·
                        let i : Fin 20 := ⟨n - 27860, by omega⟩
                        have hval : i.val + 27860 = n := by change n - 27860 + 27860 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 27860)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_27860_27879 i hlen'
                      ·
                        let i : Fin 20 := ⟨n - 27880, by omega⟩
                        have hval : i.val + 27880 = n := by change n - 27880 + 27880 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 27880)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_27880_27899 i hlen'
                    ·
                      by_cases hcut : n < 27920
                      ·
                        let i : Fin 20 := ⟨n - 27900, by omega⟩
                        have hval : i.val + 27900 = n := by change n - 27900 + 27900 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 27900)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_27900_27919 i hlen'
                      ·
                        by_cases hcut : n < 27940
                        ·
                          let i : Fin 20 := ⟨n - 27920, by omega⟩
                          have hval : i.val + 27920 = n := by change n - 27920 + 27920 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 27920)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_27920_27939 i hlen'
                        ·
                          let i : Fin 20 := ⟨n - 27940, by omega⟩
                          have hval : i.val + 27940 = n := by change n - 27940 + 27940 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 27940)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_27940_27959 i hlen'
                  ·
                    by_cases hcut : n < 28020
                    ·
                      by_cases hcut : n < 27980
                      ·
                        let i : Fin 20 := ⟨n - 27960, by omega⟩
                        have hval : i.val + 27960 = n := by change n - 27960 + 27960 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 27960)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_27960_27979 i hlen'
                      ·
                        by_cases hcut : n < 28000
                        ·
                          let i : Fin 20 := ⟨n - 27980, by omega⟩
                          have hval : i.val + 27980 = n := by change n - 27980 + 27980 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 27980)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_27980_27999 i hlen'
                        ·
                          let i : Fin 20 := ⟨n - 28000, by omega⟩
                          have hval : i.val + 28000 = n := by change n - 28000 + 28000 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 28000)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_28000_28019 i hlen'
                    ·
                      by_cases hcut : n < 28040
                      ·
                        let i : Fin 20 := ⟨n - 28020, by omega⟩
                        have hval : i.val + 28020 = n := by change n - 28020 + 28020 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 28020)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_28020_28039 i hlen'
                      ·
                        by_cases hcut : n < 28060
                        ·
                          let i : Fin 20 := ⟨n - 28040, by omega⟩
                          have hval : i.val + 28040 = n := by change n - 28040 + 28040 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 28040)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_28040_28059 i hlen'
                        ·
                          let i : Fin 20 := ⟨n - 28060, by omega⟩
                          have hval : i.val + 28060 = n := by change n - 28060 + 28060 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 28060)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_28060_28079 i hlen'
                ·
                  by_cases hcut : n < 28180
                  ·
                    by_cases hcut : n < 28120
                    ·
                      by_cases hcut : n < 28100
                      ·
                        let i : Fin 20 := ⟨n - 28080, by omega⟩
                        have hval : i.val + 28080 = n := by change n - 28080 + 28080 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 28080)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_28080_28099 i hlen'
                      ·
                        let i : Fin 20 := ⟨n - 28100, by omega⟩
                        have hval : i.val + 28100 = n := by change n - 28100 + 28100 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 28100)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_28100_28119 i hlen'
                    ·
                      by_cases hcut : n < 28140
                      ·
                        let i : Fin 20 := ⟨n - 28120, by omega⟩
                        have hval : i.val + 28120 = n := by change n - 28120 + 28120 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 28120)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_28120_28139 i hlen'
                      ·
                        by_cases hcut : n < 28160
                        ·
                          let i : Fin 20 := ⟨n - 28140, by omega⟩
                          have hval : i.val + 28140 = n := by change n - 28140 + 28140 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 28140)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_28140_28159 i hlen'
                        ·
                          let i : Fin 20 := ⟨n - 28160, by omega⟩
                          have hval : i.val + 28160 = n := by change n - 28160 + 28160 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 28160)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_28160_28179 i hlen'
                  ·
                    by_cases hcut : n < 28240
                    ·
                      by_cases hcut : n < 28200
                      ·
                        let i : Fin 20 := ⟨n - 28180, by omega⟩
                        have hval : i.val + 28180 = n := by change n - 28180 + 28180 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 28180)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_28180_28199 i hlen'
                      ·
                        by_cases hcut : n < 28220
                        ·
                          let i : Fin 20 := ⟨n - 28200, by omega⟩
                          have hval : i.val + 28200 = n := by change n - 28200 + 28200 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 28200)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_28200_28219 i hlen'
                        ·
                          let i : Fin 20 := ⟨n - 28220, by omega⟩
                          have hval : i.val + 28220 = n := by change n - 28220 + 28220 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 28220)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_28220_28239 i hlen'
                    ·
                      by_cases hcut : n < 28260
                      ·
                        let i : Fin 20 := ⟨n - 28240, by omega⟩
                        have hval : i.val + 28240 = n := by change n - 28240 + 28240 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 28240)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_28240_28259 i hlen'
                      ·
                        by_cases hcut : n < 28280
                        ·
                          let i : Fin 20 := ⟨n - 28260, by omega⟩
                          have hval : i.val + 28260 = n := by change n - 28260 + 28260 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 28260)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_28260_28279 i hlen'
                        ·
                          let i : Fin 20 := ⟨n - 28280, by omega⟩
                          have hval : i.val + 28280 = n := by change n - 28280 + 28280 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 28280)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_28280_28299 i hlen'
              ·
                by_cases hcut : n < 28520
                ·
                  by_cases hcut : n < 28400
                  ·
                    by_cases hcut : n < 28340
                    ·
                      by_cases hcut : n < 28320
                      ·
                        let i : Fin 20 := ⟨n - 28300, by omega⟩
                        have hval : i.val + 28300 = n := by change n - 28300 + 28300 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 28300)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_28300_28319 i hlen'
                      ·
                        let i : Fin 20 := ⟨n - 28320, by omega⟩
                        have hval : i.val + 28320 = n := by change n - 28320 + 28320 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 28320)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_28320_28339 i hlen'
                    ·
                      by_cases hcut : n < 28360
                      ·
                        let i : Fin 20 := ⟨n - 28340, by omega⟩
                        have hval : i.val + 28340 = n := by change n - 28340 + 28340 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 28340)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_28340_28359 i hlen'
                      ·
                        by_cases hcut : n < 28380
                        ·
                          let i : Fin 20 := ⟨n - 28360, by omega⟩
                          have hval : i.val + 28360 = n := by change n - 28360 + 28360 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 28360)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_28360_28379 i hlen'
                        ·
                          let i : Fin 20 := ⟨n - 28380, by omega⟩
                          have hval : i.val + 28380 = n := by change n - 28380 + 28380 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 28380)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_28380_28399 i hlen'
                  ·
                    by_cases hcut : n < 28460
                    ·
                      by_cases hcut : n < 28420
                      ·
                        let i : Fin 20 := ⟨n - 28400, by omega⟩
                        have hval : i.val + 28400 = n := by change n - 28400 + 28400 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 28400)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_28400_28419 i hlen'
                      ·
                        by_cases hcut : n < 28440
                        ·
                          let i : Fin 20 := ⟨n - 28420, by omega⟩
                          have hval : i.val + 28420 = n := by change n - 28420 + 28420 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 28420)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_28420_28439 i hlen'
                        ·
                          let i : Fin 20 := ⟨n - 28440, by omega⟩
                          have hval : i.val + 28440 = n := by change n - 28440 + 28440 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 28440)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_28440_28459 i hlen'
                    ·
                      by_cases hcut : n < 28480
                      ·
                        let i : Fin 20 := ⟨n - 28460, by omega⟩
                        have hval : i.val + 28460 = n := by change n - 28460 + 28460 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 28460)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_28460_28479 i hlen'
                      ·
                        by_cases hcut : n < 28500
                        ·
                          let i : Fin 20 := ⟨n - 28480, by omega⟩
                          have hval : i.val + 28480 = n := by change n - 28480 + 28480 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 28480)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_28480_28499 i hlen'
                        ·
                          let i : Fin 20 := ⟨n - 28500, by omega⟩
                          have hval : i.val + 28500 = n := by change n - 28500 + 28500 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 28500)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_28500_28519 i hlen'
                ·
                  by_cases hcut : n < 28640
                  ·
                    by_cases hcut : n < 28580
                    ·
                      by_cases hcut : n < 28540
                      ·
                        let i : Fin 20 := ⟨n - 28520, by omega⟩
                        have hval : i.val + 28520 = n := by change n - 28520 + 28520 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 28520)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_28520_28539 i hlen'
                      ·
                        by_cases hcut : n < 28560
                        ·
                          let i : Fin 20 := ⟨n - 28540, by omega⟩
                          have hval : i.val + 28540 = n := by change n - 28540 + 28540 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 28540)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_28540_28559 i hlen'
                        ·
                          let i : Fin 20 := ⟨n - 28560, by omega⟩
                          have hval : i.val + 28560 = n := by change n - 28560 + 28560 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 28560)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_28560_28579 i hlen'
                    ·
                      by_cases hcut : n < 28600
                      ·
                        let i : Fin 20 := ⟨n - 28580, by omega⟩
                        have hval : i.val + 28580 = n := by change n - 28580 + 28580 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 28580)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_28580_28599 i hlen'
                      ·
                        by_cases hcut : n < 28620
                        ·
                          let i : Fin 20 := ⟨n - 28600, by omega⟩
                          have hval : i.val + 28600 = n := by change n - 28600 + 28600 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 28600)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_28600_28619 i hlen'
                        ·
                          let i : Fin 20 := ⟨n - 28620, by omega⟩
                          have hval : i.val + 28620 = n := by change n - 28620 + 28620 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 28620)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_28620_28639 i hlen'
                  ·
                    by_cases hcut : n < 28700
                    ·
                      by_cases hcut : n < 28660
                      ·
                        let i : Fin 20 := ⟨n - 28640, by omega⟩
                        have hval : i.val + 28640 = n := by change n - 28640 + 28640 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 28640)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_28640_28659 i hlen'
                      ·
                        by_cases hcut : n < 28680
                        ·
                          let i : Fin 20 := ⟨n - 28660, by omega⟩
                          have hval : i.val + 28660 = n := by change n - 28660 + 28660 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 28660)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_28660_28679 i hlen'
                        ·
                          let i : Fin 20 := ⟨n - 28680, by omega⟩
                          have hval : i.val + 28680 = n := by change n - 28680 + 28680 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 28680)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_28680_28699 i hlen'
                    ·
                      by_cases hcut : n < 28720
                      ·
                        let i : Fin 20 := ⟨n - 28700, by omega⟩
                        have hval : i.val + 28700 = n := by change n - 28700 + 28700 = n; omega
                        have hlen' : 1 < (fastFactors (i.val + 28700)).length := by simpa [hval] using hlen
                        simpa [hval] using fast_no_zero_28700_28719 i hlen'
                      ·
                        by_cases hcut : n < 28740
                        ·
                          let i : Fin 20 := ⟨n - 28720, by omega⟩
                          have hval : i.val + 28720 = n := by change n - 28720 + 28720 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 28720)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_28720_28739 i hlen'
                        ·
                          let i : Fin 9 := ⟨n - 28740, by omega⟩
                          have hval : i.val + 28740 = n := by change n - 28740 + 28740 = n; omega
                          have hlen' : 1 < (fastFactors (i.val + 28740)).length := by simpa [hval] using hlen
                          simpa [hval] using fast_no_zero_28740_28748 i hlen'
