import FormalConjectures.Util.ProblemImports

open Finset Nat

/--
A193279: Number of distinct sums of distinct proper divisors of $n$.
The count excludes an empty subset of proper divisors that would give $0$ as a sum.
-/
def A193279 (n : ℕ) : ℕ :=
  let D := properDivisors n
  -- The set of all distinct sums of subsets of D, including the sum of the empty set (0).
  let S := D.powerset.image (fun s : Finset ℕ => s.sum id)
  -- The number of distinct sums, minus the single sum 0 from the empty set.
  S.card - 1

-- subset sums of D as a Finset
noncomputable def SS (D : Finset ℕ) : Finset ℕ := D.powerset.image (fun s : Finset ℕ => s.sum id)

theorem SS_empty : SS ∅ = {0} := by
  simp [SS]

theorem SS_insert {a : ℕ} {D : Finset ℕ} (ha : a ∉ D) :
    SS (insert a D) = SS D ∪ (SS D).image (· + a) := by
  unfold SS
  rw [Finset.powerset_insert, Finset.image_union]
  congr 1
  rw [Finset.image_image, Finset.image_image]
  apply Finset.image_congr
  intro s hs
  simp only [Finset.coe_powerset, Set.mem_preimage, Set.mem_powerset_iff, Finset.coe_subset] at hs
  have : a ∉ s := fun h => ha (hs h)
  simp only [Function.comp_apply, Finset.sum_insert this, id, add_comm]

-- key interval union lemma
theorem interval_union {T a : ℕ} (h : a ≤ T + 1) :
    range (T + 1) ∪ (range (T + 1)).image (· + a) = range (T + a + 1) := by
  apply Finset.ext
  intro x
  simp only [Finset.mem_union, Finset.mem_image, Finset.mem_range]
  constructor
  · rintro (hx | ⟨y, hy, rfl⟩)
    · omega
    · omega
  · intro hx
    by_cases hxa : x < a
    · left; omega
    · right; exact ⟨x - a, by omega, by omega⟩

theorem geom2 (m : ℕ) : ∑ i ∈ range m, 2^i = 2^m - 1 := by
  induction m with
  | zero => simp
  | succ j ih => rw [Finset.sum_range_succ, ih]; have : 1 ≤ 2^j := Nat.one_le_two_pow
                 rw [pow_succ]; omega

theorem pow_inj : Function.Injective (fun j : ℕ => (2:ℕ)^j) := by
  intro a b h; simpa using Nat.pow_right_injective (le_refl 2) h

theorem powq_inj (q : ℕ) (hq : 0 < q) : Function.Injective (fun j : ℕ => (2:ℕ)^j*q) := by
  intro a b h; simp only at h
  exact Nat.pow_right_injective (le_refl 2) (Nat.eq_of_mul_eq_mul_right hq h)

section Euler
open ArithmeticFunction
open scoped sigma

theorem sigma_two_pow_eq_mersenne_succ (k : ℕ) : σ 1 (2 ^ k) = mersenne (k + 1) := by
  simp_rw [sigma_one_apply, mersenne, ← one_add_one_eq_two, ← geom_sum_mul_add 1 (k + 1)]
  norm_num

theorem eq_two_pow_mul_odd {n : ℕ} (hpos : 0 < n) : ∃ k m : ℕ, n = 2 ^ k * m ∧ ¬Even m := by
  have h := Nat.finiteMultiplicity_iff.2 ⟨Nat.prime_two.ne_one, hpos⟩
  obtain ⟨m, hm⟩ := pow_multiplicity_dvd 2 n
  use multiplicity 2 n, m
  refine ⟨hm, ?_⟩
  rw [even_iff_two_dvd]
  have hg := h.not_pow_dvd_of_multiplicity_lt (Nat.lt_succ_self _)
  contrapose! hg
  rcases hg with ⟨k, rfl⟩
  apply Dvd.intro k
  rw [pow_succ, mul_assoc, ← hm]

theorem eq_two_pow_mul_prime_mersenne_of_even_perfect {n : ℕ} (ev : Even n) (perf : Nat.Perfect n) :
    ∃ k : ℕ, Nat.Prime (mersenne (k + 1)) ∧ n = 2 ^ k * mersenne (k + 1) := by
  have hpos := perf.2
  rcases eq_two_pow_mul_odd hpos with ⟨k, m, rfl, hm⟩
  use k
  rw [even_iff_two_dvd] at hm
  rw [Nat.perfect_iff_sum_divisors_eq_two_mul hpos, ← sigma_one_apply,
    isMultiplicative_sigma.map_mul_of_coprime (Nat.prime_two.coprime_pow_of_not_dvd hm).symm,
    sigma_two_pow_eq_mersenne_succ, ← mul_assoc, ← pow_succ'] at perf
  obtain ⟨j, rfl⟩ := ((Odd.coprime_two_right (by simp)).pow_right _).dvd_of_dvd_mul_left
    (Dvd.intro _ perf)
  rw [← mul_assoc, mul_comm _ (mersenne _), mul_assoc] at perf
  have h := mul_left_cancel₀ (by positivity) perf
  rw [sigma_one_apply, Nat.sum_divisors_eq_sum_properDivisors_add_self, ← succ_mersenne, add_mul,
    one_mul, add_comm] at h
  have hj := add_left_cancel h
  cases Nat.sum_properDivisors_dvd (by rw [hj]; apply Dvd.intro_left (mersenne (k + 1)) rfl) with
  | inl h_1 =>
    have j1 : j = 1 := Eq.trans hj.symm h_1
    rw [j1, mul_one, Nat.sum_properDivisors_eq_one_iff_prime] at h_1
    simp [h_1, j1]
  | inr h_1 =>
    have jcon := Eq.trans hj.symm h_1
    rw [← one_mul j, ← mul_assoc, mul_one] at jcon
    have jcon2 := mul_right_cancel₀ ?_ jcon
    · exfalso
      match k with
      | 0 =>
        apply hm
        rw [← jcon2, pow_zero, one_mul, one_mul] at ev
        rw [← jcon2, one_mul]
        exact even_iff_two_dvd.mp ev
      | .succ k =>
        apply _root_.ne_of_lt _ jcon2
        rw [mersenne, ← Nat.pred_eq_sub_one, Nat.lt_pred_iff, ← pow_one (Nat.succ 1)]
        apply pow_lt_pow_right₀ (Nat.lt_succ_self 1) (Nat.succ_lt_succ k.succ_pos)
    contrapose! hm
    simp [hm]

end Euler

theorem covering (D : Finset ℕ)
    (h : ∀ d ∈ D, d ≤ 1 + ∑ e ∈ D.filter (· < d), e) :
    SS D = range (D.sum id + 1) := by
  induction D using Finset.strongInductionOn with
  | _ D IH =>
    rcases D.eq_empty_or_nonempty with rfl | hne
    · simp [SS_empty]
    · set a := D.max' hne with ha_def
      have ha_mem : a ∈ D := D.max'_mem hne
      set D' := D.erase a with hD'_def
      have ha_not : a ∉ D' := Finset.notMem_erase a D
      have hins : D = insert a D' := by
        rw [hD'_def, Finset.insert_erase ha_mem]
      -- all elements of D' are < a
      have hlt : ∀ e ∈ D', e < a := by
        intro e he
        have he' : e ∈ D := Finset.mem_of_mem_erase he
        have hne_a : e ≠ a := Finset.ne_of_mem_erase he
        have : e ≤ a := D.le_max' e he'
        omega
      -- hypothesis for D'
      have hD' : ∀ d ∈ D', d ≤ 1 + ∑ e ∈ D'.filter (· < d), e := by
        intro d hd
        have hdD : d ∈ D := Finset.mem_of_mem_erase hd
        have := h d hdD
        have hfilter : D'.filter (· < d) = D.filter (· < d) := by
          rw [hD'_def, Finset.filter_erase]
          rw [Finset.erase_eq_of_notMem]
          simp only [Finset.mem_filter]
          rintro ⟨_, had⟩
          -- a < d but d ≤ a since a is max
          have : d ≤ a := D.le_max' d hdD
          omega
        rw [hfilter]; exact this
      have IH' := IH D' (Finset.erase_ssubset ha_mem) hD'
      -- now compute SS D
      rw [hins, SS_insert ha_not, IH']
      -- need: a ≤ D'.sum id + 1
      have hfilter_a : D.filter (· < a) = D' := by
        apply Finset.ext
        intro x
        simp only [Finset.mem_filter, hD'_def, Finset.mem_erase]
        constructor
        · rintro ⟨hxD, hxa⟩; exact ⟨by omega, hxD⟩
        · rintro ⟨hxa, hxD⟩; exact ⟨hxD, hlt x (by rw [hD'_def, Finset.mem_erase]; exact ⟨hxa, hxD⟩)⟩
      have hcond := h a ha_mem
      rw [hfilter_a] at hcond
      -- hcond : a ≤ 1 + ∑ e ∈ D', e
      have hsum_eq : (∑ e ∈ D', e) = D'.sum id := by simp [id]
      have ha_le : a ≤ D'.sum id + 1 := by rw [← hsum_eq]; omega
      rw [interval_union ha_le]
      congr 1
      -- D'.sum id + a = (insert a D').sum id
      rw [Finset.sum_insert ha_not]
      simp [id]
      omega

-- characterization of proper divisors of 2^k * q where q = 2^(k+1)-1 prime
theorem mem_pd {k q : ℕ} (hq : q.Prime) (hqval : q + 1 = 2^(k+1)) (m : ℕ) :
    m ∈ (2^k * q).properDivisors ↔ (∃ i ≤ k, m = 2^i) ∨ (∃ i < k, m = 2^i * q) := by
  have hq2 : 2 ≤ q := hq.two_le
  have hqgt : 2^k < q := by
    have : 2^(k+1) = 2*2^k := by rw [pow_succ]; ring
    omega
  have hn : 0 < 2^k * q := by positivity
  rw [Nat.mem_properDivisors]
  constructor
  · rintro ⟨hdvd, hlt⟩
    rw [Nat.dvd_mul] at hdvd
    obtain ⟨a, b, ha, hb, hab⟩ := hdvd
    rw [Nat.dvd_prime_pow Nat.prime_two] at ha
    obtain ⟨i, hik, rfl⟩ := ha
    rcases (Nat.dvd_prime hq).mp hb with hb1 | hbq
    · subst hb1
      left; exact ⟨i, hik, by omega⟩
    · rw [hbq] at hab
      right
      refine ⟨i, ?_, by rw [← hab]⟩
      -- m = 2^i * q < 2^k * q ⟹ i < k
      rw [← hab] at hlt
      have : 2^i < 2^k := by
        by_contra hcon
        push_neg at hcon
        have : 2^k * q ≤ 2^i * q := Nat.mul_le_mul_right q hcon
        omega
      exact (Nat.pow_lt_pow_iff_right (by norm_num)).mp this
  · rintro (⟨i, hik, rfl⟩ | ⟨i, hik, rfl⟩)
    · constructor
      · exact dvd_mul_of_dvd_left (pow_dvd_pow 2 hik) q
      · have h1 : 2^i ≤ 2^k := Nat.pow_le_pow_right (by norm_num) hik
        have h2 : 2^k < 2^k * q := by nlinarith [Nat.one_le_two_pow (n := k)]
        omega
    · constructor
      · exact mul_dvd_mul_right (pow_dvd_pow 2 (le_of_lt hik)) q
      · have hlt2 : 2^i < 2^k := (Nat.pow_lt_pow_iff_right (by norm_num)).mpr hik
        exact (Nat.mul_lt_mul_right (by omega)).mpr hlt2

theorem hyp {k q : ℕ} (hq : q.Prime) (hqval : q + 1 = 2^(k+1)) :
    ∀ d ∈ (2^k*q).properDivisors,
      d ≤ 1 + ∑ e ∈ (2^k*q).properDivisors.filter (· < d), e := by
  have hq2 : 2 ≤ q := hq.two_le
  have hqgt : 2^k < q := by
    have : 2^(k+1) = 2*2^k := by rw [pow_succ]; ring
    omega
  have hq0 : 0 < q := by omega
  intro d hd
  rw [mem_pd hq hqval] at hd
  rcases hd with ⟨i, hik, rfl⟩ | ⟨i, hik, rfl⟩
  · -- d = 2^i, i ≤ k
    set E : Finset ℕ := (range i).image (fun j => 2^j) with hE
    have hsumE : ∑ e ∈ E, e = 2^i - 1 := by
      rw [hE, Finset.sum_image (fun x _ y _ h => pow_inj h)]
      exact geom2 i
    have hsub : E ⊆ (2^k*q).properDivisors.filter (· < 2^i) := by
      intro x hx
      rw [hE, Finset.mem_image] at hx
      obtain ⟨j, hj, rfl⟩ := hx
      rw [Finset.mem_range] at hj
      rw [Finset.mem_filter, mem_pd hq hqval]
      refine ⟨Or.inl ⟨j, by omega, rfl⟩, ?_⟩
      exact (Nat.pow_lt_pow_iff_right (by norm_num)).mpr hj
    have hle := Finset.sum_le_sum_of_subset (f := fun e => e) hsub
    rw [hsumE] at hle
    simp only at hle
    have : 1 ≤ 2^i := Nat.one_le_two_pow
    omega
  · -- d = 2^i * q, i < k
    set E1 : Finset ℕ := (range (k+1)).image (fun j => 2^j) with hE1
    set E2 : Finset ℕ := (range i).image (fun j => 2^j * q) with hE2
    have hdisj : Disjoint E1 E2 := by
      rw [Finset.disjoint_left]
      intro a ha1 ha2
      rw [hE1, Finset.mem_image] at ha1
      obtain ⟨j, hj, rfl⟩ := ha1
      rw [Finset.mem_range] at hj
      rw [hE2, Finset.mem_image] at ha2
      obtain ⟨j', hj', heq⟩ := ha2
      rw [Finset.mem_range] at hj'
      have hjk : 2^j ≤ 2^k := Nat.pow_le_pow_right (by norm_num) (by omega)
      have : q ≤ 2^j' * q := Nat.le_mul_of_pos_left q (by positivity)
      omega
    have hsumE1 : ∑ e ∈ E1, e = q := by
      rw [hE1, Finset.sum_image (fun x _ y _ h => pow_inj h), geom2 (k+1)]
      omega
    have hsumE2 : ∑ e ∈ E2, e = (2^i - 1) * q := by
      rw [hE2, Finset.sum_image (fun x _ y _ h => powq_inj q hq0 h)]
      rw [← Finset.sum_mul, geom2 i]
    have hsumE : ∑ e ∈ E1 ∪ E2, e = 2^i * q := by
      rw [Finset.sum_union hdisj, hsumE1, hsumE2]
      have h1 : 1 ≤ 2^i := Nat.one_le_two_pow
      have h2 : (2^i - 1) * q = 2^i * q - q := by rw [Nat.sub_mul, one_mul]
      rw [h2]
      have h3 : q ≤ 2^i * q := Nat.le_mul_of_pos_left q (by positivity)
      omega
    have hsub : E1 ∪ E2 ⊆ (2^k*q).properDivisors.filter (· < 2^i * q) := by
      intro x hx
      rw [Finset.mem_union] at hx
      rw [Finset.mem_filter, mem_pd hq hqval]
      have hdpos : 0 < 2^i * q := by positivity
      rcases hx with hx | hx
      · rw [hE1, Finset.mem_image] at hx
        obtain ⟨j, hj, rfl⟩ := hx
        rw [Finset.mem_range] at hj
        have hjk : 2^j ≤ 2^k := Nat.pow_le_pow_right (by norm_num) (by omega)
        have hqle : q ≤ 2^i * q := Nat.le_mul_of_pos_left q (by positivity)
        exact ⟨Or.inl ⟨j, by omega, rfl⟩, by omega⟩
      · rw [hE2, Finset.mem_image] at hx
        obtain ⟨j, hj, rfl⟩ := hx
        rw [Finset.mem_range] at hj
        refine ⟨Or.inr ⟨j, by omega, rfl⟩, ?_⟩
        have : 2^j < 2^i := (Nat.pow_lt_pow_iff_right (by norm_num)).mpr (by omega)
        exact (Nat.mul_lt_mul_right hq0).mpr this
    have hle := Finset.sum_le_sum_of_subset (f := fun e => e) hsub
    rw [hsumE] at hle
    simp only at hle
    omega

/--
%C A193279 a(n)=n if n is an even perfect number (is the converse true?)
-/
theorem oeis_193279_conjecture_0 (n : ℕ) :
  (Nat.Perfect n ∧ Even n) → A193279 n = n := by
  rintro ⟨perf, ev⟩
  obtain ⟨k, hqprime, hn⟩ := eq_two_pow_mul_prime_mersenne_of_even_perfect ev perf
  have hqval : mersenne (k+1) + 1 = 2^(k+1) := succ_mersenne (k+1)
  subst hn
  have hpos : 0 < 2^k * mersenne (k+1) := perf.2
  have hsum : ∑ e ∈ (2^k * mersenne (k+1)).properDivisors, e = 2^k * mersenne (k+1) :=
    (Nat.perfect_iff_sum_properDivisors hpos).mp perf
  have hcov := covering ((2^k * mersenne (k+1)).properDivisors) (hyp hqprime hqval)
  unfold SS at hcov
  have hsumid : (2^k * mersenne (k+1)).properDivisors.sum id = 2^k * mersenne (k+1) := hsum
  rw [hsumid] at hcov
  unfold A193279
  simp only [hcov, Finset.card_range]
  omega
