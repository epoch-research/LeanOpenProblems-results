import Submission.Work

/-!
Finite estimates for a constructive lower-bound approach. These do not yet give a
superquadratic family and do not settle the conjecture.
-/
namespace Erdos970.ConstructiveCover

noncomputable def sift (R P : Finset ℕ) (r : ℕ → ℕ) : Finset ℕ :=
  R.filter (fun i => ∀ p ∈ P, ¬i ≡ r p [MOD p])

theorem exists_efficient_residue (R : Finset ℕ) {p : ℕ} (hp : 0 < p) :
    ∃ j < p, p * (R.filter (fun i => ¬i ≡ j [MOD p])).card ≤ (p - 1) * R.card := by
  classical
  have hsum : ∑ j ∈ Finset.range p, (R.filter (fun i => i % p = j)).card = R.card := by
    symm
    apply Finset.card_eq_sum_card_fiberwise
    intro i hi
    exact Finset.mem_range.mpr (Nat.mod_lt i hp)
  have hex : ∃ j ∈ Finset.range p,
      R.card ≤ p * (R.filter (fun i => i % p = j)).card := by
    by_contra h
    push_neg at h
    have hh : (∑ j ∈ Finset.range p, p * (R.filter (fun i => i % p = j)).card) <
        ∑ j ∈ Finset.range p, R.card := by
      apply Finset.sum_lt_sum
      · intro j hj
        exact (h j hj).le
      · exact ⟨0, Finset.mem_range.mpr hp, h 0 (Finset.mem_range.mpr hp)⟩
    rw [← Finset.mul_sum, hsum] at hh
    simp at hh
  obtain ⟨j, hj, hjc⟩ := hex
  have hjlt : j < p := Finset.mem_range.mp hj
  have hcard := Finset.card_filter_add_card_filter_not (s := R) (fun i => i % p = j)
  have heq : (R.filter (fun i => ¬i ≡ j [MOD p])) =
      R.filter (fun i => ¬i % p = j) := by
    simp only [Nat.ModEq, Nat.mod_eq_of_lt hjlt]
  refine ⟨j, hjlt, ?_⟩
  rw [heq]
  have hsub : p - 1 + 1 = p := by omega
  nlinarith

/-- A finite greedy sieve achieves at least the product-density removal. -/
theorem exists_sift_card_le (P : Finset ℕ) (hP : ∀ p ∈ P, 0 < p) (R : Finset ℕ) :
    ∃ r : ℕ → ℕ,
      (∏ p ∈ P, p) * (sift R P r).card ≤ (∏ p ∈ P, (p - 1)) * R.card := by
  classical
  induction P using Finset.induction_on generalizing R with
  | empty =>
    exact ⟨fun _ => 0, by simp [sift]⟩
  | @insert p P hp ih =>
    obtain ⟨r, hr⟩ := ih (fun q hq => hP q (Finset.mem_insert_of_mem hq)) R
    obtain ⟨j, hj, hjc⟩ := exists_efficient_residue (sift R P r)
      (hP p (Finset.mem_insert_self _ _))
    let r' : ℕ → ℕ := fun q => if q = p then j else r q
    have heq : sift R (insert p P) r' =
        (sift R P r).filter (fun i => ¬i ≡ j [MOD p]) := by
      ext i
      simp only [sift, Finset.mem_filter, Finset.mem_insert]
      constructor
      · rintro ⟨hiR, hi⟩
        refine ⟨⟨hiR, ?_⟩, ?_⟩
        · intro q hq
          have hqp : q ≠ p := by intro he; exact hp (he ▸ hq)
          simpa [r', hqp] using hi q (Or.inr hq)
        · simpa [r'] using hi p (Or.inl rfl)
      · rintro ⟨⟨hiR, hiP⟩, hip⟩
        refine ⟨hiR, fun q hq => ?_⟩
        rcases hq with rfl | hq
        · simpa [r'] using hip
        · have hqp : q ≠ p := by intro he; exact hp (he ▸ hq)
          simpa [r', hqp] using hiP q hq
    refine ⟨r', ?_⟩
    rw [heq, Finset.prod_insert hp, Finset.prod_insert hp]
    calc
      (p * ∏ q ∈ P, q) * ((sift R P r).filter (fun i => ¬i ≡ j [MOD p])).card =
          (∏ q ∈ P, q) * (p * ((sift R P r).filter (fun i => ¬i ≡ j [MOD p])).card) := by ring
      _ ≤ (∏ q ∈ P, q) * ((p - 1) * (sift R P r).card) := Nat.mul_le_mul_left _ hjc
      _ = (p - 1) * ((∏ q ∈ P, q) * (sift R P r).card) := by ring
      _ ≤ (p - 1) * ((∏ q ∈ P, (q - 1)) * R.card) := Nat.mul_le_mul_left _ hr
      _ = _ := by ring

/-- A greedy second sieve, followed by one fresh prime per hole, gives an explicit budget. -/
theorem not_bound_of_greedy_budget (m : ℕ) (P S : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (hS : ∀ p ∈ S, p.Prime)
    (hdis : Disjoint P S) (r₀ : ℕ → ℕ) :
    ¬IsJacobsthalBound
      (P.card + S.card +
        ((∏ p ∈ S, (p - 1)) * (sift (Finset.range m) P r₀).card) / (∏ p ∈ S, p)) m := by
  classical
  let R := sift (Finset.range m) P r₀
  obtain ⟨r, hr⟩ := exists_sift_card_le S (fun p hp => (hS p hp).pos) R
  let U := sift R S r
  let t : ℕ → ℕ := fun p => if p ∈ S then r p else r₀ p
  have hprod : 0 < ∏ p ∈ S, p := Finset.prod_pos (fun p hp => (hS p hp).pos)
  have hcard : U.card ≤ ((∏ p ∈ S, (p - 1)) * R.card) / (∏ p ∈ S, p) := by
    apply (Nat.le_div_iff_mul_le hprod).mpr
    simpa only [Nat.mul_comm] using hr
  have hcover : ∀ i : ℕ, i < m → i ∉ U → ∃ p ∈ P ∪ S, i ≡ t p [MOD p] := by
    intro i hi hiU
    by_cases hiR : i ∈ R
    · have hnot : ¬∀ p ∈ S, ¬i ≡ r p [MOD p] := by
        intro hh
        exact hiU (Finset.mem_filter.mpr ⟨hiR, hh⟩)
      push_neg at hnot
      obtain ⟨p, hp, hip⟩ := hnot
      exact ⟨p, Finset.mem_union_right P hp, by simpa [t, hp] using hip⟩
    · have hnot : ¬∀ p ∈ P, ¬i ≡ r₀ p [MOD p] := by
        intro hh
        exact hiR (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hi, hh⟩)
      push_neg at hnot
      obtain ⟨p, hp, hip⟩ := hnot
      have hpS : p ∉ S := fun hh => Finset.disjoint_left.mp hdis hp hh
      exact ⟨p, Finset.mem_union_left S hp, by simpa [t, hpS] using hip⟩
  have hPS : ∀ p ∈ P ∪ S, p.Prime := by
    intro p hp
    rcases Finset.mem_union.mp hp with hp | hp
    · exact hP p hp
    · exact hS p hp
  obtain ⟨Q, hQ, hQc, v, hv⟩ := extend_cover_by_fresh_primes m U (P ∪ S) hPS t hcover
  apply (not_isJacobsthalBound_iff_cover _ m).mpr
  refine ⟨Q, hQ, ?_, v, hv⟩
  rw [Finset.card_union_of_disjoint hdis] at hQc
  exact hQc.trans (Nat.add_le_add_left hcard _)

/-- With zero classes outside a fixed exceptional prime set, surviving composites are smooth. -/
theorem prime_or_smooth {S : Finset ℕ} {A X i : ℕ}
    (hAX : A ≤ X) (hS : ∀ p ∈ S, A < p)
    (hi : 0 < i) (hiAX : i ≤ A * X)
    (havoid : ∀ p : ℕ, p.Prime → p ≤ X → p ∉ S → ¬p ∣ i) :
    i.Prime ∨ i.primeFactors ⊆ S := by
  by_cases hprime : i.Prime
  · exact Or.inl hprime
  right
  intro q hq
  by_contra hqS
  obtain ⟨hqprime, hqi, _⟩ := Nat.mem_primeFactors.mp hq
  have hXq : X < q := by
    by_contra hh
    exact havoid q hqprime (by omega) hqS hqi
  obtain ⟨d, hid⟩ := hqi
  have hdpos : 0 < d := by nlinarith
  have hdA : d ≤ A := by nlinarith
  have hdne : d ≠ 1 := by
    intro hd
    have hiq : i = q := by simpa [hd] using hid
    exact hprime (hiq.symm ▸ hqprime)
  obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd hdne
  have hple : p ≤ d := Nat.le_of_dvd hdpos hpd
  have hpS : p ∉ S := by intro hh; have := hS p hh; omega
  apply havoid p hp (by omega) hpS
  rw [hid]
  exact dvd_mul_of_dvd_right hpd q

/-- Finite prime sets arbitrarily far out have arbitrarily large reciprocal sums. -/
theorem exists_prime_tail_sum (A : ℕ) (M : ℝ) :
    ∃ S : Finset ℕ, (∀ p ∈ S, p.Prime ∧ A < p) ∧ M < ∑ p ∈ S, (1 : ℝ) / p := by
  classical
  let L : Set Nat.Primes := {p | (p : ℕ) ≤ A}
  have hL : L.Finite := Set.Finite.preimage Subtype.val_injective.injOn (Set.finite_Iic A)
  have hnot : ¬Summable (fun p : ↥(Lᶜ) => (1 : ℝ) / (p.val : ℕ)) := by
    intro h
    exact Nat.Primes.not_summable_one_div (hL.summable_compl_iff.mp h)
  have hex : ∃ T : Finset ↥(Lᶜ), M < ∑ p ∈ T, (1 : ℝ) / (p.val : ℕ) := by
    by_contra hn
    push_neg at hn
    exact hnot (summable_of_sum_le (fun _ => by positivity) hn)
  obtain ⟨T, hT⟩ := hex
  refine ⟨T.image (fun p => (p.val : ℕ)), ?_, ?_⟩
  · intro p hp
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hp
    exact ⟨q.val.property, Nat.lt_of_not_ge q.property⟩
  · rw [Finset.sum_image]
    · exact hT
    · intro p hp q hq he
      exact Subtype.ext (Subtype.ext he)

/-- A finite version of the elementary Euler-product estimate. -/
theorem product_density_sum_le (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) :
    (∏ p ∈ S, ((p : ℝ) - 1)) * (1 + ∑ p ∈ S, (1 : ℝ) / p) ≤ ∏ p ∈ S, (p : ℝ) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert p S hp ih =>
    have hpprime := hS p (Finset.mem_insert_self _ _)
    have hSpr : ∀ q ∈ S, q.Prime := fun q hq => hS q (Finset.mem_insert_of_mem hq)
    have hpR : 0 < (p : ℝ) := by exact_mod_cast hpprime.pos
    have hprod : 0 ≤ ∏ q ∈ S, ((q : ℝ) - 1) := by
      apply Finset.prod_nonneg
      intro q hq
      have hqR : (1 : ℝ) ≤ q := by exact_mod_cast (hSpr q hq).one_le
      linarith
    have hsum : 0 ≤ ∑ q ∈ S, (1 : ℝ) / q := Finset.sum_nonneg (fun q hq => by positivity)
    have hinv : (p : ℝ) * (1 / p) = 1 := mul_one_div_cancel hpR.ne'
    have hinvpos : (0 : ℝ) ≤ 1 / p := by positivity
    have haux : ((p : ℝ) - 1) * (1 + (1 / p + ∑ q ∈ S, (1 : ℝ) / q)) ≤
        p * (1 + ∑ q ∈ S, (1 : ℝ) / q) := by nlinarith
    rw [Finset.prod_insert hp, Finset.prod_insert hp, Finset.sum_insert hp]
    calc
      _ = (∏ q ∈ S, ((q : ℝ) - 1)) *
          (((p : ℝ) - 1) * (1 + (1 / p + ∑ q ∈ S, (1 : ℝ) / q))) := by ring
      _ ≤ (∏ q ∈ S, ((q : ℝ) - 1)) * (p * (1 + ∑ q ∈ S, (1 : ℝ) / q)) :=
        mul_le_mul_of_nonneg_left haux hprod
      _ = p * ((∏ q ∈ S, ((q : ℝ) - 1)) * (1 + ∑ q ∈ S, (1 : ℝ) / q)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (ih hSpr) hpR.le

/-- The product density of a finite tail of the primes can be made arbitrarily small. -/
theorem exists_prime_tail_density (A D : ℕ) :
    ∃ S : Finset ℕ, (∀ p ∈ S, p.Prime ∧ A < p) ∧
      D * (∏ p ∈ S, (p - 1)) ≤ ∏ p ∈ S, p := by
  obtain ⟨S, hS, hsum⟩ := exists_prime_tail_sum A (D : ℝ)
  refine ⟨S, hS, ?_⟩
  have hprod := product_density_sum_le S (fun p hp => (hS p hp).1)
  have hnonneg : 0 ≤ ∏ p ∈ S, ((p : ℝ) - 1) := by
    apply Finset.prod_nonneg
    intro p hp
    have : (1 : ℝ) ≤ p := by exact_mod_cast (hS p hp).1.one_le
    linarith
  have hle : (D : ℝ) * (∏ p ∈ S, ((p : ℝ) - 1)) ≤ ∏ p ∈ S, (p : ℝ) := by
    calc
      _ = (∏ p ∈ S, ((p : ℝ) - 1)) * D := mul_comm _ _
      _ ≤ (∏ p ∈ S, ((p : ℝ) - 1)) * (1 + ∑ p ∈ S, (1 : ℝ) / p) :=
        mul_le_mul_of_nonneg_left (by linarith) hnonneg
      _ ≤ _ := hprod
  have hcast : (∏ p ∈ S, ((p : ℝ) - 1)) = ((∏ p ∈ S, (p - 1) : ℕ) : ℝ) := by
    rw [Nat.cast_prod]
    apply Finset.prod_congr rfl
    intro p hp
    rw [Nat.cast_sub (hS p hp).1.one_le, Nat.cast_one]
  rw [hcast, ← Nat.cast_prod] at hle
  exact_mod_cast hle

/-- The survivors of the zero-class part of the construction are primes or fixed smooth numbers. -/
theorem zero_sift_card_le (A X : ℕ) (S : Finset ℕ)
    (hAX : A ≤ X) (hS : ∀ p ∈ S, A < p) :
    (sift (Finset.range (A * X)) ((X + 1).primesBelow \ S) (fun _ => 0)).card ≤
      (A * X).primeCounting +
        2 ^ (S.sup id + 1).primesBelow.card * (A * X).sqrt + 1 := by
  classical
  let B := S.sup id + 1
  have hsub : sift (Finset.range (A * X)) ((X + 1).primesBelow \ S) (fun _ => 0) ⊆
      insert 0 ((A * X + 1).primesBelow ∪ Nat.smoothNumbersUpTo (A * X) B) := by
    intro i hi
    obtain ⟨hiM, hiP⟩ := Finset.mem_filter.mp hi
    have hiM' : i < A * X := Finset.mem_range.mp hiM
    by_cases hi0 : i = 0
    · simp [hi0]
    have hor := prime_or_smooth hAX hS (Nat.pos_of_ne_zero hi0) hiM'.le
      (fun p hp hpX hpS hd => hiP p
        (Finset.mem_sdiff.mpr ⟨Nat.mem_primesBelow.mpr ⟨by omega, hp⟩, hpS⟩)
        (by simpa only [Nat.ModEq, Nat.zero_mod] using Nat.mod_eq_zero_of_dvd hd))
    apply Finset.mem_insert_of_mem
    rcases hor with hip | his
    · exact Finset.mem_union_left _ (Nat.mem_primesBelow.mpr ⟨by omega, hip⟩)
    · apply Finset.mem_union_right
      apply Nat.mem_smoothNumbersUpTo.mpr
      refine ⟨hiM'.le, Nat.mem_smoothNumbers_of_primeFactors_subset hi0 ?_⟩
      intro p hp
      have hple : p ≤ S.sup id := Finset.le_sup (f := id) (his hp)
      exact Finset.mem_range.mpr (by dsimp [B]; omega)
  have hpc : (A * X + 1).primesBelow.card = (A * X).primeCounting := by
    simp only [Nat.primesBelow, Nat.primeCounting, Nat.primeCounting',
      Nat.count_eq_card_filter_range]
  calc
    _ ≤ (insert 0 ((A * X + 1).primesBelow ∪ Nat.smoothNumbersUpTo (A * X) B)).card :=
      Finset.card_le_card hsub
    _ ≤ ((A * X + 1).primesBelow ∪ Nat.smoothNumbersUpTo (A * X) B).card + 1 :=
      Finset.card_insert_le _ _
    _ ≤ ((A * X + 1).primesBelow.card + (Nat.smoothNumbersUpTo (A * X) B).card) + 1 :=
      Nat.add_le_add_right (Finset.card_union_le _ _) _
    _ ≤ _ := by
      rw [hpc]
      exact Nat.add_le_add_right (Nat.add_le_add_left (Nat.smoothNumbersUpTo_card_le _ _) _) _

/-- An explicit finite covering budget combining all parts of the construction. -/
theorem exists_cover_budget (A X : ℕ) (S : Finset ℕ) (hA : 0 < A) (hAX : A ≤ X)
    (hS : ∀ p ∈ S, p.Prime ∧ A < p)
    (hdensity : A * (∏ p ∈ S, (p - 1)) ≤ ∏ p ∈ S, p) :
    ∃ k : ℕ, ¬IsJacobsthalBound k (A * X) ∧
      A * k ≤ A * (X.primeCounting + S.card) + (A * X).primeCounting +
        2 ^ (S.sup id + 1).primesBelow.card * (A * X).sqrt + 1 := by
  classical
  let P := (X + 1).primesBelow \ S
  let R := sift (Finset.range (A * X)) P (fun _ => 0)
  let U := ∏ p ∈ S, (p - 1)
  let V := ∏ p ∈ S, p
  let F := (U * R.card) / V
  let k := P.card + S.card + F
  have hP : ∀ p ∈ P, p.Prime := fun p hp =>
    (Nat.mem_primesBelow.mp (Finset.mem_sdiff.mp hp).1).2
  have hdis : Disjoint P S := Finset.sdiff_disjoint
  refine ⟨k, not_bound_of_greedy_budget (A * X) P S hP
    (fun p hp => (hS p hp).1) hdis (fun _ => 0), ?_⟩
  have hV : 0 < V := Finset.prod_pos (fun p hp => (hS p hp).1.pos)
  have hF : F * V ≤ U * R.card := Nat.div_mul_le_self _ _
  have hF' : A * F ≤ R.card := by
    have h1 := Nat.mul_le_mul_left A hF
    have h2 := Nat.mul_le_mul_right R.card hdensity
    change A * U * R.card ≤ V * R.card at h2
    have h3 : (A * F) * V ≤ R.card * V := by nlinarith
    exact (mul_le_mul_iff_left₀ hV).mp (by nlinarith [h3])
  have hPcard : P.card ≤ X.primeCounting := by
    have hh := Finset.card_le_card (Finset.sdiff_subset (s := (X + 1).primesBelow) (t := S))
    simpa only [Nat.primesBelow, Nat.primeCounting, Nat.primeCounting',
      Nat.count_eq_card_filter_range] using hh
  have hR := zero_sift_card_le A X S hAX (fun p hp => (hS p hp).2)
  change R.card ≤ _ at hR
  dsimp only [k]
  nlinarith [Nat.mul_le_mul_left A hPcard]

#print axioms exists_sift_card_le
#print axioms prime_or_smooth
#print axioms not_bound_of_greedy_budget
#print axioms exists_prime_tail_density
#print axioms exists_cover_budget
end Erdos970.ConstructiveCover
