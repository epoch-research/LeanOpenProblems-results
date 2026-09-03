import Submission.DivisorBound

/-!
A divisor bound for quartic representation fibers with fixed first and second
power sums. This does not bound the number of fibers at a fixed fourth-power sum.
-/

namespace Erdos322Research.QuarticMomentFiber

/-- The complementary-coordinate product is fixed by power sums one, two, four. -/
theorem complement_product_identity (a : Fin 4 → ℤ) :
    8 * (∏ i, ((∑ j, a j) - a i)) =
      3 * (∑ i, a i)^4 - 2 * (∑ i, a i)^2 * (∑ i, a i^2) +
        (∑ i, a i^2)^2 - 2 * (∑ i, a i^4) := by
  simp only [Fin.sum_univ_four, Fin.prod_univ_four]
  ring

private theorem complementary_products_equal (s t n : ℕ) (a b : Fin 4 → ℕ)
    (has : ∑ i, a i = s) (hat : ∑ i, a i^2 = t) (han : ∑ i, a i^4 = n)
    (hbs : ∑ i, b i = s) (hbt : ∑ i, b i^2 = t) (hbn : ∑ i, b i^4 = n) :
    (∏ i, (s - a i)) = ∏ i, (s - b i) := by
  have ha (i : Fin 4) : a i ≤ s := by
    rw [← has]
    exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
  have hb (i : Fin 4) : b i ≤ s := by
    rw [← hbs]
    exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
  have has' : ∑ i, (a i : ℤ) = s := by exact_mod_cast has
  have hat' : ∑ i, (a i : ℤ)^2 = t := by exact_mod_cast hat
  have han' : ∑ i, (a i : ℤ)^4 = n := by exact_mod_cast han
  have hbs' : ∑ i, (b i : ℤ) = s := by exact_mod_cast hbs
  have hbt' : ∑ i, (b i : ℤ)^2 = t := by exact_mod_cast hbt
  have hbn' : ∑ i, (b i : ℤ)^4 = n := by exact_mod_cast hbn
  have h₁ := complement_product_identity (fun i => (a i : ℤ))
  have h₂ := complement_product_identity (fun i => (b i : ℤ))
  rw [has', hat', han'] at h₁
  rw [hbs', hbt', hbn'] at h₂
  have he : (∏ i, ((s : ℤ) - a i)) = ∏ i, ((s : ℤ) - b i) := by omega
  have hac : ((∏ i, (s - a i) : ℕ) : ℤ) = ∏ i, ((s : ℤ) - a i) := by
    push_cast [ha]
    rfl
  have hbc : ((∏ i, (s - b i) : ℕ) : ℤ) = ∏ i, ((s : ℤ) - b i) := by
    push_cast [hb]
    rfl
  exact_mod_cast hac.trans (he.trans hbc.symm)

/-- Every nonempty nondegenerate fiber injects into four divisors of one
positive integer at most `s^4`. The condition `a i < s` excludes the tuples
supported at a single coordinate, for which the complementary product is zero. -/
theorem fiber_divisor_bound (S : Finset (Fin 4 → ℕ)) (s t n : ℕ)
    (hne : S.Nonempty)
    (hs : ∀ a ∈ S, ∑ i, a i = s)
    (ht : ∀ a ∈ S, ∑ i, a i^2 = t)
    (hn : ∀ a ∈ S, ∑ i, a i^4 = n)
    (hstrict : ∀ a ∈ S, ∀ i, a i < s) :
    ∃ N : ℕ, 0 < N ∧ N ≤ s^4 ∧ S.card ≤ N.divisors.card^4 := by
  classical
  obtain ⟨b, hb⟩ := hne
  let N : ℕ := ∏ i, (s - b i)
  have hN : 0 < N := Finset.prod_pos (by
    intro i _
    exact Nat.sub_pos_of_lt (hstrict b hb i))
  have hbound : N ≤ s^4 := by
    calc
      N ≤ ∏ _i : Fin 4, s := Finset.prod_le_prod' (fun i _ => Nat.sub_le _ _)
      _ = s^4 := by simp
  have hprod (a : S) : (∏ i, (s - a.val i)) = N :=
    complementary_products_equal s t n a.val b (hs a.val a.property)
      (ht a.val a.property) (hn a.val a.property) (hs b hb) (ht b hb) (hn b hb)
  let f : S → (Fin 4 → N.divisors) := fun a i =>
    ⟨s - a.val i, Nat.mem_divisors.mpr ⟨by
      rw [← hprod a]
      exact Finset.dvd_prod_of_mem (fun i => s - a.val i) (Finset.mem_univ i), hN.ne'⟩⟩
  have hf : Function.Injective f := by
    intro a b hab
    apply Subtype.ext
    funext i
    have he := congrArg (fun v : Fin 4 → N.divisors => (v i : ℕ)) hab
    change s - a.val i = s - b.val i at he
    have ha := hstrict a.val a.property i
    have hb' := hstrict b.val b.property i
    omega
  refine ⟨N, hN, hbound, ?_⟩
  have hc := Fintype.card_le_of_injective f hf
  simpa using hc

/-- The fiber bound is uniform in all three prescribed moments. This version
uses the first moment as its size parameter and excludes one-supported tuples. -/
theorem nondegenerate_fiber_subpolynomial_sum (ε : ℝ) (hε : 0 < ε) :
    ∃ C > (0 : ℝ), ∀ (S : Finset (Fin 4 → ℕ)) (s t n : ℕ),
      (∀ a ∈ S, ∑ i, a i = s) →
      (∀ a ∈ S, ∑ i, a i^2 = t) →
      (∀ a ∈ S, ∑ i, a i^4 = n) →
      (∀ a ∈ S, ∀ i, a i < s) →
      (S.card : ℝ) ≤ C * (s : ℝ)^ε := by
  obtain ⟨D, hD, hdiv⟩ := divisor_count_subpolynomial (ε/16) (by positivity)
  refine ⟨D^4, by positivity, ?_⟩
  intro S s t n hs ht hn hstrict
  by_cases he : S.Nonempty
  · obtain ⟨N, hN, hNs, hc⟩ := fiber_divisor_bound S s t n he hs ht hn hstrict
    have hr : (N : ℝ)^(ε/16) ≤ (s : ℝ)^(ε/4) := by
      calc
        (N : ℝ)^(ε/16) ≤ ((s : ℝ)^4)^(ε/16) :=
          Real.rpow_le_rpow (by positivity) (by exact_mod_cast hNs) (by positivity)
        _ = (s : ℝ)^(ε/4) := by
          rw [← Real.rpow_natCast (s : ℝ) 4, ← Real.rpow_mul (by positivity)]
          congr 1
          ring
    have hd : (N.divisors.card : ℝ) ≤ D*(s : ℝ)^(ε/4) :=
      (hdiv N hN).trans (mul_le_mul_of_nonneg_left hr hD.le)
    calc
      (S.card : ℝ) ≤ (N.divisors.card : ℝ)^4 := by exact_mod_cast hc
      _ ≤ (D*(s : ℝ)^(ε/4))^4 := pow_le_pow_left₀ (by positivity) hd 4
      _ = D^4*(s : ℝ)^ε := by
        rw [mul_pow, ← Real.rpow_mul_natCast (by positivity)]
        congr 2
        ring
  · have hz : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp he
    simp only [hz, Finset.card_empty, Nat.cast_zero]
    positivity

private theorem degenerate_fiber_card_le_four (S : Finset (Fin 4 → ℕ)) (s : ℕ)
    (hs : ∀ a ∈ S, ∑ i, a i = s)
    (hbad : ∀ a ∈ S, ¬ ∀ i, a i < s) : S.card ≤ 4 := by
  classical
  let g : Fin 4 → Fin 4 → ℕ := fun i j => if j = i then s else 0
  have hsub : S ⊆ Finset.univ.image g := by
    intro a ha
    obtain ⟨i, hi⟩ := not_forall.mp (hbad a ha)
    have hia : s ≤ a i := Nat.le_of_not_gt hi
    have hai : a i = s := by
      have hle := Finset.single_le_sum (f := a)
        (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
      rw [hs a ha] at hle
      omega
    have herase : ∑ j ∈ Finset.univ.erase i, a j = 0 := by
      have he := Finset.add_sum_erase Finset.univ a (Finset.mem_univ i)
      rw [hs a ha, hai] at he
      omega
    have hjzero (j : Fin 4) (hji : j ≠ i) : a j = 0 := by
      have hle := Finset.single_le_sum (f := a) (fun _ _ => Nat.zero_le _)
        (Finset.mem_erase.mpr ⟨hji, Finset.mem_univ j⟩)
      rw [herase] at hle
      omega
    refine Finset.mem_image.mpr ⟨i, Finset.mem_univ i, ?_⟩
    funext j
    by_cases hji : j = i
    · subst j
      simpa [g] using hai.symm
    · simp [g, hji, hjzero j hji]
  exact (Finset.card_le_card hsub).trans (by
    simpa using (Finset.card_image_le (s := Finset.univ) (f := g)))

/-- For each positive exponent, a single constant bounds every finite quartic
fiber with prescribed first and second power sums. All degeneracies are included.
The constant is independent of both auxiliary moment values. -/
theorem fiber_subpolynomial (ε : ℝ) (hε : 0 < ε) :
    ∃ C > (0 : ℝ), ∀ (S : Finset (Fin 4 → ℕ)) (s t n : ℕ), 1 ≤ n →
      (∀ a ∈ S, ∑ i, a i = s) →
      (∀ a ∈ S, ∑ i, a i^2 = t) →
      (∀ a ∈ S, ∑ i, a i^4 = n) →
      (S.card : ℝ) ≤ C * (n : ℝ)^ε := by
  classical
  obtain ⟨D, hD, hbound⟩ := nondegenerate_fiber_subpolynomial_sum ε hε
  refine ⟨D*4^ε+4, by positivity, ?_⟩
  intro S s t n hnpos hs ht hn
  by_cases he : S.Nonempty
  · obtain ⟨b, hb⟩ := he
    have hbi (i : Fin 4) : b i ≤ n := by
      have hle := Finset.single_le_sum (f := fun j => b j^4)
        (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
      rw [hn b hb] at hle
      exact (Nat.le_pow (by decide : 0 < 4)).trans hle
    have hsn : s ≤ 4*n := by
      calc
        s = ∑ i, b i := (hs b hb).symm
        _ ≤ ∑ _i : Fin 4, n := Finset.sum_le_sum (fun i _ => hbi i)
        _ = 4*n := by simp
    let T := S.filter (fun a => ∀ i, a i < s)
    let U := S.filter (fun a => ¬ ∀ i, a i < s)
    have hT : (T.card : ℝ) ≤ D*(s : ℝ)^ε := hbound T s t n
      (fun a ha => hs a (Finset.mem_filter.mp ha).1)
      (fun a ha => ht a (Finset.mem_filter.mp ha).1)
      (fun a ha => hn a (Finset.mem_filter.mp ha).1)
      (fun a ha => (Finset.mem_filter.mp ha).2)
    have hU : (U.card : ℝ) ≤ 4 := by
      exact_mod_cast degenerate_fiber_card_le_four U s
        (fun a ha => hs a (Finset.mem_filter.mp ha).1)
        (fun a ha => (Finset.mem_filter.mp ha).2)
    have hcard : (S.card : ℝ) = T.card + U.card := by
      exact_mod_cast (Finset.card_filter_add_card_filter_not
        (s := S) (p := fun a => ∀ i, a i < s)).symm
    have hr : (s : ℝ)^ε ≤ 4^ε*(n : ℝ)^ε := by
      rw [← Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 4) (by positivity)]
      exact Real.rpow_le_rpow (by positivity) (by exact_mod_cast hsn) hε.le
    have hone : 1 ≤ (n : ℝ)^ε := Real.one_le_rpow (by exact_mod_cast hnpos) hε.le
    calc
      (S.card : ℝ) = T.card + U.card := hcard
      _ ≤ D*(s : ℝ)^ε+4 := add_le_add hT hU
      _ ≤ D*(4^ε*(n : ℝ)^ε)+4*(n : ℝ)^ε :=
        add_le_add (mul_le_mul_of_nonneg_left hr hD.le)
          (by nlinarith)
      _ = (D*4^ε+4)*(n : ℝ)^ε := by ring
  · have hz : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp he
    simp only [hz, Finset.card_empty, Nat.cast_zero]
    positivity

end Erdos322Research.QuarticMomentFiber
