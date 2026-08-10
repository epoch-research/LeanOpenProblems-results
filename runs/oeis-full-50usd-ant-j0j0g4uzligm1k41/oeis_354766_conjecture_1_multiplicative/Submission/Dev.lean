import FormalConjectures.Util.ProblemImports
open Int Finset
set_option maxHeartbeats 1000000
open scoped BigOperators

private def count_solutions_pair (a b : ℤ) : ℕ :=
  let v : ℤ := 2 * b - a * a
  if v < 0 then 0
  else
    let s := v.sqrt
    if s * s = v then (if v = 0 then 1 else 2) else 0

-- solutions (h,i) with h+i=a, h^2+i^2=b, over a box
noncomputable def pairSol (a b : ℤ) : Finset (ℤ × ℤ) :=
  (Finset.Icc (-(b+1)) (b+1) ×ˢ Finset.Icc (-(b+1)) (b+1)).filter
    (fun p => p.1 + p.2 = a ∧ p.1^2 + p.2^2 = b)

-- roots of w^2 = v
noncomputable def rootSol (v : ℤ) : Finset ℤ :=
  (Finset.Icc (-(v+1)) (v+1)).filter (fun w => w * w = v)

-- key bijection: (h,i) ↦ h - i
lemma pairSol_card (a b : ℤ) : (pairSol a b).card = (rootSol (2*b - a*a)).card := by
  apply Finset.card_bij (fun p _ => p.1 - p.2)
  · rintro ⟨h, i⟩ hp
    simp only [pairSol, mem_filter, mem_product, mem_Icc] at hp
    obtain ⟨_, hsum, hsq⟩ := hp
    have hv : (h - i) * (h - i) = 2 * b - a * a := by nlinarith [hsum, hsq]
    simp only [rootSol, mem_filter, mem_Icc]
    refine ⟨⟨?_, ?_⟩, hv⟩
    · nlinarith [hv, sq_nonneg (h - i)]
    · nlinarith [hv, sq_nonneg (h - i)]
  · rintro ⟨h1,i1⟩ hp1 ⟨h2,i2⟩ hp2 heq
    simp only [pairSol, mem_filter, mem_product, mem_Icc] at hp1 hp2
    simp only at heq
    obtain ⟨_, hs1, _⟩ := hp1
    obtain ⟨_, hs2, _⟩ := hp2
    have e1 : h1 = h2 := by omega
    have e2 : i1 = i2 := by omega
    simp [e1, e2]
  · intro w hw
    simp only [rootSol, mem_filter, mem_Icc] at hw
    obtain ⟨⟨hw1, hw2⟩, hwsq⟩ := hw
    have hsqeven : (a + w) ^ 2 = 2 * (b + a * w) := by nlinarith [hwsq]
    have hpar : Even (a + w) := by
      have h2 : Even ((a + w) ^ 2) := ⟨b + a * w, by linarith [hsqeven]⟩
      exact (Int.even_pow.mp h2).1
    obtain ⟨h, hh⟩ := hpar
    refine ⟨(h, a - h), ?_, ?_⟩
    · have hb0 : 0 ≤ b := by nlinarith [hwsq, mul_self_nonneg w, mul_self_nonneg a]
      have hsq : h ^ 2 + (a - h) ^ 2 = b := by nlinarith [hh, hwsq]
      have hh2 : h ^ 2 ≤ b := by nlinarith [hsq, sq_nonneg (a - h)]
      have hi2 : (a - h) ^ 2 ≤ b := by nlinarith [hsq, sq_nonneg h]
      simp only [pairSol, mem_filter, mem_product, mem_Icc]
      refine ⟨⟨⟨?_, ?_⟩, ?_, ?_⟩, by omega, hsq⟩
      · nlinarith [hh2]
      · nlinarith [hh2]
      · nlinarith [hi2]
      · nlinarith [hi2]
    · simp only; omega

-- characterization of square roots
lemma mul_self_eq_iff (v w : ℤ) :
    w * w = v ↔ (v.sqrt * v.sqrt = v ∧ (w = v.sqrt ∨ w = -v.sqrt)) := by
  constructor
  · intro h
    have hnn : 0 ≤ v := by rw [← h]; exact mul_self_nonneg w
    have hs : v.sqrt = (w.natAbs : ℤ) := by rw [← h, Int.sqrt_eq w]
    have hsv : v.sqrt * v.sqrt = v := by
      rw [hs, ← Int.natCast_mul, Int.natAbs_mul_self, h]
    refine ⟨hsv, ?_⟩
    rcases Int.natAbs_eq w with hw | hw
    · left; rw [hs, ← hw]
    · right; rw [hs]; omega
  · rintro ⟨hsv, hw | hw⟩ <;> subst hw
    · exact hsv
    · rw [neg_mul_neg]; exact hsv

lemma rootSol_card (v : ℤ) :
    (rootSol v).card
      = (if v < 0 then 0 else if v.sqrt * v.sqrt = v then (if v = 0 then 1 else 2) else 0) := by
  by_cases hneg : v < 0
  · simp only [hneg, if_true]
    rw [Finset.card_eq_zero]
    ext w
    simp only [rootSol, mem_filter, notMem_empty, iff_false, not_and]
    intro _ hww
    nlinarith [mul_self_nonneg w]
  · simp only [hneg, if_false]
    push_neg at hneg
    by_cases hsq : v.sqrt * v.sqrt = v
    · simp only [hsq, if_true]
      have hsnn : 0 ≤ v.sqrt := Int.sqrt_nonneg v
      have hsle : v.sqrt ≤ v + 1 := by nlinarith [hsq, hsnn]
      have hmem : rootSol v = ({v.sqrt, -v.sqrt} : Finset ℤ) := by
        ext w
        simp only [rootSol, mem_filter, mem_Icc, mem_insert, mem_singleton]
        rw [mul_self_eq_iff]
        constructor
        · rintro ⟨_, _, h⟩; exact h
        · intro h
          have hb : -(v+1) ≤ w ∧ w ≤ v + 1 := by rcases h with h | h <;> omega
          exact ⟨hb, hsq, h⟩
      rw [hmem]
      by_cases hv0 : v = 0
      · rw [if_pos hv0]
        have h0 : v.sqrt = 0 := by rw [hv0]; simpa using Int.sqrt_eq 0
        rw [h0]; simp
      · rw [if_neg hv0]
        have hpos : 0 < v.sqrt := by
          rcases lt_or_eq_of_le hsnn with h | h
          · exact h
          · exfalso; apply hv0; rw [← hsq, ← h]; ring
        rw [Finset.card_pair (by omega)]
    · simp only [hsq, if_false]
      rw [Finset.card_eq_zero]
      ext w
      simp only [rootSol, mem_filter, notMem_empty, iff_false, not_and]
      intro _ hww
      rw [mul_self_eq_iff] at hww
      exact hsq hww.1

lemma count_pair_eq (a b : ℤ) : count_solutions_pair a b = (pairSol a b).card := by
  rw [pairSol_card, rootSol_card]
  rfl

-- pair count equals filter over any large enough box
lemma count_pair_card (a b B : ℤ) (hB : b + 1 ≤ B) :
    count_solutions_pair a b
      = ((Finset.Icc (-B) B ×ˢ Finset.Icc (-B) B).filter
          (fun p => p.1 + p.2 = a ∧ p.1 ^ 2 + p.2 ^ 2 = b)).card := by
  rw [count_pair_eq]
  congr 1
  ext ⟨h, i⟩
  simp only [pairSol, mem_filter, mem_product, mem_Icc]
  constructor
  · rintro ⟨_, hs, hsq⟩
    refine ⟨⟨⟨?_, ?_⟩, ?_, ?_⟩, hs, hsq⟩ <;>
      nlinarith [hsq, sq_nonneg h, sq_nonneg i]
  · rintro ⟨_, hs, hsq⟩
    refine ⟨⟨⟨?_, ?_⟩, ?_, ?_⟩, hs, hsq⟩ <;>
      nlinarith [hsq, sq_nonneg h, sq_nonneg i]

private noncomputable def count_solutions_triple (x y : ℤ) : ℕ :=
  if y < 0 then 0
  else if x * x > 3 * y then 0
  else
    let m : ℤ := y.sqrt
    Finset.Icc (-m) m |>.sum fun c => count_solutions_pair (x - c) (y - c * c)

noncomputable def tripleSol (x y : ℤ) : Finset (ℤ × ℤ × ℤ) :=
  (Finset.Icc (-(y+1)) (y+1) ×ˢ Finset.Icc (-(y+1)) (y+1) ×ˢ Finset.Icc (-(y+1)) (y+1)).filter
    (fun p => p.1 + p.2.1 + p.2.2 = x ∧ p.1 ^ 2 + p.2.1 ^ 2 + p.2.2 ^ 2 = y)

lemma tripleFiber_mem (x y c : ℤ) (hc : c ∈ Finset.Icc (-(y+1)) (y+1)) :
    ((tripleSol x y).filter (fun p => p.2.2 = c)).card
      = count_solutions_pair (x - c) (y - c * c) := by
  rw [count_pair_card (x - c) (y - c * c) (y + 1) (by nlinarith [mul_self_nonneg c])]
  apply Finset.card_bij (fun p _ => (p.1, p.2.1))
  · rintro ⟨h, i, j⟩ hp
    simp only [tripleSol, mem_filter, mem_product, mem_Icc] at hp
    obtain ⟨⟨⟨hh1, hh2⟩, ⟨hi1, hi2⟩, _⟩, hsum, hsq⟩ := hp.1
    have hjc : j = c := hp.2
    subst hjc
    simp only [mem_filter, mem_product, mem_Icc]
    refine ⟨⟨⟨hh1, hh2⟩, hi1, hi2⟩, by linarith [hsum], by nlinarith [hsq]⟩
  · rintro ⟨h1, i1, j1⟩ hp1 ⟨h2, i2, j2⟩ hp2 heq
    simp only [mem_filter] at hp1 hp2
    simp only [Prod.mk.injEq] at heq
    obtain ⟨h1e, h2e⟩ := heq
    have : j1 = c := hp1.2
    have : j2 = c := hp2.2
    simp_all
  · rintro ⟨h, i⟩ hp
    simp only [mem_filter, mem_product, mem_Icc] at hp
    obtain ⟨⟨⟨hh1, hh2⟩, hi1, hi2⟩, hsum, hsq⟩ := hp
    simp only [mem_Icc] at hc
    refine ⟨(h, i, c), ?_, rfl⟩
    simp only [mem_filter]
    refine ⟨?_, trivial⟩
    simp only [tripleSol, mem_filter, mem_product, mem_Icc]
    exact ⟨⟨⟨hh1, hh2⟩, ⟨hi1, hi2⟩, hc⟩, by linarith [hsum], by nlinarith [hsq]⟩

lemma tripleSol_sum (x y : ℤ) :
    (tripleSol x y).card
      = ∑ c ∈ Finset.Icc (-(y+1)) (y+1), count_solutions_pair (x - c) (y - c * c) := by
  rw [Finset.card_eq_sum_card_fiberwise
    (f := fun p => p.2.2) (t := Finset.Icc (-(y+1)) (y+1))]
  · exact Finset.sum_congr rfl (fun c hc => tripleFiber_mem x y c hc)
  · rintro ⟨h, i, j⟩ hp
    rw [tripleSol] at hp
    have hb := (Finset.mem_filter.mp hp).1
    simp only [mem_product, mem_Icc] at hb
    exact Finset.mem_Icc.mpr hb.2.2

lemma isqrt_mul_le (y : ℤ) (hy : 0 ≤ y) : y.sqrt * y.sqrt ≤ y := by
  have h := Nat.sqrt_le y.toNat
  have hs : y.sqrt = (Nat.sqrt y.toNat : ℤ) := rfl
  rw [hs]
  calc (Nat.sqrt y.toNat : ℤ) * (Nat.sqrt y.toNat : ℤ)
      = ((Nat.sqrt y.toNat * Nat.sqrt y.toNat : ℕ) : ℤ) := by push_cast; ring
    _ ≤ (y.toNat : ℤ) := by exact_mod_cast h
    _ = y := Int.toNat_of_nonneg hy

lemma isqrt_lt_succ (y : ℤ) (hy : 0 ≤ y) : y < (y.sqrt + 1) * (y.sqrt + 1) := by
  have h := Nat.lt_succ_sqrt y.toNat
  have hs : y.sqrt = (Nat.sqrt y.toNat : ℤ) := rfl
  rw [hs]
  calc y = (y.toNat : ℤ) := (Int.toNat_of_nonneg hy).symm
    _ < ((Nat.succ (Nat.sqrt y.toNat) * Nat.succ (Nat.sqrt y.toNat) : ℕ) : ℤ) := by exact_mod_cast h
    _ = ((Nat.sqrt y.toNat : ℤ) + 1) * ((Nat.sqrt y.toNat : ℤ) + 1) := by
        push_cast [Nat.succ_eq_add_one]; ring

lemma count_triple_eq (x y : ℤ) : count_solutions_triple x y = (tripleSol x y).card := by
  by_cases hy : y < 0
  · have hz : count_solutions_triple x y = 0 := by unfold count_solutions_triple; rw [if_pos hy]
    rw [hz]; symm; rw [Finset.card_eq_zero]
    ext p
    simp only [tripleSol, mem_filter, mem_product, mem_Icc, notMem_empty, iff_false]
    rintro ⟨-, -, hsq⟩
    nlinarith [sq_nonneg p.1, sq_nonneg p.2.1, sq_nonneg p.2.2]
  · by_cases hx : x * x > 3 * y
    · have hz : count_solutions_triple x y = 0 := by
        unfold count_solutions_triple; rw [if_neg hy, if_pos hx]
      rw [hz]; symm; rw [Finset.card_eq_zero]
      ext p
      simp only [tripleSol, mem_filter, mem_product, mem_Icc, notMem_empty, iff_false]
      rintro ⟨-, hsum, hsq⟩
      subst hsum hsq
      nlinarith [sq_nonneg (p.1 - p.2.1), sq_nonneg (p.2.1 - p.2.2), sq_nonneg (p.1 - p.2.2), hx]
    · unfold count_solutions_triple
      rw [if_neg hy, if_neg hx, tripleSol_sum]
      push_neg at hy hx
      apply Finset.sum_subset
      · intro c hc
        simp only [mem_Icc] at hc ⊢
        have hle : y.sqrt ≤ y + 1 := by nlinarith [isqrt_mul_le y hy, Int.sqrt_nonneg y]
        omega
      · intro c _ hcs
        simp only [mem_Icc, not_and_or, not_le] at hcs
        have hm := isqrt_lt_succ y hy
        have hs0 := Int.sqrt_nonneg y
        have hlt : y - c * c < 0 := by
          rcases hcs with h | h
          · have hc1 : y.sqrt + 1 ≤ -c := by omega
            nlinarith [hm, hc1, hs0]
          · have hc1 : y.sqrt + 1 ≤ c := by omega
            nlinarith [hm, hc1, hs0]
        unfold count_solutions_pair
        rw [if_pos (by nlinarith [hlt, mul_self_nonneg (x - c)])]
