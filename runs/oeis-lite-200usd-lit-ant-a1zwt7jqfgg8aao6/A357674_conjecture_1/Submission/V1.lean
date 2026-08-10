import Submission.Build

open Nat Finset BigOperators

namespace Wolst
variable {p : ℕ} [Fact p.Prime]

/-- Pair sum over a finset. -/
noncomputable def pairsum (b : ℕ → ZMod (p^5)) (s : Finset ℕ) : ZMod (p^5) :=
  ∑ i ∈ s, b i * (∑ j ∈ s.filter (· < i), b j)

lemma pairsum_insert (b : ℕ → ZMod (p^5)) {a : ℕ} {t : Finset ℕ} (ha : a ∉ t) :
    pairsum b (insert a t) = pairsum b t + b a * (∑ j ∈ t, b j) := by
  unfold pairsum
  rw [Finset.sum_insert ha]
  -- term i=a: b a * ∑_{j∈insert, j<a} b j = b a * ∑_{j∈t, j<a} b j (a<a false)
  have hfa : (insert a t).filter (· < a) = t.filter (· < a) := by
    ext x; simp only [Finset.mem_filter, Finset.mem_insert]
    constructor
    · rintro ⟨hx|hx, hlt⟩
      · omega
      · exact ⟨hx, hlt⟩
    · rintro ⟨hx, hlt⟩; exact ⟨Or.inr hx, hlt⟩
  rw [hfa]
  -- the sum over i∈t with insert-filter
  have hrest : ∑ i ∈ t, b i * (∑ j ∈ (insert a t).filter (· < i), b j)
      = ∑ i ∈ t, b i * (∑ j ∈ t.filter (· < i), b j) + ∑ i ∈ t, (if a < i then b i * b a else 0) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    by_cases hai : a < i
    · have : (insert a t).filter (· < i) = insert a (t.filter (· < i)) := by
        ext x; simp only [Finset.mem_filter, Finset.mem_insert]
        constructor
        · rintro ⟨hx|hx, hlt⟩
          · exact Or.inl hx
          · exact Or.inr ⟨hx, hlt⟩
        · rintro (hx|⟨hx,hlt⟩)
          · exact ⟨Or.inl hx, by omega⟩
          · exact ⟨Or.inr hx, hlt⟩
      rw [this, Finset.sum_insert (by simp only [Finset.mem_filter]; rintro ⟨hx,_⟩; exact ha hx)]
      rw [if_pos hai]; ring
    · have : (insert a t).filter (· < i) = t.filter (· < i) := by
        ext x; simp only [Finset.mem_filter, Finset.mem_insert]
        constructor
        · rintro ⟨hx|hx, hlt⟩
          · omega
          · exact ⟨hx, hlt⟩
        · rintro ⟨hx, hlt⟩; exact ⟨Or.inr hx, hlt⟩
      rw [this, if_neg hai]; ring
  rw [hrest]
  -- ∑_{i∈t} (if a<i then b i b a else 0) = b a * ∑_{i∈t, a<i} b i,  and combined with the b a∑_{j<a}
  -- want total: pairsum t + b a * ∑_t b
  have hsplit : ∑ i ∈ t, (if a < i then b i * b a else 0)
      = b a * ∑ i ∈ t.filter (a < ·), b i := by
    rw [Finset.mul_sum, ← Finset.sum_filter]
    apply Finset.sum_congr rfl; intro i _; ring
  rw [hsplit]
  have hcover : (∑ j ∈ t.filter (· < a), b j) + (∑ i ∈ t.filter (a < ·), b i) = ∑ j ∈ t, b j := by
    rw [← Finset.sum_union]
    · apply Finset.sum_congr _ (fun _ _ => rfl)
      ext x; simp only [Finset.mem_union, Finset.mem_filter]
      constructor
      · rintro (⟨hx,_⟩|⟨hx,_⟩) <;> exact hx
      · intro hx
        rcases lt_trichotomy x a with h|h|h
        · exact Or.inl ⟨hx, h⟩
        · exact absurd h.symm (by rintro rfl; exact ha hx)
        · exact Or.inr ⟨hx, h⟩
    · rw [Finset.disjoint_filter]; intro x _ h1; omega
  -- assemble
  have : b a * (∑ j ∈ t.filter (· < a), b j) + b a * ∑ i ∈ t.filter (a < ·), b i = b a * ∑ j ∈ t, b j := by
    rw [← mul_add, hcover]
  linear_combination this

/-- Product expansion: `∏(1+p·b i) = 1 + p·∑b + p²·pairsum + p³·(remainder)`. -/
lemma prod_expand (b : ℕ → ZMod (p^5)) (s : Finset ℕ) :
    ∃ c : ZMod (p^5), ∏ i ∈ s, (1 + (p:ZMod (p^5)) * b i)
      = 1 + (p:ZMod (p^5)) * (∑ i ∈ s, b i)
        + (p:ZMod (p^5))^2 * pairsum b s + (p:ZMod (p^5))^3 * c := by
  classical
  induction s using Finset.induction with
  | empty => exact ⟨0, by simp [pairsum]⟩
  | @insert a t ha ih =>
    obtain ⟨c, hc⟩ := ih
    refine ⟨c + b a * pairsum b t + (p:ZMod (p^5)) * b a * c, ?_⟩
    rw [Finset.prod_insert ha, hc, Finset.sum_insert ha, pairsum_insert b ha]
    ring
end Wolst

namespace Wolst
variable {p : ℕ} [Fact p.Prime]

/-- The value `v = C(3p-1, p-1)` cast into `ZMod (p^5)`. -/
noncomputable def vval (p : ℕ) : ZMod (p^5) := (((3*p-1).choose (p-1) : ℕ) : ZMod (p^5))

lemma vval_prod :
    vval p = ∏ i ∈ Finset.Ico 1 p, (1 + (2:ZMod (p^5))*(p:ZMod (p^5)) * ((i:ZMod (p^5)))⁻¹) := by
  have h := cval (p := p) 2
  rw [show (2+1)*p - 1 = 3*p - 1 from by ring] at h
  rw [vval]; exact h

lemma sq_sum_eq (b : ℕ → ZMod (p^5)) (s : Finset ℕ) :
    (∑ i ∈ s, b i)^2 = 2 * pairsum b s + ∑ i ∈ s, (b i)^2 := by
  classical
  induction s using Finset.induction with
  | empty => simp [pairsum]
  | @insert a t ha ih =>
    rw [Finset.sum_insert ha, pairsum_insert b ha, Finset.sum_insert ha]
    have := ih
    ring_nf
    ring_nf at this
    linear_combination this

/-- `v - 1` is divisible by `p^3`. -/
theorem vsub1_dvd (hp7 : 7 ≤ p) :
    ∃ z : ZMod (p^5), vval p - 1 = (p:ZMod (p^5))^3 * z := by
  set R := ZMod (p^5)
  set b : ℕ → R := fun i => 2 * (i:R)⁻¹ with hb
  have hbi : ∀ i, b i = 2 * (i:R)⁻¹ := fun i => rfl
  -- vval = ∏ (1 + p * b i)
  have hvprod : vval p = ∏ i ∈ Finset.Ico 1 p, (1 + (p:R) * b i) := by
    rw [vval_prod]
    apply Finset.prod_congr rfl; intro i _; rw [hbi]; ring
  obtain ⟨c, hc⟩ := prod_expand b (Finset.Ico 1 p)
  -- ∑ b = 2 S1
  have hsumb : ∑ i ∈ Finset.Ico 1 p, b i = 2 * S 1 := by
    unfold S; rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro i _
    rw [hbi, pow_one]
  -- ∑ b^2 = 4 S2
  have hsumb2 : ∑ i ∈ Finset.Ico 1 p, (b i)^2 = 4 * S 2 := by
    unfold S; rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro i _
    rw [hbi]; ring
  -- pairsum = 2 S1^2 - 2 S2
  have hpair : pairsum b (Finset.Ico 1 p) = 2 * (S 1)^2 - 2 * S 2 := by
    have h := sq_sum_eq b (Finset.Ico 1 p)
    rw [hsumb, hsumb2] at h
    have h2u : IsUnit (2:R) := by
      have := isUnit_cast (p:=p) (k:=5) 2 (by norm_num) (by omega); simpa using this
    apply h2u.mul_left_cancel
    linear_combination -h
  -- S1 = p^2 zS1, S2 = p zS2
  obtain ⟨zS1, hzS1⟩ := S1_dvd_p2 (p:=p) hp7
  obtain ⟨zS2, hzS2⟩ := S_dvd_p (p:=p) 2 (by omega) (by omega)
  have hp5 : (p:R)^5 = 0 := by rw [← Nat.cast_pow]; exact ZMod.natCast_self _
  refine ⟨2 * zS1 - 2 * zS2 + c, ?_⟩
  rw [hvprod, hc, hsumb, hpair, hzS1, hzS2]
  linear_combination (2*(p:R)*zS1^2) * hp5
end Wolst
