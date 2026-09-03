import Submission.FullFiberOverlapCount

/-! Forced overlap counts for full index fibers 0,...,H with H<=q.
This is auxiliary method analysis, not a bound on the original maximum. -/
namespace Erdos773.ShortFullFiberOverlap
open Finset PartialResidueFibers PartialFiberSelection MatchedResidueLifting FullFiberOverlap FullFiberOverlapCount
set_option maxHeartbeats 2000000

/-- The exact difference with gap 2u in a full fiber. -/
lemma gap_difference {q H r u a : ℕ} (hq : 0 < q) (hu : 0 < u) (ha : a+2*u ≤ H) :
    (q*(a+2*u)+r)^2-(q*a+r)^2 ∈ positiveDiffs (fiberValues q r (Icc 0 H)) := by
  apply mem_positiveDiffs.mpr
  refine ⟨(q*a+r)^2,mem_image.mpr ⟨a,mem_Icc.mpr ⟨Nat.zero_le _,by omega⟩,rfl⟩,
    (q*(a+2*u)+r)^2,mem_image.mpr ⟨a+2*u,mem_Icc.mpr ⟨Nat.zero_le _,ha⟩,rfl⟩,?_,rfl⟩
  apply Nat.pow_lt_pow_left _ (by decide : (2 : ℕ) ≠ 0)
  exact Nat.add_lt_add_right (Nat.mul_lt_mul_of_pos_left (by omega : a < a+2*u) hq) r

/-- Each modular match of small gaps yields an actual common positive
difference, with the prescribed endpoint gaps in each fiber. -/
theorem small_gap_shared_difference {q H L r s u v : ℕ} (hL : 0 < L)
    (hHL : 10*L ≤ H) (hu : u ∈ Icc L (2*L)) (hv : v ∈ Icc L (2*L))
    (hcop : q.Coprime v) (hr : r < q) (hs : s < q)
    (he : r*u ≡ s*v [MOD q]) :
    ∃ D ∈ positiveDiffs (fiberValues q r (Icc 0 H)) ∩
        positiveDiffs (fiberValues q s (Icc 0 H)),
      ∃ a c : ℕ, a+2*u ≤ H ∧ c+2*v ≤ H ∧
        (q*(a+2*u)+r)^2-(q*a+r)^2=D ∧
        (q*(c+2*v)+s)^2-(q*c+s)^2=D := by
  obtain ⟨a,c,ha,hc,he⟩ := small_gap_collision hL hu hv hcop hr hs he
  have ha := ha.trans hHL
  have hc := hc.trans hHL
  have hq : 0 < q := by omega
  have hu0 : 0 < u := lt_of_lt_of_le hL (mem_Icc.mp hu).1
  have hv0 : 0 < v := lt_of_lt_of_le hL (mem_Icc.mp hv).1
  have hD : (q*(c+2*v)+s)^2-(q*c+s)^2=(q*(a+2*u)+r)^2-(q*a+r)^2 := by omega
  refine ⟨_,mem_inter.mpr ⟨gap_difference hq hu0 ha,?_⟩,a,c,ha,hc,rfl,hD⟩
  rw [← hD]
  exact gap_difference hq hv0 hc

/-- Distinct short modular matches have distinct actual cross keys. -/
theorem shortKeys_embedding (q H L : ℕ) (R : Finset ℕ) (hL : 0 < L) (hHL : 10*L ≤ H) (hHq : H ≤ q)
    (hR : ∀ r ∈ R, r < q) (hunit : ∀ r ∈ R, q.Coprime (2*r))
    (hgap : ∀ v ∈ Icc L (2*L), q.Coprime v) :
    ∃ f : shortKeys q L R → (Σ _ : ℕ × ℕ, ℕ),
      (∀ k, f k ∈ crossKeys R (fun r => fiberValues q r (Icc 0 H))) ∧
      Function.Injective f ∧ ∀ k, (f k).1=(k.val.1.1,k.val.2.1) := by
  classical
  have hh (k : shortKeys q L R) := mem_shortKeys.mp k.property
  have hex (k : shortKeys q L R) := small_gap_shared_difference hL hHL
    (hh k).2.1 (hh k).2.2.2.1 (hgap _ (hh k).2.2.2.1)
    (hR _ (hh k).1) (hR _ (hh k).2.2.1) (hh k).2.2.2.2.2
  choose D hD a c ha hc hDa hDc using hex
  let f : shortKeys q L R → (Σ _ : ℕ × ℕ, ℕ) := fun k =>
    ⟨(k.val.1.1,k.val.2.1),D k⟩
  refine ⟨f,?_,?_,fun _ => rfl⟩
  · intro k
    exact mem_sigma.mpr ⟨mem_filter.mpr ⟨mem_product.mpr ⟨(hh k).1,(hh k).2.2.1⟩,
      (hh k).2.2.2.2.1⟩,hD k⟩
  · intro k l he
    have hlabels := congrArg Sigma.fst he
    have hdiff := congrArg (fun z : Σ _ : ℕ × ℕ, ℕ => z.2) he
    change (k.val.1.1,k.val.2.1)=(l.val.1.1,l.val.2.1) at hlabels
    have hr := congrArg (fun z : ℕ × ℕ => z.1) hlabels
    have hs := congrArg (fun z : ℕ × ℕ => z.2) hlabels
    change k.val.1.1=l.val.1.1 at hr
    change k.val.2.1=l.val.2.1 at hs
    change D k=D l at hdiff
    have hlu : 0 < l.val.1.2 := lt_of_lt_of_le hL (mem_Icc.mp (hh l).2.1).1
    have hlv : 0 < l.val.2.2 := lt_of_lt_of_le hL (mem_Icc.mp (hh l).2.2.2.1).1
    have hku : 0 < k.val.1.2 := lt_of_lt_of_le hL (mem_Icc.mp (hh k).2.1).1
    have hkv : 0 < k.val.2.2 := lt_of_lt_of_le hL (mem_Icc.mp (hh k).2.2.2.1).1
    have hDa' := hDa l
    have hDc' := hDc l
    rw [← hr,← hdiff] at hDa'
    rw [← hs,← hdiff] at hDc'
    have hu := gap_unique (by omega : 0 < q) (hunit _ (hh k).1) hku hlu ((ha k).trans hHq) ((ha l).trans hHq) (hDa k) hDa'
    have hv := gap_unique (by omega : 0 < q) (hunit _ (hh k).2.2.1) hkv hlv ((hc k).trans hHq) ((hc l).trans hHq) (hDc k) hDc'
    apply Subtype.ext
    exact Prod.ext (Prod.ext hr hu) (Prod.ext hs hv)

/-- Weighted overlap count forced by the same injection. -/
theorem shortKeys_weight_le (q H L : ℕ) (R : Finset ℕ) (hL : 0 < L) (hHL : 10*L ≤ H) (hHq : H ≤ q)
    (hR : ∀ r ∈ R, r < q) (hunit : ∀ r ∈ R, q.Coprime (2*r))
    (hgap : ∀ v ∈ Icc L (2*L), q.Coprime v) (p : ℕ → ℝ) :
    (∑ k ∈ shortKeys q L R, p k.1.1^2*p k.2.1^2) ≤
      ∑ k ∈ crossKeys R (fun r => fiberValues q r (Icc 0 H)), p k.1.1^2*p k.1.2^2 := by
  classical
  obtain ⟨f,hf,hi,hlabels⟩ := shortKeys_embedding q H L R hL hHL hHq hR hunit hgap
  let w (k : Σ _ : ℕ × ℕ, ℕ) : ℝ := p k.1.1^2*p k.1.2^2
  have hsub : (univ.image f) ⊆ crossKeys R (fun r => fiberValues q r (Icc 0 H)) := by
    intro k hk
    obtain ⟨l,_,rfl⟩ := mem_image.mp hk
    exact hf l
  have hle := sum_le_sum_of_subset_of_nonneg (f := w) hsub
    (fun k _ _ => mul_nonneg (sq_nonneg _) (sq_nonneg _))
  rw [sum_image hi.injOn] at hle
  have hw (k : shortKeys q L R) : w (f k)=p k.val.1.1^2*p k.val.2.1^2 := by
    dsimp [w]
    rw [hlabels]
  simp_rw [hw] at hle
  have heq := sum_coe_sort (shortKeys q L R) (fun k => p k.1.1^2*p k.2.1^2)
  rw [heq] at hle
  exact hle

/-- A prime modulus supplies the small-gap unit condition automatically. -/
theorem prime_shortKeys_weight_le (q H L : ℕ) (R : Finset ℕ) (hq : q.Prime)
    (hL : 0 < L) (hHL : 10*L ≤ H) (hHq : H ≤ q)
    (hR : ∀ r ∈ R, r < q) (hunit : ∀ r ∈ R, q.Coprime (2*r)) (p : ℕ → ℝ) :
    (∑ k ∈ shortKeys q L R, p k.1.1^2*p k.2.1^2) ≤
      ∑ k ∈ crossKeys R (fun r => fiberValues q r (Icc 0 H)), p k.1.1^2*p k.1.2^2 := by
  apply shortKeys_weight_le q H L R hL hHL hHq hR hunit _ p
  intro v hv
  apply hq.coprime_iff_not_dvd.mpr
  apply Nat.not_dvd_of_pos_of_lt
  · exact lt_of_lt_of_le hL (mem_Icc.mp hv).1
  · have hh := (mem_Icc.mp hv).2
    omega

/-- Every short modular collision counted by pigeonhole is paid for by the
actual full-fiber overlap budget. -/
theorem full_weight_pigeonhole (q H L : ℕ) (R : Finset ℕ) (hq : q.Prime)
    (hL : 0 < L) (hHL : 10*L ≤ H) (hHq : H ≤ q)
    (hR : ∀ r ∈ R, r < q) (hunit : ∀ r ∈ R, q.Coprime (2*r)) (p : ℕ → ℝ) :
    ((L+1 : ℕ)*(∑ r ∈ R, p r^2) : ℝ)^2 ≤ (q : ℝ)*
      (((L+1 : ℕ) : ℝ)*(∑ r ∈ R, p r^4) +
        2*(∑ k ∈ crossKeys R (fun r => fiberValues q r (Icc 0 H)), p k.1.1^2*p k.1.2^2)) := by
  have hh := short_weight_pigeonhole q L R hq.pos (by omega)
    (fun r hr => Nat.Coprime.of_dvd_right (dvd_mul_left r 2) (hunit r hr)) p
  have hc := prime_shortKeys_weight_le q H L R hq hL hHL hHq hR hunit p
  have hq0 : (0:ℝ) ≤ q := Nat.cast_nonneg q
  nlinarith only [hh,mul_le_mul_of_nonneg_left hc hq0]

#print axioms small_gap_shared_difference
#print axioms prime_shortKeys_weight_le
#print axioms full_weight_pigeonhole
end Erdos773.ShortFullFiberOverlap
