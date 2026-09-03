import Submission.WeightedPartialFibers

/-!
Small modular gap matches force genuine shared differences between full short
square fibers. These lemmas concern full fibers, not arbitrary partial index
sets and not the original maximum over all subsets of squares.
-/
namespace Erdos773.FullFiberOverlap
open Finset PartialResidueFibers PartialFiberSelection MatchedResidueLifting
set_option maxHeartbeats 2000000

lemma residue_preimage {q v r : ℕ} (hq : 0 < q) (hv : q.Coprime v) (hr : r < q) :
    ∃ t < q, v*t%q=r := by
  let f : Fin q → Fin q := fun t => ⟨v*t.val%q,Nat.mod_lt _ hq⟩
  have hi : Function.Injective f := by
    intro a b he
    have hh : v*a.val ≡ v*b.val [MOD q] := congrArg Fin.val he
    exact Fin.ext ((hh.cancel_left_of_coprime hv).eq_of_lt_of_lt a.isLt b.isLt)
  obtain ⟨t,ht⟩ := Finite.surjective_of_injective hi ⟨r,hr⟩
  exact ⟨t.val,t.isLt,congrArg Fin.val ht⟩

/-- One modular ratio determines both center congruences. -/
lemma common_multiplier {q r s u v : ℕ} (hq : 0 < q) (hv : q.Coprime v)
    (hr : r < q) (hs : s < q) (he : r*u ≡ s*v [MOD q]) :
    ∃ t < q, v*t%q=r ∧ u*t%q=s := by
  obtain ⟨t,ht,hrt⟩ := residue_preimage hq hv hr
  refine ⟨t,ht,hrt,?_⟩
  have hrmod : v*t ≡ r [MOD q] := by simpa [Nat.ModEq,Nat.mod_eq_of_lt hr] using hrt
  have hm : v*(u*t) ≡ v*s [MOD q] := by
    have hh := (hrmod.mul_right u).trans he
    simpa only [mul_comm,mul_left_comm,mul_assoc] using hh
  have hh := hm.cancel_left_of_coprime hv
  simpa only [Nat.ModEq,Nat.mod_eq_of_lt hs] using hh

/-- Choosing the common multiplier t+3q puts all four endpoints below 10L. -/
theorem small_gap_collision {q L r s u v : ℕ} (hL : 0 < L)
    (hu : u ∈ Icc L (2*L)) (hv : v ∈ Icc L (2*L))
    (hcop : q.Coprime v) (hr : r < q) (hs : s < q)
    (he : r*u ≡ s*v [MOD q]) :
    ∃ a c : ℕ, a+2*u ≤ 10*L ∧ c+2*v ≤ 10*L ∧
      (q*(a+2*u)+r)^2+(q*c+s)^2 = (q*a+r)^2+(q*(c+2*v)+s)^2 := by
  have hq : 0 < q := by omega
  obtain ⟨hu1,hu2⟩ := mem_Icc.mp hu
  obtain ⟨hv1,hv2⟩ := mem_Icc.mp hv
  have hu0 : 0 < u := by omega
  have hv0 : 0 < v := by omega
  obtain ⟨t,ht,hrt,hst⟩ := common_multiplier hq hcop hr hs he
  have htU : u*t/q < u := (Nat.div_lt_iff_lt_mul hq).mpr (by nlinarith)
  have htV : v*t/q < v := (Nat.div_lt_iff_lt_mul hq).mpr (by nlinarith)
  let a := 3*v+v*t/q-u
  let c := 3*u+u*t/q-v
  have huv : u ≤ 3*v := by omega
  have hvu : v ≤ 3*u := by omega
  have ha : a+u=3*v+v*t/q := Nat.sub_add_cancel (huv.trans (Nat.le_add_right _ _))
  have hc : c+v=3*u+u*t/q := Nat.sub_add_cancel (hvu.trans (Nat.le_add_right _ _))
  have haQ : a+2*u ≤ 10*L := by omega
  have hcQ : c+2*v ≤ 10*L := by omega
  have hrdiv : q*(a+u)+r=v*(3*q+t) := by
    have hh := Nat.mod_add_div (v*t) q
    rw [hrt] at hh
    rw [ha]
    nlinarith only [hh]
  have hsdiv : q*(c+v)+s=u*(3*q+t) := by
    have hh := Nat.mod_add_div (u*t) q
    rw [hst] at hh
    rw [hc]
    nlinarith only [hh]
  refine ⟨a,c,haQ,hcQ,?_⟩
  have hh : u*(q*(a+u)+r)=v*(q*(c+v)+s) := by rw [hrdiv,hsdiv]; ring
  nlinarith only [congrArg (fun n => 4*q*n) hh]

/-- The exact difference with gap 2u in a full fiber. -/
lemma gap_difference {q r u a : ℕ} (hq : 0 < q) (hu : 0 < u) (ha : a+2*u ≤ q) :
    (q*(a+2*u)+r)^2-(q*a+r)^2 ∈ positiveDiffs (fiberValues q r (Icc 0 q)) := by
  apply mem_positiveDiffs.mpr
  refine ⟨(q*a+r)^2,mem_image.mpr ⟨a,mem_Icc.mpr ⟨Nat.zero_le _,by omega⟩,rfl⟩,
    (q*(a+2*u)+r)^2,mem_image.mpr ⟨a+2*u,mem_Icc.mpr ⟨Nat.zero_le _,ha⟩,rfl⟩,?_,rfl⟩
  apply Nat.pow_lt_pow_left _ (by decide : (2 : ℕ) ≠ 0)
  exact Nat.add_lt_add_right (Nat.mul_lt_mul_of_pos_left (by omega : a < a+2*u) hq) r

/-- Each modular match of small gaps yields an actual common positive
difference, with the prescribed endpoint gaps in each fiber. -/
theorem small_gap_shared_difference {q L r s u v : ℕ} (hL : 0 < L)
    (hqL : 10*L ≤ q) (hu : u ∈ Icc L (2*L)) (hv : v ∈ Icc L (2*L))
    (hcop : q.Coprime v) (hr : r < q) (hs : s < q)
    (he : r*u ≡ s*v [MOD q]) :
    ∃ D ∈ positiveDiffs (fiberValues q r (Icc 0 q)) ∩
        positiveDiffs (fiberValues q s (Icc 0 q)),
      ∃ a c : ℕ, a+2*u ≤ q ∧ c+2*v ≤ q ∧
        (q*(a+2*u)+r)^2-(q*a+r)^2=D ∧
        (q*(c+2*v)+s)^2-(q*c+s)^2=D := by
  obtain ⟨a,c,ha,hc,he⟩ := small_gap_collision hL hu hv hcop hr hs he
  have ha := ha.trans hqL
  have hc := hc.trans hqL
  have hq : 0 < q := by omega
  have hu0 : 0 < u := lt_of_lt_of_le hL (mem_Icc.mp hu).1
  have hv0 : 0 < v := lt_of_lt_of_le hL (mem_Icc.mp hv).1
  have hD : (q*(c+2*v)+s)^2-(q*c+s)^2=(q*(a+2*u)+r)^2-(q*a+r)^2 := by omega
  refine ⟨_,mem_inter.mpr ⟨gap_difference hq hu0 ha,?_⟩,a,c,ha,hc,rfl,hD⟩
  rw [← hD]
  exact gap_difference hq hv0 hc

/-- Sidon endpoint uniqueness makes the prescribed gap recoverable from D. -/
lemma gap_unique {q r u v a b D : ℕ} (hq : 0 < q) (hcop : q.Coprime (2*r))
    (hu : 0 < u) (hv : 0 < v) (ha : a+2*u ≤ q) (hb : b+2*v ≤ q)
    (hDa : (q*(a+2*u)+r)^2-(q*a+r)^2=D)
    (hDb : (q*(b+2*v)+r)^2-(q*b+r)^2=D) : u=v := by
  have hs := ResidueFibers.unit_progression_squares_sidon q r hq hcop
  have hmem (i : ℕ) (hi : i ≤ q) : (q*i+r)^2 ∈ (Icc 0 q).image (fun j => (q*j+r)^2) :=
    mem_image.mpr ⟨i,mem_Icc.mpr ⟨Nat.zero_le _,hi⟩,rfl⟩
  have hlt (i j : ℕ) (hj : 0 < j) : (q*i+r)^2 < (q*(i+2*j)+r)^2 := by
    apply Nat.pow_lt_pow_left _ (by decide : (2 : ℕ) ≠ 0)
    nlinarith
  obtain ⟨h1,h2⟩ := endpoints_unique hs (hmem a (by omega)) (hmem (a+2*u) ha)
    (hmem b (by omega)) (hmem (b+2*v) hb) (hlt a u hu) (hlt b v hv) (hDa.trans hDb.symm)
  have h1' := Nat.pow_left_injective (by decide : (2 : ℕ) ≠ 0) h1
  have h2' := Nat.pow_left_injective (by decide : (2 : ℕ) ≠ 0) h2
  have hab : a=b := by nlinarith only [h1',hq]
  have huv : a+2*u=b+2*v := by nlinarith only [h2',hq]
  omega

/-- Ordered by the two labels, so each distinct-label match is counted once. -/
def shortKeys (q L : ℕ) (R : Finset ℕ) : Finset ((ℕ × ℕ) × (ℕ × ℕ)) :=
  (((R ×ˢ Icc L (2*L)) ×ˢ (R ×ˢ Icc L (2*L)))).filter
    (fun k => k.1.1 < k.2.1 ∧ k.1.1*k.1.2 ≡ k.2.1*k.2.2 [MOD q])

lemma mem_shortKeys {q L : ℕ} {R : Finset ℕ} {k : (ℕ × ℕ) × (ℕ × ℕ)} :
    k ∈ shortKeys q L R ↔ k.1.1 ∈ R ∧ k.1.2 ∈ Icc L (2*L) ∧
      k.2.1 ∈ R ∧ k.2.2 ∈ Icc L (2*L) ∧ k.1.1 < k.2.1 ∧
      k.1.1*k.1.2 ≡ k.2.1*k.2.2 [MOD q] := by
  simp only [shortKeys,mem_filter,mem_product]
  tauto

/-- Distinct short modular matches have distinct actual cross keys. -/
theorem shortKeys_embedding (q L : ℕ) (R : Finset ℕ) (hL : 0 < L) (hqL : 10*L ≤ q)
    (hR : ∀ r ∈ R, r < q) (hunit : ∀ r ∈ R, q.Coprime (2*r))
    (hgap : ∀ v ∈ Icc L (2*L), q.Coprime v) :
    ∃ f : shortKeys q L R → (Σ _ : ℕ × ℕ, ℕ),
      (∀ k, f k ∈ crossKeys R (fun r => fiberValues q r (Icc 0 q))) ∧
      Function.Injective f ∧ ∀ k, (f k).1=(k.val.1.1,k.val.2.1) := by
  classical
  have hh (k : shortKeys q L R) := mem_shortKeys.mp k.property
  have hex (k : shortKeys q L R) := small_gap_shared_difference hL hqL
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
    have hu := gap_unique (by omega : 0 < q) (hunit _ (hh k).1) hku hlu (ha k) (ha l) (hDa k) hDa'
    have hv := gap_unique (by omega : 0 < q) (hunit _ (hh k).2.2.1) hkv hlv (hc k) (hc l) (hDc k) hDc'
    apply Subtype.ext
    exact Prod.ext (Prod.ext hr hu) (Prod.ext hs hv)

/-- Raw overlap count forced by short modular matches. -/
theorem shortKeys_card_le (q L : ℕ) (R : Finset ℕ) (hL : 0 < L) (hqL : 10*L ≤ q)
    (hR : ∀ r ∈ R, r < q) (hunit : ∀ r ∈ R, q.Coprime (2*r))
    (hgap : ∀ v ∈ Icc L (2*L), q.Coprime v) :
    (shortKeys q L R).card ≤ (crossKeys R (fun r => fiberValues q r (Icc 0 q))).card := by
  classical
  obtain ⟨f,hf,hi,_⟩ := shortKeys_embedding q L R hL hqL hR hunit hgap
  have hc := card_le_card_of_injOn (s := univ) f (fun k _ => hf k) hi.injOn
  simpa using hc

/-- Weighted overlap count forced by the same injection. -/
theorem shortKeys_weight_le (q L : ℕ) (R : Finset ℕ) (hL : 0 < L) (hqL : 10*L ≤ q)
    (hR : ∀ r ∈ R, r < q) (hunit : ∀ r ∈ R, q.Coprime (2*r))
    (hgap : ∀ v ∈ Icc L (2*L), q.Coprime v) (p : ℕ → ℝ) :
    (∑ k ∈ shortKeys q L R, p k.1.1^2*p k.2.1^2) ≤
      ∑ k ∈ crossKeys R (fun r => fiberValues q r (Icc 0 q)), p k.1.1^2*p k.1.2^2 := by
  classical
  obtain ⟨f,hf,hi,hlabels⟩ := shortKeys_embedding q L R hL hqL hR hunit hgap
  let w (k : Σ _ : ℕ × ℕ, ℕ) : ℝ := p k.1.1^2*p k.1.2^2
  have hsub : (univ.image f) ⊆ crossKeys R (fun r => fiberValues q r (Icc 0 q)) := by
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
theorem prime_shortKeys_weight_le (q L : ℕ) (R : Finset ℕ) (hq : q.Prime)
    (hL : 0 < L) (hqL : 10*L ≤ q)
    (hR : ∀ r ∈ R, r < q) (hunit : ∀ r ∈ R, q.Coprime (2*r)) (p : ℕ → ℝ) :
    (∑ k ∈ shortKeys q L R, p k.1.1^2*p k.2.1^2) ≤
      ∑ k ∈ crossKeys R (fun r => fiberValues q r (Icc 0 q)), p k.1.1^2*p k.1.2^2 := by
  apply shortKeys_weight_le q L R hL hqL hR hunit _ p
  intro v hv
  apply hq.coprime_iff_not_dvd.mpr
  apply Nat.not_dvd_of_pos_of_lt
  · exact lt_of_lt_of_le hL (mem_Icc.mp hv).1
  · have hh := (mem_Icc.mp hv).2
    omega

#print axioms small_gap_shared_difference
#print axioms gap_unique
#print axioms shortKeys_card_le
#print axioms prime_shortKeys_weight_le
end Erdos773.FullFiberOverlap
