import Submission.ResidueFibers

/-!
A sufficient modular criterion for a union of full arithmetic-progression
fibers to have Sidon squares. The criterion has a two-thirds exponent ceiling;
that ceiling is NOT an upper bound for arbitrary subsets of squares.
-/
namespace Erdos773.MatchedResidueLifting
open Finset
set_option maxHeartbeats 1000000

/-- Square-sum residues identify the unordered pair of root residues. -/
def PairMatching (q : ℕ) (R : Finset ℕ) : Prop :=
  ∀ r ∈ R, ∀ s ∈ R, ∀ t ∈ R, ∀ u ∈ R,
    r^2+s^2 ≡ t^2+u^2 [MOD q] →
    (r=t ∧ s=u) ∨ (r=u ∧ s=t)

/-- Different residue/index pairs give different short products modulo q.
The factor two is included to avoid an implicit cancellation assumption. -/
def ShortProducts (q H : ℕ) (R : Finset ℕ) : Prop :=
  Set.InjOn (fun p : ℕ × ℕ => (2*p.1*p.2)%q)
    ((R ×ˢ (Icc 1 H : Finset ℕ) : Finset (ℕ × ℕ)) : Set (ℕ × ℕ))

/-- The full fibers, including index zero. -/
def roots (q H : ℕ) (R : Finset ℕ) : Finset ℕ :=
  (R ×ˢ Icc 0 H).image (fun p => q*p.2+p.1)

private lemma matched_collision (q H r s a b c d : ℕ) (hq : 0 < q)
    (hr : q.Coprime (2*r))
    (hH : H ≤ q) (ha : a ≤ H) (hb : b ≤ H) (hc : c ≤ H) (hd : d ≤ H)
    {R : Finset ℕ} (hrR : r ∈ R) (hsR : s ∈ R)
    (hP : ShortProducts q H R)
    (he : (q*a+r)^2+(q*b+s)^2 = (q*c+r)^2+(q*d+s)^2) :
    (q*a+r=q*c+r ∧ q*b+s=q*d+s) ∨
    (q*a+r=q*d+s ∧ q*b+s=q*c+r) := by
  by_cases hrs : r=s
  · subst s
    rcases ResidueFibers.unit_progression_collision q r a b c d hq hr
      (ha.trans hH) (hb.trans hH) (hc.trans hH) (hd.trans hH) he with h | h
    · left; simp [h.1,h.2]
    · right; simp [h.1,h.2]
  have hn : q*(a^2+b^2)+2*r*a+2*s*b =
      q*(c^2+d^2)+2*r*c+2*s*d := by
    apply Nat.eq_of_mul_eq_mul_left hq
    nlinarith only [he]
  have hmod : 2*r*a+2*s*b ≡ 2*r*c+2*s*d [MOD q] := by
    have hh := congrArg (fun n : ℕ => n%q) hn
    simpa only [Nat.ModEq, Nat.add_mod, Nat.mul_mod_right,
      zero_add, Nat.mod_mod] using hh
  have heq : a=c := by
    rcases lt_trichotomy a c with hac | hac | hca
    · have hdb : d < b := by
        by_contra! h
        have h1 : q*a+r < q*c+r := by nlinarith
        have h2 : q*b+s ≤ q*d+s := by nlinarith
        nlinarith only [he,h1,h2, Nat.zero_le (q*a+r), Nat.zero_le (q*b+s)]
      have hp : 2*r*(c-a) ≡ 2*s*(b-d) [MOD q] := by
        have hc' := Nat.sub_add_cancel hac.le
        have hb' := Nat.sub_add_cancel hdb.le
        have hh : 2*r*a+2*s*d+2*s*(b-d) ≡
            2*r*a+2*s*d+2*r*(c-a) [MOD q] := by
          convert hmod using 1 <;> nlinarith only [hc',hb']
        exact (Nat.ModEq.add_left_cancel' _ hh).symm
      have hh : (r,c-a)=(s,b-d) :=
        hP (mem_product.mpr ⟨hrR, mem_Icc.mpr ⟨by omega,by omega⟩⟩)
          (mem_product.mpr ⟨hsR, mem_Icc.mpr ⟨by omega,by omega⟩⟩) hp
      exact (hrs (congrArg Prod.fst hh)).elim
    · exact hac
    · have hbd : b < d := by
        by_contra! h
        have h1 : q*c+r < q*a+r := by nlinarith
        have h2 : q*d+s ≤ q*b+s := by nlinarith
        nlinarith only [he,h1,h2, Nat.zero_le (q*c+r), Nat.zero_le (q*d+s)]
      have hp : 2*r*(a-c) ≡ 2*s*(d-b) [MOD q] := by
        have ha' := Nat.sub_add_cancel hca.le
        have hd' := Nat.sub_add_cancel hbd.le
        have hh : 2*r*c+2*s*b+2*r*(a-c) ≡
            2*r*c+2*s*b+2*s*(d-b) [MOD q] := by
          convert hmod using 1 <;> nlinarith only [ha',hd']
        exact Nat.ModEq.add_left_cancel' _ hh
      have hh : (r,a-c)=(s,d-b) :=
        hP (mem_product.mpr ⟨hrR, mem_Icc.mpr ⟨by omega,by omega⟩⟩)
          (mem_product.mpr ⟨hsR, mem_Icc.mpr ⟨by omega,by omega⟩⟩) hp
      exact (hrs (congrArg Prod.fst hh)).elim
  have hbd : b=d := by
    subst c
    have hh : (q*b+s)^2=(q*d+s)^2 := by omega
    have hh' := Nat.pow_left_injective (by decide : (2 : ℕ) ≠ 0) hh
    nlinarith
  left
  simp [heq,hbd]

/-- A genuine sufficient condition for the union, not just its individual fibers. -/
theorem squares_sidon (q H : ℕ) (R : Finset ℕ) (hq : 0 < q)
    (hH : H ≤ q) (hunit : ∀ r ∈ R, q.Coprime (2*r))
    (hM : PairMatching q R) (hP : ShortProducts q H R) :
    IsSidon (((roots q H R).image (fun n => n^2)) : Set ℕ) := by
  intro a ha c hc b hb d hd he
  simp only [mem_coe, mem_image, roots, mem_product, mem_Icc] at ha hc hb hd
  obtain ⟨_, ⟨⟨r,i⟩, ⟨hr,_,hi⟩, rfl⟩, rfl⟩ := ha
  obtain ⟨_, ⟨⟨t,k⟩, ⟨ht,_,hk⟩, rfl⟩, rfl⟩ := hc
  obtain ⟨_, ⟨⟨s,j⟩, ⟨hs,_,hj⟩, rfl⟩, rfl⟩ := hb
  obtain ⟨_, ⟨⟨u,l⟩, ⟨hu,_,hl⟩, rfl⟩, rfl⟩ := hd
  dsimp only [Prod.fst,Prod.snd] at *
  have hm : r^2+s^2 ≡ t^2+u^2 [MOD q] := by
    have hh := congrArg (fun n : ℕ => n%q) he
    simpa only [Nat.ModEq, Nat.add_mod, Nat.mul_mod_right,
      zero_add, Nat.pow_mod, Nat.mod_mod] using hh
  rcases hM r hr s hs t ht u hu hm with ⟨hrt,hsu⟩ | ⟨hru,hst⟩
  · subst t; subst u
    rcases matched_collision q H r s i j k l hq (hunit r hr) hH hi hj hk hl
      hr hs hP he with h | h
    · left; simp [h.1,h.2]
    · right; simp [h.1,h.2]
  · subst u; subst t
    have he' : (q*i+r)^2+(q*j+s)^2=(q*l+r)^2+(q*k+s)^2 := by omega
    rcases matched_collision q H r s i j l k hq (hunit r hr) hH hi hj hl hk
      hr hs hP he' with h | h
    · right; simp [h.1,h.2]
    · left; simp [h.1,h.2]

/-- The number of roots retained by the full-fiber construction. -/
theorem roots_card (q H : ℕ) (R : Finset ℕ) (hq : 0 < q)
    (hR : ∀ r ∈ R, r < q) :
    (roots q H R).card = R.card*(H+1) := by
  rw [roots, card_image_of_injOn]
  · simp
  · rintro ⟨r,i⟩ hp ⟨s,j⟩ hp' he
    have hr := hR r (mem_product.mp hp).1
    have hs := hR s (mem_product.mp hp').1
    have hh := congrArg (fun n : ℕ => n%q) he
    simp only [Nat.add_mod, Nat.mul_mod_right, zero_add, Nat.mod_eq_of_lt hr,
      Nat.mod_eq_of_lt hs] at hh
    apply Prod.ext hh
    dsimp at he
    change i=j
    apply Nat.eq_of_mul_eq_mul_left hq
    change q*i=q*j
    omega

/-- Every positive canonical residue gives roots inside the claimed ambient interval. -/
theorem roots_subset (q H : ℕ) (R : Finset ℕ)
    (hR : ∀ r ∈ R, 1 ≤ r ∧ r < q) : roots q H R ⊆ Icc 1 (q*(H+1)) := by
  intro n hn
  obtain ⟨⟨r,k⟩,hp,rfl⟩ := mem_image.mp hn
  obtain ⟨hr,hk⟩ := mem_product.mp hp
  obtain ⟨hr1,hrq⟩ := hR r hr
  have hkH := (mem_Icc.mp hk).2
  apply mem_Icc.mpr
  constructor
  · dsimp; omega
  · dsimp; nlinarith

/-- The criterion supplies an actual lower bound, subject to all its hypotheses. -/
theorem finite_lower (q H : ℕ) (R : Finset ℕ) (hq : 0 < q)
    (hH : H ≤ q) (hR : ∀ r ∈ R, 1 ≤ r ∧ r < q)
    (hunit : ∀ r ∈ R, q.Coprime (2*r))
    (hM : PairMatching q R) (hP : ShortProducts q H R) :
    R.card*(H+1) ≤ maxSidonSubsetCard
      ((Icc 1 (q*(H+1))).image (fun n : ℕ => n^2)) := by
  have hc : ((roots q H R).image (fun n => n^2)).card = R.card*(H+1) := by
    rw [card_image_of_injective _ (Nat.pow_left_injective (by decide : (2 : ℕ) ≠ 0))]
    exact roots_card q H R hq (fun r hr => (hR r hr).2)
  rw [← hc]
  apply le_sup
  exact mem_filter.mpr ⟨mem_powerset.mpr (image_subset_image (roots_subset q H R hR)),
    squares_sidon q H R hq hH hunit hM hP⟩

/-- Modular pair matching alone has the usual square-root cardinality bound. -/
theorem pairMatching_card (q : ℕ) (R : Finset ℕ) (hq : 0 < q)
    (hM : PairMatching q R) : R.card^2 ≤ 2*q := by
  let f : ℕ × ℕ → ℕ × Bool := fun p => ((p.1^2+p.2^2)%q, decide (p.1 ≤ p.2))
  have hc : (R ×ˢ R).card ≤ ((range q) ×ˢ (univ : Finset Bool)).card := by
    apply card_le_card_of_injOn f
    · intro p hp
      exact mem_product.mpr ⟨mem_range.mpr (Nat.mod_lt _ hq),mem_univ _⟩
    · rintro ⟨r,s⟩ hp ⟨t,u⟩ hp' he
      obtain ⟨hr,hs⟩ := mem_product.mp hp
      obtain ⟨ht,hu⟩ := mem_product.mp hp'
      have hsum : r^2+s^2 ≡ t^2+u^2 [MOD q] := congrArg Prod.fst he
      have hord : (r ≤ s) ↔ (t ≤ u) := by
        have hh : decide (r ≤ s) = decide (t ≤ u) := congrArg Prod.snd he
        simpa using hh
      rcases hM r hr s hs t ht u hu hsum with h | h
      · exact Prod.ext h.1 h.2
      · apply Prod.ext <;> omega
  simpa [pow_two, mul_comm] using hc

/-- Injectivity of the short products uses one residue per product. -/
theorem shortProducts_card (q H : ℕ) (R : Finset ℕ) (hq : 0 < q)
    (hP : ShortProducts q H R) : R.card*H ≤ q := by
  have hc : (R ×ˢ Icc 1 H).card ≤ (range q).card := by
    apply card_le_card_of_injOn (fun p : ℕ × ℕ => (2*p.1*p.2)%q)
    · intro p hp
      exact mem_range.mpr (Nat.mod_lt _ hq)
    · exact hP
  simpa using hc

/-- Ceiling for this sufficient criterion only. N=q(H+1) bounds its root
height. No bound for the original Sidon maximum follows from this theorem. -/
theorem criterion_card_ceiling (q H : ℕ) (R : Finset ℕ) (hq : 0 < q)
    (hH : 1 ≤ H) (hR : ∀ r ∈ R, r < q)
    (hM : PairMatching q R) (hP : ShortProducts q H R) :
    (roots q H R).card^3 ≤ 4*(q*(H+1))^2 := by
  rw [roots_card q H R hq hR]
  have h1 := pairMatching_card q R hq hM
  have h2 := shortProducts_card q H R hq hP
  have h3 : R.card*(H+1) ≤ 2*q := by
    have hh := Nat.mul_le_mul_left R.card hH
    nlinarith only [h2,hh]
  calc
    _ = R.card^2*(H+1)^2*(R.card*(H+1)) := by ring
    _ ≤ (2*q)*(H+1)^2*(2*q) :=
      Nat.mul_le_mul (Nat.mul_le_mul_right _ h1) h3
    _ = _ := by ring

/-- A small nonvacuous application with three full fibers. -/
theorem three_fiber_example :
    IsSidon (((roots 101 3 {1,4,13}).image (fun n => n^2)) : Set ℕ) := by
  apply squares_sidon 101 3 {1,4,13} (by decide) (by decide)
  · intro r hr
    simp only [mem_insert, mem_singleton] at hr
    rcases hr with rfl | rfl | rfl <;> decide
  · unfold PairMatching
    decide +kernel
  · unfold ShortProducts
    decide +kernel

#print axioms roots_subset
#print axioms finite_lower
#print axioms three_fiber_example
#print axioms squares_sidon
#print axioms roots_card
#print axioms pairMatching_card
#print axioms shortProducts_card
#print axioms criterion_card_ceiling
end Erdos773.MatchedResidueLifting
