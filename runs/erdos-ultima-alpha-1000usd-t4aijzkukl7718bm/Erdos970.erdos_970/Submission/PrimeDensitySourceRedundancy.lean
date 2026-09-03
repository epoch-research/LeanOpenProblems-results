import Submission.UnionSourceRedundancy
import Submission.RecursiveDensityScaling
import Submission.UnionSeededTransfer

/-! Full overlap-aware source redundancy at initial-prime reference prefixes.
This removes the large-missing-prime restriction by comparing the density of
the entire union with the first j primes. Arithmetic source bounds not certified
by the same plain envelope remain outside the theorem. -/
namespace Erdos970.RecursiveSieve
open Finset FiniteSelberg GapAverages

noncomputable def firstPrimeMarginal (i : ℕ) : ℝ := 1/(Nat.nth Nat.Prime i : ℝ)

lemma firstPrimeMarginal_valid (i : ℕ) :
    0 ≤ firstPrimeMarginal i ∧ firstPrimeMarginal i < 1 := by
  have hp : (1 : ℝ) < Nat.nth Nat.Prime i := by exact_mod_cast (Nat.prime_nth_prime i).one_lt
  exact ⟨by unfold firstPrimeMarginal; positivity,
    (div_lt_one (by linarith)).mpr hp⟩

lemma firstPrimeDensity_pos (k : ℕ) : 0 < prefixDensity firstPrimeMarginal k :=
  prod_pos (fun i _ => sub_pos.mpr (firstPrimeMarginal_valid i).2)

/-- Initial primes minimize density among prime sets of a fixed size. -/
theorem firstPrimeDensity_le (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (k : ℕ) (hPk : P.card ≤ k) : prefixDensity firstPrimeMarginal k ≤ density P := by
  let p : Fin P.card → ℕ := P.orderEmbOfFin rfl
  have hp : ∀ i, (p i).Prime := fun i => hP _ (P.orderEmbOfFin_mem rfl i)
  have hmono : StrictMono p := (P.orderEmbOfFin rfl).strictMono
  have he : (univ : Finset (Fin P.card)).image p = P := image_orderEmbOfFin_univ P rfl
  have hprod : density P = ∏ i : Fin P.card, (1-1/(p i : ℝ)) := by
    conv_lhs => rw [← he]
    exact density_image_eq p hmono.injective univ
  have hbase : prefixDensity firstPrimeMarginal P.card ≤ density P := by
    rw [hprod,prefixDensity,← Fin.prod_univ_eq_prod_range (fun i => 1-firstPrimeMarginal i) P.card]
    apply prod_le_prod
    · intro i hi
      exact sub_nonneg.mpr (firstPrimeMarginal_valid i.val).2.le
    · intro i hi
      apply sub_le_sub_left
      have hpi : (0 : ℝ) < Nat.nth Nat.Prime i.val := by
        exact_mod_cast (Nat.prime_nth_prime i.val).pos
      exact one_div_le_one_div_of_le hpi (by exact_mod_cast nth_prime_le_sorted p hp hmono i)
  exact (prefixDensity_antitone firstPrimeMarginal
    (fun i => ⟨(firstPrimeMarginal_valid i).1,(firstPrimeMarginal_valid i).2.le⟩) hPk).trans hbase

/-- Density of the image of an initial segment of the reference list. -/
lemma firstPrimeDensity_prefix_image (K n : ℕ) (hn : n ≤ K) :
    density ((prefixIndices K n).image (fun i : Fin K => Nat.nth Nat.Prime i.val)) =
      prefixDensity firstPrimeMarginal n := by
  have he : (prefixIndices K n).image (fun i : Fin K => Nat.nth Nat.Prime i.val) =
      (range n).image (Nat.nth Nat.Prime) := by
    ext p
    simp only [mem_image,mem_range]
    constructor
    · rintro ⟨i,hi,he⟩
      exact ⟨i.val,(mem_filter.mp hi).2,he⟩
    · rintro ⟨i,hi,he⟩
      exact ⟨⟨i,hi.trans_le hn⟩,mem_filter.mpr ⟨mem_univ _,hi⟩,he⟩
  rw [he]
  unfold density prefixDensity firstPrimeMarginal
  exact prod_image (Nat.nth_strictMono Nat.infinite_setOf_prime).injective.injOn

/-- A union source at the first n reference primes is already below the local
plain envelope whenever its own length has a plain positive certificate at j.
No pointwise lower bound on missing prime sizes is required. -/
theorem firstPrime_unionSource_le_of_plain_certificate
    (K n j : ℕ) (hn : n ≤ K) (p : Fin K → ℕ) (hp : ∀ i, (p i).Prime)
    (g : ℝ) (hg : 0 < g)
    (hpos : 0 < (linearEnvelope firstPrimeMarginal j g).1) (x : ℝ) :
    max 0 (unionSourceGain p (fun i => Nat.nth Nat.Prime i.val) (prefixIndices K n) j/g*(x-1)-
      unionSourceGain p (fun i => Nat.nth Nat.Prime i.val) (prefixIndices K n) j) ≤
        (linearEnvelope firstPrimeMarginal n x).1 := by
  let B := prefixIndices K n
  let v (i : Fin K) := Nat.nth Nat.Prime i.val
  let P := B.image p
  let Q := B.image v
  let U := P ∪ Q
  let R := P \ Q
  let t := unionSourceGain p v B j
  have hP : ∀ r ∈ P, r.Prime := by
    intro r hr
    obtain ⟨i,_,rfl⟩ := mem_image.mp hr
    exact hp i
  have hQ : ∀ r ∈ Q, r.Prime := by
    intro r hr
    obtain ⟨i,_,rfl⟩ := mem_image.mp hr
    exact Nat.prime_nth_prime _
  have hU : ∀ r ∈ U, r.Prime := by
    intro r hr
    rcases mem_union.mp hr with hr | hr
    · exact hP r hr
    · exact hQ r hr
  have hR : ∀ r ∈ R, r.Prime := fun r hr => hP r (mem_sdiff.mp hr).1
  have hQn : Q.card = n := by
    have hvinj : Function.Injective v := by
      intro i l he
      exact Fin.ext ((Nat.nth_strictMono Nat.infinite_setOf_prime).injective he)
    rw [card_image_of_injective B hvinj]
    exact prefixIndices_card K n hn
  have hnU : n ≤ U.card := by rw [← hQn]; exact card_le_card subset_union_right
  have ht0 : 0 ≤ t := unionSourceGain_nonneg p v hp B j
  change max 0 (t/g*(x-1)-t) ≤ _
  by_cases hUj : j+1 ≤ U.card
  · have ht : t = 0 := by
      change ((j+1-U.card : ℕ) : ℝ)/density R = 0
      rw [Nat.sub_eq_zero_of_le hUj,Nat.cast_zero,zero_div]
    simp only [ht,zero_div,zero_mul,sub_zero,max_self]
    exact linearEnvelope_lower_nonneg _ _ _
  · have hUj' : U.card ≤ j := by omega
    have hnj : n ≤ j := hnU.trans hUj'
    have hq : ∀ i, 0 ≤ firstPrimeMarginal i ∧ firstPrimeMarginal i ≤ 1 :=
      fun i => ⟨(firstPrimeMarginal_valid i).1,(firstPrimeMarginal_valid i).2.le⟩
    have hgap := linearEnvelope_positive_prefix_gap firstPrimeMarginal n j hnj
      (fun i _ => hq i) g hg.le hpos
    have hnpos : 0 < (linearEnvelope firstPrimeMarginal n g).1 := by
      have hnonneg : (0 : ℝ) ≤ (j-n : ℕ) := Nat.cast_nonneg _
      linarith
    have hdU := firstPrimeDensity_le U hU j hUj'
    have hden : density U = prefixDensity firstPrimeMarginal n*density R := by
      have hd : Disjoint Q R := by
        apply disjoint_left.mpr
        intro r hr hrR
        exact (mem_sdiff.mp hrR).2 hr
      have he : Q ∪ R = U := by dsimp only [U,R]; rw [union_sdiff_self_eq_union,union_comm]
      calc
        density U = density (Q ∪ R) := congrArg density he.symm
        _ = density Q*density R := prod_union hd
        _ = _ := by rw [firstPrimeDensity_prefix_image K n hn]
    rw [hden] at hdU
    have hbound := positive_prefix_density_ratio firstPrimeMarginal hq n j hnj g hg.le hpos
    have htnum : ((j+1-U.card : ℕ) : ℝ) ≤ (j : ℝ)+1 := by exact_mod_cast Nat.sub_le (j+1) U.card
    have hdt : t*density R = ((j+1-U.card : ℕ) : ℝ) := by
      exact div_mul_cancel₀ _ (density_pos R hR).ne'
    have hm := mul_le_mul_of_nonneg_left hdU ht0
    have hm' := mul_le_mul_of_nonneg_right htnum (firstPrimeDensity_pos n).le
    have htcap : t ≤ (linearEnvelope firstPrimeMarginal n g).1+(n : ℝ)+1 := by
      apply (mul_le_mul_iff_right₀ (firstPrimeDensity_pos j)).mp
      have he : t*(prefixDensity firstPrimeMarginal n*density R) =
          (t*density R)*prefixDensity firstPrimeMarginal n := by ring
      rw [he,hdt] at hm
      nlinarith only [hm,hm',hbound]
    exact affineSource_le_of_local_positive firstPrimeMarginal n (fun i _ => hq i)
      g hg hnpos t ht0 htcap x

/-- Full recursive equality for overlap-aware sources whose lengths were
plain-certified. This is uniform in the actual prime list, with no extra
large-missing-prime premise and no restriction on the source budget choices. -/
theorem firstPrime_union_seeded_eq_plain_of_plain_certificates
    (K : ℕ) (p : Fin K → ℕ) (hp : ∀ i, (p i).Prime) (j g : ℕ → ℕ)
    (hg : ∀ n ≤ K, 0 < g n)
    (hpos : ∀ n ≤ K, 0 < (linearEnvelope firstPrimeMarginal (j n) (g n : ℝ)).1)
    (x : ℝ) (hx : 0 ≤ x) :
    seededLinearEnvelope firstPrimeMarginal
      (unionBlockSource p (fun i => Nat.nth Nat.Prime i.val) j g) K x =
        linearEnvelope firstPrimeMarginal K x := by
  apply seededLinearEnvelope_eq_plain firstPrimeMarginal _ K
    (fun i _ => ⟨(firstPrimeMarginal_valid i).1,(firstPrimeMarginal_valid i).2.le⟩) _ x hx
  intro n hn y hy
  exact firstPrime_unionSource_le_of_plain_certificate K n (j n) hn p hp
    (g n : ℝ) (by exact_mod_cast hg n hn) (hpos n hn) y

/-- The scalar arithmetic transfer criterion uses a finite marginal extension;
its root value is identical to the same plain reference value in this case. -/
theorem extended_firstPrime_union_seeded_eq_plain
    (K : ℕ) (p : Fin K → ℕ) (hp : ∀ i, (p i).Prime) (j g : ℕ → ℕ)
    (hg : ∀ n ≤ K, 0 < g n)
    (hpos : ∀ n ≤ K, 0 < (linearEnvelope firstPrimeMarginal (j n) (g n : ℝ)).1)
    (x : ℝ) (hx : 0 ≤ x) :
    seededLinearEnvelope (extendMarginal (fun i : Fin K => 1/(Nat.nth Nat.Prime i.val : ℝ)))
      (unionBlockSource p (fun i => Nat.nth Nat.Prime i.val) j g) K x =
        linearEnvelope firstPrimeMarginal K x := by
  rw [seededLinearEnvelope_congr _ firstPrimeMarginal _ K x
    (fun i hi => by simp only [extendMarginal,hi,dif_pos,firstPrimeMarginal])]
  exact firstPrime_union_seeded_eq_plain_of_plain_certificates K p hp j g hg hpos x hx

#print axioms firstPrimeDensity_le
#print axioms firstPrimeDensity_prefix_image
#print axioms firstPrime_unionSource_le_of_plain_certificate
#print axioms firstPrime_union_seeded_eq_plain_of_plain_certificates
#print axioms extended_firstPrime_union_seeded_eq_plain
end Erdos970.RecursiveSieve
