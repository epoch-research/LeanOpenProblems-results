import Submission.RelativeGeometricBands
import Submission.CompactGapRatioColoring
import Submission.RelativePrimitiveMaxima

/-! A global sufficient criterion involving only the two endpoint regimes
of the adjacent-gap ratio. No summable endpoint cover is constructed here. -/
namespace Erdos1206.RelativeEndpointReduction
open RelativePrimitiveMaxima
open scoped Classical

def Endpoint (H a b c d : ℕ) : Prop :=
  H*(b-a) < (H+1)*(d-c) ∨ H*(d-c) < b-a

/-- Every positive-density source of positive integers has a positive-density
subset whose surviving cubic collisions lie in the two endpoint regimes. -/
theorem exists_positive_endpoint_source (H : ℕ) (hH : 1 ≤ H) {S : Set ℕ}
    (hS : 0<S.lowerDensity) (hpos : ∀ n∈S, 0<n) :
    ∃ T : Set ℕ, T ⊆ S ∧ 0<T.lowerDensity ∧
      ∀ a b c d : ℕ, b∈T → d∈T → a<b → b≤c → c<d →
        a^3+d^3=b^3+c^3 → Endpoint H a b c d := by
  have hHR : (1:ℝ) ≤ H := by exact_mod_cast hH
  have hs : (0:ℝ) < 100*H := by positivity
  let q : ℝ := (100*H+1)/(100*H)
  have hq : 1<q := by
    apply (lt_div_iff₀ hs).mpr
    linarith
  obtain ⟨T,hTS,hTd,hsep⟩ := RelativeGeometricBands.exists_ratio_separated_subset
    hq (show (1:ℝ) ≤ 2*H by linarith) hS hpos
  refine ⟨T,hTS,hTd,?_⟩
  intro a b c d hb hd hab hbc hcd he
  by_contra hn
  have hlo : (H+1)*(d-c) ≤ H*(b-a) := by
    have : ¬ H*(b-a) < (H+1)*(d-c) := fun h => hn (Or.inl h)
    omega
  have hup : b-a ≤ H*(d-c) := by
    have : ¬ H*(d-c) < b-a := fun h => hn (Or.inr h)
    omega
  have hloR : ((H:ℝ)+1)*((d:ℝ)-c) ≤ H*((b:ℝ)-a) := by
    have hh := (show (((H+1)*(d-c):ℕ):ℝ) ≤ ((H*(b-a):ℕ):ℝ) by exact_mod_cast hlo)
    simpa only [Nat.cast_mul,Nat.cast_add,Nat.cast_one,Nat.cast_sub hcd.le,
      Nat.cast_sub hab.le] using hh
  have hupR : (b:ℝ)-a ≤ H*((d:ℝ)-c) := by
    have hh := (show ((b-a:ℕ):ℝ) ≤ ((H*(d-c):ℕ):ℝ) by exact_mod_cast hup)
    simpa only [Nat.cast_mul,Nat.cast_sub hcd.le,Nat.cast_sub hab.le] using hh
  have heR : (a:ℝ)^3+d^3=(b:ℝ)^3+c^3 := by exact_mod_cast he
  obtain ⟨hlo',hup'⟩ := CompactGapRatioColoring.compact_gap_root_ratio hHR
    (Nat.cast_nonneg a) (by exact_mod_cast hab) (by exact_mod_cast hbc)
    (by exact_mod_cast hcd) heR hloR hupR
  have hnear := hsep b hb d hd (by omega) hup'
  exact (not_lt_of_ge hlo') hnear

def endpointMaxima (H : ℕ) (S : Set ℕ) : Set ℕ :=
  {q | ∃ a∈S, ∃ b∈S, ∃ c∈S, ∃ d∈S,
    0<a ∧ a<b ∧ b<c ∧ c<d ∧ a^3+d^3=b^3+c^3 ∧
      Endpoint H a b c d ∧ q=primitiveMax a b c d}

/-- A summable primitive-maximum cover is needed only for ratios close to one
or larger than H. The entire intervening compact range can be removed inside
the same source while retaining positive lower density. -/
theorem summable_endpoint_maxima_suffice (H : ℕ) (hH : 1 ≤ H) {S : Set ℕ}
    (hS : 0<S.lowerDensity) (hpos : ∀ n∈S, 0<n)
    (hs : Summable (fun d : ℕ => if d∈endpointMaxima H S then (1:ℝ)/d else 0)) :
    ∃ A : Set ℕ, A.Infinite ∧ 0<A.lowerDensity ∧ IsSidon ((fun n : ℕ => n^3) '' A) := by
  obtain ⟨T,hTS,hTd,hend⟩ := exists_positive_endpoint_source H hH hS hpos
  have hsub : maxima T ⊆ endpointMaxima H S := by
    rintro q ⟨a,ha,b,hb,c,hc,d,hd,ha0,hab,hbc,hcd,he,hq⟩
    exact ⟨a,hTS ha,b,hTS hb,c,hTS hc,d,hTS hd,ha0,hab,hbc,hcd,he,
      hend a b c d hb hd hab hbc.le hcd he,hq⟩
  apply summable_maxima_suffice hTd (fun n hn => hpos n (hTS hn))
  apply hs.of_nonneg_of_le
  · intro n
    split_ifs <;> positivity
  · intro n
    by_cases hn : n∈maxima T
    · simp only [hn,hsub hn,if_true,le_refl]
    · simp only [hn,if_false]
      split_ifs <;> positivity

#print axioms exists_positive_endpoint_source
#print axioms summable_endpoint_maxima_suffice
end Erdos1206.RelativeEndpointReduction
