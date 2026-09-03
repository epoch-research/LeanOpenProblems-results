import FormalConjecturesUtil

/-! Rational-approximation resonances for quadratic shrinking-window sets.
These results concern a particular candidate class, not arbitrary subsets
of the naturals and not a disproof of Erdős 66. -/
namespace Erdos66QuadraticPhaseResonance
open AdditiveCombinatorics Filter
open scoped Classical Topology
set_option maxHeartbeats 1500000

noncomputable def phaseSet (α : ℝ) (w : ℕ → ℝ) : Set ℕ :=
  {n | ∃ z : ℤ, |α*(n:ℝ)^2-(z:ℝ)| ≤ w n}

lemma phase_mem_of_small_remainder (α : ℝ) (w : ℕ → ℝ)
    (a p n : ℕ) (hp : 0 < p) (hn : n ≤ p) (δ B : ℝ) (hδ : 0 ≤ δ)
    (happrox : |α-(a:ℝ)/p| ≤ δ)
    (hrem : ((a*n^2 % p : ℕ):ℝ) ≤ B)
    (hw : δ*(p:ℝ)^2+B/(p:ℝ) ≤ w n) : n ∈ phaseSet α w := by
  have hpR : (0:ℝ) < p := by exact_mod_cast hp
  have hnR : (n:ℝ) ≤ p := by exact_mod_cast hn
  have he := Nat.mod_add_div (a*n^2) p
  have heR : ((a*n^2 % p : ℕ):ℝ)+(p:ℝ)*((a*n^2 / p : ℕ):ℝ) = (a:ℝ)*(n:ℝ)^2 := by
    exact_mod_cast he
  have hdecomp : α*(n:ℝ)^2-((a*n^2 / p : ℕ):ℝ) =
      (α-(a:ℝ)/p)*(n:ℝ)^2+((a*n^2 % p : ℕ):ℝ)/(p:ℝ) := by
    field_simp
    nlinarith
  refine ⟨(a*n^2 / p : ℕ), ?_⟩
  simp only [Int.cast_natCast]
  rw [hdecomp]
  calc
    _ ≤ |(α-(a:ℝ)/p)*(n:ℝ)^2| + |((a*n^2 % p : ℕ):ℝ)/(p:ℝ)| := abs_add_le _ _
    _ = |α-(a:ℝ)/p| * (n:ℝ)^2+((a*n^2 % p : ℕ):ℝ)/(p:ℝ) := by
      rw [abs_mul,abs_of_nonneg (sq_nonneg (n:ℝ)),
        abs_of_nonneg (show 0 ≤ ((a*n^2 % p : ℕ):ℝ)/(p:ℝ) by positivity)]
    _ ≤ δ*(p:ℝ)^2+B/(p:ℝ) := by
      apply add_le_add
      · exact (mul_le_mul_of_nonneg_right happrox (sq_nonneg _)).trans
          (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (Nat.cast_nonneg _) hnR 2) hδ)
      · exact div_le_div_of_nonneg_right hrem hpR.le
    _ ≤ w n := hw

lemma square_remainder (p a k : ℕ) (u : ZMod p)
    (hu : (a : ZMod p)*u^2=1) (hk : k^2 < p) :
    a*((u*(k:ZMod p)).val)^2 % p = k^2 := by
  letI : NeZero p := ⟨by omega⟩
  have he : ((a*((u*(k:ZMod p)).val)^2 : ℕ):ZMod p) = (k^2:ℕ) := by
    push_cast
    rw [ZMod.natCast_zmod_val, mul_pow, ← mul_assoc, hu, one_mul]
  have hh := (ZMod.natCast_eq_natCast_iff' _ _ p).mp he
  rwa [Nat.mod_eq_of_lt hk] at hh

lemma reflected_remainder (p a x : ℕ) (hx : x ≤ p) :
    a*(p-x)^2 % p = a*x^2 % p := by
  apply (ZMod.natCast_eq_natCast_iff' _ _ p).mp
  push_cast [Nat.cast_sub hx]
  simp only [ZMod.natCast_self,zero_sub,neg_sq]

/-- A square-unit numerator supplies m distinct endpoints whose reflections
have the same small rational quadratic phase. -/
theorem finite_resonance (α : ℝ) (w : ℕ → ℝ) (p a m : ℕ)
    (hp : 0 < p) (hm : m^2 < p) (u : (ZMod p)ˣ)
    (hu : (a : ZMod p)*(u:ZMod p)^2=1) (δ : ℝ) (hδ : 0 ≤ δ)
    (happrox : |α-(a:ℝ)/p| ≤ δ)
    (hw : ∀ n ≤ p, δ*(p:ℝ)^2+(m:ℝ)^2/(p:ℝ) ≤ w n) :
    m ≤ sumRep (phaseSet α w) p := by
  letI : NeZero p := ⟨Nat.ne_of_gt hp⟩
  let x : ℕ → ℕ := fun k ↦ ((u:ZMod p)*(k:ZMod p)).val
  have hx (k : ℕ) : x k ≤ p := (ZMod.val_lt _).le
  have hkm (k : ℕ) (hk : k < m) : k^2 < p := by
    have := Nat.pow_le_pow_left (Nat.le_of_lt hk) 2
    omega
  have hmem (k : ℕ) (hk : k < m) :
      x k ∈ phaseSet α w ∧ p-x k ∈ phaseSet α w := by
    have hsmall : ((a*(x k)^2 % p : ℕ):ℝ) ≤ (m:ℝ)^2 := by
      rw [square_remainder p a k (u:ZMod p) hu (hkm k hk)]
      exact_mod_cast Nat.pow_le_pow_left (Nat.le_of_lt hk) 2
    constructor
    · exact phase_mem_of_small_remainder α w a p (x k) hp (hx k) δ ((m:ℝ)^2)
        hδ happrox hsmall (hw _ (hx k))
    · apply phase_mem_of_small_remainder α w a p (p-x k) hp (Nat.sub_le _ _) δ ((m:ℝ)^2)
        hδ happrox _ (hw _ (Nat.sub_le _ _))
      rwa [reflected_remainder p a (x k) (hx k)]
  have hmp : m ≤ p := by nlinarith
  have hinj : Set.InjOn x (↑(Finset.range m) : Set ℕ) := by
    intro k hk l hl he
    have hkl : (k:ZMod p)=(l:ZMod p) := by
      have hh : (u:ZMod p)*(k:ZMod p)=(u:ZMod p)*(l:ZMod p) :=
        ZMod.val_injective p he
      have hh' := congrArg (fun z : ZMod p ↦ (↑(u⁻¹):ZMod p)*z) hh
      simpa only [← mul_assoc,Units.inv_mul,one_mul] using hh'
    have heq := (ZMod.natCast_eq_natCast_iff' k l p).mp hkl
    rw [Nat.mod_eq_of_lt (by have := Finset.mem_range.mp hk; omega),
      Nat.mod_eq_of_lt (by have := Finset.mem_range.mp hl; omega)] at heq
    exact heq
  rw [sumRep_def]
  calc
    m = (Finset.range m).card := (Finset.card_range m).symm
    _ ≤ _ := Finset.card_le_card_of_injOn (fun k ↦ (x k,p-x k)) (by
      intro k hk
      simpa only [Finset.mem_coe,Finset.mem_filter,Finset.mem_antidiagonal] using
        And.intro (Nat.add_sub_of_le (hx k)) (hmem k (Finset.mem_range.mp hk))) (by
      intro k hk l hl he
      exact hinj hk hl (congrArg Prod.fst he))

end Erdos66QuadraticPhaseResonance
