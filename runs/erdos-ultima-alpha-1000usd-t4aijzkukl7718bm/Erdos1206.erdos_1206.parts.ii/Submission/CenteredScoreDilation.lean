import Submission.CenteredScoreCriterion
import Submission.ScorePrimeCover

/-! Necessary uncentered separation for the uniform centered-score criterion.
No separating score is constructed here. -/
namespace Erdos1206.CenteredScoreDilation
open QuadraticPrimeMoments FullPrimeScoreVariance PowerWindowMeanOscillation
open scoped Classical

noncomputable def rawSpread (w : ℕ → ℝ) (a b c d : ℕ) : ℝ :=
  max (max |primeScore w a-primeScore w b| |primeScore w a-primeScore w c|)
    (max (max |primeScore w a-primeScore w d| |primeScore w b-primeScore w c|)
      (max |primeScore w b-primeScore w d| |primeScore w c-primeScore w d|))

lemma score_fresh_prime (w : ℕ → ℝ) {p n : ℕ} (hp : p.Prime)
    (hn : 0 < n) (hbig : n < p) :
    primeScore w (p*n) = w p+primeScore w n := by
  have hnot : p ∉ n.primeFactors := by
    intro h
    exact (not_le_of_gt hbig) (Nat.le_of_mem_primeFactors h)
  rw [primeScore,Nat.primeFactors_mul hp.ne_zero hn.ne',hp.primeFactors,
    Finset.singleton_union,Finset.sum_insert hnot]
  rfl

lemma dilated_power_comparable {p d m n : ℕ} (hpd : d^2 ≤ p)
    (hm : m ≤ d) (hn : 0 < n) : (p*m)^2 ≤ (p*n)^3 := by
  calc
    _ = p^2*m^2 := mul_pow _ _ _
    _ ≤ p^2*d^2 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hm 2)
    _ ≤ p^2*p := Nat.mul_le_mul_left _ hpd
    _ = p^3*1 := by ring
    _ ≤ p^3*n^3 := Nat.mul_le_mul_left _ (Nat.one_le_pow _ _ hn)
    _ = _ := (mul_pow _ _ _).symm

/-- If one fixed positive quadruple has a uniform centered margin under all
sufficiently large fresh-prime dilations, it already has that raw margin. -/
theorem raw_margin_of_prime_dilations (w : ℕ → ℝ)
    (hs : Summable (fun p : ℕ => if p.Prime then w p^2/p else 0))
    {a b c d : ℕ} (ha : 0 < a) (hab : a ≤ b) (hbc : b ≤ c) (hcd : c ≤ d)
    {ε : ℝ} (K : ℕ)
    (hgap : ∀ p : ℕ, p.Prime → K ≤ p → d < p →
      ε ≤ CenteredScoreCriterion.spread w (p*a) (p*b) (p*c) (p*d)) :
    ε ≤ rawSpread w a b c d := by
  by_contra hle
  have hR : rawSpread w a b c d < ε := lt_of_not_ge hle
  let η := (ε-rawSpread w a b c d)/2
  have hη : 0 < η := by dsimp [η]; linarith
  obtain ⟨H,hH⟩ := center_power_oscillation w hs hη
  obtain ⟨p,hpbound,hp⟩ := Nat.exists_infinite_primes (H+K+d^2+d+1)
  have hpH : H ≤ p := by omega
  have hpK : K ≤ p := by omega
  have hpd : d^2 ≤ p := by omega
  have hdp : d < p := by omega
  have hpos (n : ℕ) (hn : a ≤ n) : 0 < n := ha.trans_le hn
  have hlarge (n : ℕ) (hn : a ≤ n) : H ≤ p*n := by
    exact hpH.trans (Nat.le_mul_of_pos_right p (hpos n hn))
  have hpair (m n : ℕ) (hm : a ≤ m) (hmd : m ≤ d)
      (hn : a ≤ n) (hnd : n ≤ d)
      (hr : |primeScore w m-primeScore w n| ≤ rawSpread w a b c d) :
      |deviation w (p*m)-deviation w (p*n)| < ε := by
    have hosc := hH (p*m) (p*n) (hlarge m hm) (hlarge n hn)
      (dilated_power_comparable hpd hmd (hpos n hn))
      (dilated_power_comparable hpd hnd (hpos m hm))
    have hid : deviation w (p*m)-deviation w (p*n) =
        (primeScore w m-primeScore w n)-(center w (p*m)-center w (p*n)) := by
      rw [deviation,deviation,score_fresh_prime w hp (hpos m hm) (hmd.trans_lt hdp),
        score_fresh_prime w hp (hpos n hn) (hnd.trans_lt hdp)]
      ring
    rw [hid]
    have ht := abs_sub (primeScore w m-primeScore w n) (center w (p*m)-center w (p*n))
    dsimp [η] at hosc
    linarith
  have hle₁ : max |primeScore w a-primeScore w b| |primeScore w a-primeScore w c|
      ≤ rawSpread w a b c d := le_max_left _ _
  have hle₂ : max (max |primeScore w a-primeScore w d| |primeScore w b-primeScore w c|)
      (max |primeScore w b-primeScore w d| |primeScore w c-primeScore w d|)
      ≤ rawSpread w a b c d := le_max_right _ _
  have hac := hab.trans hbc
  have had := hac.trans hcd
  have hbd := hbc.trans hcd
  have hsmall : CenteredScoreCriterion.spread w (p*a) (p*b) (p*c) (p*d) < ε := by
    exact max_lt
      (max_lt
        (hpair a b le_rfl had hab hbd ((le_max_left _ _).trans hle₁))
        (hpair a c le_rfl had hac hcd ((le_max_right _ _).trans hle₁)))
      (max_lt
        (max_lt
          (hpair a d le_rfl had had le_rfl ((le_max_left _ _).trans ((le_max_left _ _).trans hle₂)))
          (hpair b c hab hbd hac hcd ((le_max_right _ _).trans ((le_max_left _ _).trans hle₂))))
        (max_lt
          (hpair b d hab hbd had le_rfl ((le_max_left _ _).trans ((le_max_right _ _).trans hle₂)))
          (hpair c d hac hcd had le_rfl ((le_max_right _ _).trans ((le_max_right _ _).trans hle₂)))))
  exact (not_lt_of_ge (hgap p hp hpK hdp)) hsmall

/-- The centered criterion's threshold on the smallest root disappears from
this necessary raw-score condition, by taking fresh-prime dilations. -/
theorem raw_margin_of_centered_margin (w : ℕ → ℝ)
    (hs : Summable (fun p : ℕ => if p.Prime then w p^2/p else 0))
    {ε : ℝ} (H₀ : ℕ)
    (hgap : ∀ a b c d : ℕ,
      Squarefree a → Squarefree b → Squarefree c → Squarefree d →
      H₀ ≤ a → 0 < a → a < b → b < c → c < d → a^3+d^3=b^3+c^3 →
        ε ≤ CenteredScoreCriterion.spread w a b c d)
    {a b c d : ℕ} (has : Squarefree a) (hbs : Squarefree b)
    (hcs : Squarefree c) (hds : Squarefree d)
    (ha : 0 < a) (hab : a < b) (hbc : b < c) (hcd : c < d)
    (he : a^3+d^3=b^3+c^3) : ε ≤ rawSpread w a b c d := by
  apply raw_margin_of_prime_dilations w hs ha hab.le hbc.le hcd.le H₀
  intro p hp hpH hdp
  have hsf (n : ℕ) (hn : Squarefree n) (hn0 : 0 < n) (hnd : n ≤ d) :
      Squarefree (p*n) := by
    apply (Nat.squarefree_mul (hp.coprime_iff_not_dvd.mpr ?_)).mpr ⟨hp.squarefree,hn⟩
    intro hd
    exact (not_le_of_gt (hnd.trans_lt hdp)) (Nat.le_of_dvd hn0 hd)
  have had : a ≤ d := (hab.trans (hbc.trans hcd)).le
  have hbd : b ≤ d := (hbc.trans hcd).le
  apply hgap (p*a) (p*b) (p*c) (p*d)
    (hsf a has ha had) (hsf b hbs (ha.trans hab) hbd)
    (hsf c hcs (ha.trans (hab.trans hbc)) hcd.le)
    (hsf d hds (ha.trans (hab.trans (hbc.trans hcd))) le_rfl)
    (hpH.trans (Nat.le_mul_of_pos_right p ha)) (Nat.mul_pos hp.pos ha)
    (Nat.mul_lt_mul_of_pos_left hab hp.pos)
    (Nat.mul_lt_mul_of_pos_left hbc hp.pos)
    (Nat.mul_lt_mul_of_pos_left hcd hp.pos)
  simpa only [mul_pow,←mul_add] using congrArg (fun n : ℕ => p^3*n) he

/-- Uniform centered separation entails a reciprocally summable prime cover
of all prime-root cube collisions. This concerns the uniform margin criterion,
not an arbitrary Sidon moving band. -/
theorem prime_cover_of_centered_margin (w : ℕ → ℝ)
    (hs : Summable (fun p : ℕ => if p.Prime then w p^2/p else 0))
    {ε : ℝ} (hε : 0 < ε) (H₀ : ℕ)
    (hgap : ∀ a b c d : ℕ,
      Squarefree a → Squarefree b → Squarefree c → Squarefree d →
      H₀ ≤ a → 0 < a → a < b → b < c → c < d → a^3+d^3=b^3+c^3 →
        ε ≤ CenteredScoreCriterion.spread w a b c d) :
    ∃ P : Set ℕ, (∀ p ∈ P, p.Prime) ∧ IsPrimeCubeCover P ∧
      Summable (fun p : ℕ => if p ∈ P then (1:ℝ)/p else 0) := by
  let B : Set ℕ := {p | p.Prime ∧ |w p| < ε/2}
  have hsidon : IsSidon ((fun n : ℕ => n^3) '' B) := by
    apply (cubeSidon_iff_no_strict_positive B).mpr
    intro a ha b hb c hc d hd ha0 hab hbc hcd he
    have hraw := raw_margin_of_centered_margin w hs H₀ hgap
      ha.1.squarefree hb.1.squarefree hc.1.squarefree hd.1.squarefree ha0 hab hbc hcd he
    have hpair (m n : ℕ) (hm : m ∈ B) (hn : n ∈ B) :
        |primeScore w m-primeScore w n| < ε := by
      have hm' : primeScore w m = w m := by simp [primeScore,hm.1.primeFactors]
      have hn' : primeScore w n = w n := by simp [primeScore,hn.1.primeFactors]
      rw [hm',hn']
      have hh := abs_sub (w m) (w n)
      have hm'' := hm.2
      have hn'' := hn.2
      linarith
    have hsmall : rawSpread w a b c d < ε :=
      max_lt (max_lt (hpair a b ha hb) (hpair a c ha hc))
        (max_lt (max_lt (hpair a d ha hd) (hpair b c hb hc))
          (max_lt (hpair b d hb hd) (hpair c d hc hd)))
    exact (not_lt_of_ge hraw) hsmall
  exact ScorePrimeCover.summable_prime_cover_of_score_band w
    (div_pos hε (by norm_num)) hs (fun p hp hw => show p ∈ B from ⟨hp,hw⟩) hsidon

#print axioms raw_margin_of_prime_dilations
#print axioms raw_margin_of_centered_margin
#print axioms prime_cover_of_centered_margin
end Erdos1206.CenteredScoreDilation
