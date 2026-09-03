import FormalConjecturesUtil

/-!
Two-row residue restrictions for primitive rational rotations.
This auxiliary result is not a proof of the asymptotic Sidon conjecture.
-/
namespace Erdos773.CompositeResidueRotation
set_option maxHeartbeats 1000000

/-- Both rotation rows, unlike either row alone, specify which leg is
zero modulo an arbitrary odd modulus. -/
theorem rows_divisibility {l a b c d p r q : ℤ}
    (hodd : IsCoprime l 2)
    (ha : a ≡ 1 [ZMOD l]) (hb : b ≡ 1 [ZMOD l])
    (hc : c ≡ 1 [ZMOD l]) (hd : d ≡ 1 [ZMOD l])
    (hrow₁ : p*a+r*b=q*c) (hrow₂ : -r*a+p*b=q*d) :
    l ∣ r ∧ l ∣ q-p := by
  have hm₁ : p+r ≡ q [ZMOD l] := by
    have h₁ := ((Int.ModEq.refl p).mul ha).add ((Int.ModEq.refl r).mul hb)
    have h₂ := (Int.ModEq.refl q).mul hc
    simp only [mul_one] at h₁ h₂
    exact h₁.symm.trans (hrow₁ ▸ h₂)
  have hm₂ : -r+p ≡ q [ZMOD l] := by
    have h₁ := ((Int.ModEq.refl (-r)).mul ha).add ((Int.ModEq.refl p).mul hb)
    have h₂ := (Int.ModEq.refl q).mul hd
    simp only [mul_one] at h₁ h₂
    exact h₁.symm.trans (hrow₂ ▸ h₂)
  have hdiff : l ∣ 2*r := by
    have h := (hm₂.trans hm₁.symm).dvd
    convert h using 1; ring
  have hr : l ∣ r := hodd.dvd_of_dvd_mul_left hdiff
  have hp : l ∣ q-p := by
    convert dvd_add hm₁.dvd hr using 1; ring
  exact ⟨hr,hp⟩

/-- A primitive Pythagorean triple lifts the diagonal residue to the
square of the modulus. No primality or squarefreeness is assumed. -/
theorem square_divides_gap {l p r q : ℤ}
    (hl : l ≠ 0) (hodd : IsCoprime l 2) (hprimitive : IsCoprime p r)
    (hpyth : q^2=p^2+r^2) (hr : l ∣ r) (hgap : l ∣ q-p) :
    l^2 ∣ q-p := by
  have hlp : IsCoprime l p :=
    hprimitive.symm.of_isCoprime_of_dvd_left hr
  obtain ⟨k,hk⟩ := hgap
  have hq : q=p+l*k := by linarith only [hk]
  have hlq : IsCoprime l q := by
    rw [hq]
    exact hlp.add_mul_left_right k
  obtain ⟨t,ht⟩ := hr
  have he : l*(2*q*k-l*(k^2+t^2))=0 := by
    rw [hq,ht] at hpyth
    rw [hq]
    nlinarith only [hpyth]
  have he' : 2*q*k=l*(k^2+t^2) := by
    have := (mul_eq_zero.mp he).resolve_left hl
    linarith only [this]
  have hkdiv : l ∣ k := (hodd.mul_right hlq).dvd_of_dvd_mul_left
    ⟨k^2+t^2,he'⟩
  obtain ⟨s,hs⟩ := hkdiv
  refine ⟨s,?_⟩
  rw [hk,hs]
  ring

/-- Every nontrivial primitive rotation between four roots equal to one
modulo an odd modulus has denominator strictly larger than half its square.
This is a denominator cutoff, not a claim that the whole carrier is Sidon. -/
theorem denominator_lower {l a b c d p r q : ℤ}
    (hl : l ≠ 0) (hodd : IsCoprime l 2) (hprimitive : IsCoprime p r)
    (ha : a ≡ 1 [ZMOD l]) (hb : b ≡ 1 [ZMOD l])
    (hc : c ≡ 1 [ZMOD l]) (hd : d ≡ 1 [ZMOD l])
    (hrow₁ : p*a+r*b=q*c) (hrow₂ : -r*a+p*b=q*d)
    (hpyth : q^2=p^2+r^2) (hq : 0 < q) (hr : r ≠ 0) :
    l^2 < 2*q := by
  obtain ⟨hleg,hgap⟩ := rows_divisibility hodd ha hb hc hd hrow₁ hrow₂
  have hdiv := square_divides_gap hl hodd hprimitive hpyth hleg hgap
  have hrsq : 0 < r^2 := sq_pos_of_ne_zero hr
  have hpq : p < q := by nlinarith only [hpyth,hrsq,hq]
  have hneg : -q < p := by nlinarith only [hpyth,hrsq,hq]
  have hle : l^2 ≤ q-p := Int.le_of_dvd (by omega) hdiv
  linarith only [hle,hneg]

/-- Positivity rules out the half-plane rotations and improves the cutoff
from m²/2 to m². The primitive denominator is still not bounded above here. -/
theorem positive_denominator_lower {l a b c d p r q : ℤ}
    (hl : l ≠ 0) (hodd : IsCoprime l 2) (hprimitive : IsCoprime p r)
    (ha : a ≡ 1 [ZMOD l]) (hb : b ≡ 1 [ZMOD l])
    (hc : c ≡ 1 [ZMOD l]) (hd : d ≡ 1 [ZMOD l])
    (hrow₁ : p*a+r*b=q*c) (hrow₂ : -r*a+p*b=q*d)
    (hpyth : q^2=p^2+r^2) (hq : 0 < q) (hr : r ≠ 0)
    (ha₀ : 0 < a) (hb₀ : 0 < b) (hc₀ : 0 < c) (hd₀ : 0 < d) :
    l^2 < q := by
  obtain ⟨hleg,hgap⟩ := rows_divisibility hodd ha hb hc hd hrow₁ hrow₂
  have hdiv := square_divides_gap hl hodd hprimitive hpyth hleg hgap
  have hdot : p*(a^2+b^2)=q*(a*c+b*d) := by
    linear_combination a*hrow₁+b*hrow₂
  have hprod : 0 < p*(a^2+b^2) := by rw [hdot]; positivity
  have hnorm : 0 < a^2+b^2 := by positivity
  have hp : 0 < p := (mul_pos_iff_of_pos_right hnorm).mp hprod
  have hrsq : 0 < r^2 := sq_pos_of_ne_zero hr
  have hpq : p < q := by nlinarith only [hpyth,hrsq,hq]
  have hle : l^2 ≤ q-p := Int.le_of_dvd (by omega) hdiv
  linarith only [hle,hp]

/-- A nontrivial modulus cannot divide its own square to the third power. -/
lemma cube_not_dvd_square {m : ℤ} (hm : 1 < m) : ¬ m^3 ∣ m^2 := by
  intro hd
  have hm₀ : 0 < m := by omega
  have hs : 0 < m^2 := sq_pos_of_pos hm₀
  have hle := Int.le_of_dvd hs hd
  have hmul := mul_pos hs (show 0 < m-1 by omega)
  nlinarith only [hle,hmul]

/-- At every odd modulus m=2t+1>1 there is a primitive positive rotation
with four distinct roots equal to one modulo m and q-p exactly m².
Thus the preceding square-divisibility statement cannot be iterated to m³
without an additional selection hypothesis. The roots have quadratic height.
This is not a counterexample to the asymptotic Sidon-subset conjecture. -/
theorem positive_primitive_square_gap (t : ℕ) (ht : 0 < t) :
    let m : ℤ := 2*t+1
    ∃ a b c d p r q : ℤ,
      0 < a ∧ a < d ∧ d < c ∧ c < b ∧ b = 5*m^2+5*m+1 ∧
      a ≡ 1 [ZMOD m] ∧ b ≡ 1 [ZMOD m] ∧
      c ≡ 1 [ZMOD m] ∧ d ≡ 1 [ZMOD m] ∧
      IsCoprime m 2 ∧ IsCoprime p r ∧ 0 < q ∧ r ≠ 0 ∧
      q^2=p^2+r^2 ∧ p*a+r*b=q*c ∧ -r*a+p*b=q*d ∧
      a^2+b^2=c^2+d^2 ∧ q-p=m^2 ∧ ¬ m^3 ∣ q-p := by
  dsimp only
  let x : ℤ := t
  let m : ℤ := 2*x+1
  have hx : 0 < x := by dsimp [x]; exact_mod_cast ht
  have hm : 1 < m := by dsimp [m]; omega
  let a := 2*m+1
  let b := 5*m^2+5*m+1
  let c := 4*m^2+4*m+1
  let d := 3*m^2+3*m+1
  let p := 6*x^2+10*x+4
  let r := 8*x^2+10*x+3
  let q := 10*x^2+14*x+5
  have hmod (k : ℤ) : m*k+1 ≡ 1 [ZMOD m] := by
    apply Int.modEq_iff_dvd.mpr
    exact ⟨-k,by ring⟩
  have ha : a ≡ 1 [ZMOD m] := by
    convert hmod 2 using 1; dsimp [a]; ring
  have hb : b ≡ 1 [ZMOD m] := by
    convert hmod (5*m+5) using 1; dsimp [b]; ring
  have hc : c ≡ 1 [ZMOD m] := by
    convert hmod (4*m+4) using 1; dsimp [c]; ring
  have hd : d ≡ 1 [ZMOD m] := by
    convert hmod (3*m+3) using 1; dsimp [d]; ring
  have hodd : IsCoprime m 2 := ⟨1,-x,by dsimp [m]; ring⟩
  have hprimitive : IsCoprime p r :=
    ⟨40*x+22,-30*x-29,by dsimp [p,r]; ring⟩
  have hgap : q-p=m^2 := by dsimp [q,p,m]; ring
  refine ⟨a,b,c,d,p,r,q,?_,?_,?_,?_,rfl,ha,hb,hc,hd,hodd,hprimitive,
    ?_,?_,?_,?_,?_,?_,hgap,?_⟩
  · dsimp [a]; omega
  · dsimp [a,d]; nlinarith
  · dsimp [d,c]; nlinarith
  · dsimp [c,b]; nlinarith
  · dsimp [q]; positivity
  · dsimp [r]; positivity
  · dsimp [q,p,r]; ring
  · dsimp [p,r,q,a,b,c,m]; ring
  · dsimp [p,r,q,a,b,d,m]; ring
  · dsimp [a,b,c,d]; ring
  · rw [hgap]
    exact cube_not_dvd_square hm

#print axioms positive_primitive_square_gap

#print axioms positive_denominator_lower
#print axioms rows_divisibility
#print axioms square_divides_gap
#print axioms denominator_lower
end Erdos773.CompositeResidueRotation
