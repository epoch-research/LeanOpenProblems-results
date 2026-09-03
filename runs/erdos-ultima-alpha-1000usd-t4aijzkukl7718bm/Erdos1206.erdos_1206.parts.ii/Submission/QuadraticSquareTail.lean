import Submission.AffineQuadraticSquarefreeSieve

/-! Eventual uniform tails for square divisibility of fixed positive quadratics. -/
namespace Erdos1206.QuadraticSquareTail
open Finset Filter QuadraticSquarefreeSieve AffineQuadraticSquarefreeSieve
open scoped Classical
set_option maxHeartbeats 1000000

lemma square_tail_count (a b c M v w N K L : ℕ) (hK : 0<K)
    (hlarge : ∀ p : ℕ, p.Prime → K<p →
      M.Coprime p ∧ (a : ZMod p) ≠ 0 ∧ (b : ZMod p)^2-4*a*c ≠ 0)
    (hbound : ∀ x ∈ (range N) ×ˢ (range N), 0 < x.1 →
      0 < quad a b c (M*x.1+v) (M*x.2+w) ∧
      quad a b c (M*x.1+v) (M*x.2+w) ≤ (L*N)^2) :
    ((((range N) ×ˢ (range N)).filter (fun x =>
      0 < x.1 ∧ ∃ p, p.Prime ∧ K < p ∧ p^2 ∣ quad a b c (M*x.1+v) (M*x.2+w))).card : ℝ) ≤
      3*(N:ℝ)^2/K+(4*N+1)*Nat.primeCounting (L*N) := by
  let P := (range (L*N+1)).filter (fun p => p.Prime ∧ K<p)
  let B := fun p => ((range N) ×ˢ (range N)).filter (fun x =>
    p^2 ∣ quad a b c (M*x.1+v) (M*x.2+w))
  let S := ((range N) ×ˢ (range N)).filter (fun x =>
    0 < x.1 ∧ ∃ p, p.Prime ∧ K < p ∧ p^2 ∣ quad a b c (M*x.1+v) (M*x.2+w))
  have hsub : S ⊆ P.biUnion B := by
    intro x hx
    obtain ⟨hxN,hxpos,p,hp,hKp,hpd'⟩ := mem_filter.mp hx
    have hpN : p≤L*N := by
      have hh := (Nat.le_of_dvd (hbound x hxN hxpos).1 hpd').trans (hbound x hxN hxpos).2
      exact (Nat.pow_le_pow_iff_left (by decide : 2 ≠ 0)).mp hh
    exact mem_biUnion.mpr ⟨p,mem_filter.mpr ⟨mem_range.mpr (by omega),hp,hKp⟩,
      mem_filter.mpr ⟨hxN,hpd'⟩⟩
  have hnat : S.card ≤ ∑ p ∈ P, (B p).card :=
    (card_le_card hsub).trans card_biUnion_le
  have hc : (S.card : ℝ) ≤ ∑ p ∈ P, ((B p).card : ℝ) := by exact_mod_cast hnat
  have hb : (∑ p ∈ P, ((B p).card : ℝ)) ≤
      ∑ p ∈ P, (3*(N:ℝ)^2/(p:ℝ)^2+4*N+1) := by
    apply sum_le_sum
    intro p hp
    have hh := (mem_filter.mp hp).2
    obtain ⟨hM,ha,hd⟩ := hlarge p hh.1 hh.2
    exact bad_prime_pairs_count hh.1 a b c M v w N hM ha hd
  have ht := prime_reciprocal_square_tail K (L*N) hK
  have hpc : P.card ≤ Nat.primeCounting (L*N) := by
    have hh : P ⊆ (range (L*N+1)).filter Nat.Prime := by
      intro p hp
      exact mem_filter.mpr ⟨(mem_filter.mp hp).1,(mem_filter.mp hp).2.1⟩
    simpa only [Nat.primeCounting,Nat.primeCounting',Nat.count_eq_card_filter_range] using card_le_card hh
  have he : (∑ p ∈ P, (3*(N:ℝ)^2/(p:ℝ)^2+4*N+1)) =
      3*(N:ℝ)^2*(∑ p ∈ P, (1:ℝ)/(p:ℝ)^2)+(4*N+1)*P.card := by
    calc
      _ = ∑ p ∈ P, (3*(N:ℝ)^2*(1/(p:ℝ)^2)+(4*N+1)) := by
        apply sum_congr rfl
        intro p hp
        ring
      _ = _ := by simp only [sum_add_distrib,← mul_sum,sum_const,nsmul_eq_mul]; ring
  rw [he] at hb
  have hh₁ := mul_le_mul_of_nonneg_left ht (show (0:ℝ)≤3*(N:ℝ)^2 by positivity)
  have hh₂ := mul_le_mul_of_nonneg_left
    (show (P.card:ℝ) ≤ Nat.primeCounting (L*N) by exact_mod_cast hpc)
    (show (0:ℝ)≤4*N+1 by positivity)
  change (S.card:ℝ) ≤ _
  change 3*(N:ℝ)^2*(∑p∈P,(1:ℝ)/(p:ℝ)^2) ≤ 3*(N:ℝ)^2*(1/(K:ℝ)) at hh₁
  rw [mul_one_div] at hh₁
  linarith only [hc,hb,hh₁,hh₂]

noncomputable def badTail (a b c H N : ℕ) : Finset (ℕ × ℕ) :=
  (range N ×ˢ range N).filter (fun x => 0 < x.1 ∧
    ∃ p, p.Prime ∧ H < p ∧ p^2 ∣ quad a b c x.1 x.2)

lemma box_value_bounds (a b c N : ℕ) (hc : 0 < c) {x : ℕ × ℕ}
    (hx : x ∈ range N ×ˢ range N) (hxpos : 0 < x.1) :
    0 < quad a b c x.1 x.2 ∧ quad a b c x.1 x.2 ≤ ((a+b+c+1)*N)^2 := by
  obtain ⟨hx1,hx2⟩ := mem_product.mp hx
  have hx1N := (mem_range.mp hx1).le
  have hx2N := (mem_range.mp hx2).le
  have hs1 := Nat.pow_le_pow_left hx1N 2
  have hs2 := Nat.pow_le_pow_left hx2N 2
  have hprod := Nat.mul_le_mul hx1N hx2N
  constructor
  · dsimp [quad]; positivity
  · have hh : quad a b c x.1 x.2 ≤ (a+b+c)*N^2 := by
      dsimp [quad]
      have h1 := Nat.mul_le_mul_left a hs2
      have h2 := Nat.mul_le_mul_left b hprod
      have h3 := Nat.mul_le_mul_left c hs1
      nlinarith only [h1,h2,h3]
    have hh' : a+b+c ≤ (a+b+c+1)^2 := by nlinarith
    have ht := Nat.mul_le_mul_right (N^2) hh'
    rw [mul_pow]
    exact hh.trans ht

lemma regular_of_large (a b c : ℕ) (ha : 0 < a)
    (hdisc : (b:ℤ)^2-4*a*c ≠ 0) {p : ℕ}
    (hlarge : a+((b:ℤ)^2-4*a*c).natAbs < p) :
    (a:ZMod p) ≠ 0 ∧ (b:ZMod p)^2-4*a*c ≠ 0 := by
  constructor
  · intro hz
    have hp := (CharP.cast_eq_zero_iff (ZMod p) p a).mp hz
    have hh := Nat.le_of_dvd ha hp
    omega
  · intro hz
    have hp : (p:ℤ) ∣ (b:ℤ)^2-4*a*c := by
      apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp
      simpa only [Int.cast_sub,Int.cast_pow,Int.cast_mul,Int.cast_ofNat,Int.cast_natCast] using hz
    have hh := Int.natAbs_le_of_dvd_ne_zero hp hdisc
    simp only [Int.natAbs_natCast] at hh
    omega

/-- A fixed cutoff makes the square-divisor tail arbitrarily small in all
sufficiently large boxes. The cutoff does not depend on the box size. -/
theorem uniform_square_tail (a b c : ℕ) (ha : 0 < a) (hc : 0 < c)
    (hdisc : (b:ℤ)^2-4*a*c ≠ 0) {ε : ℝ} (hε : 0 < ε) :
    ∃ H : ℕ, ∀ᶠ N : ℕ in atTop, ((badTail a b c H N).card:ℝ) ≤ ε*(N:ℝ)^2 := by
  obtain ⟨H₀,hH₀⟩ := exists_nat_gt (6/ε)
  let H := H₀+a+((b:ℤ)^2-4*a*c).natAbs+1
  have hH : 0 < H := by dsimp [H]; omega
  have hHR : (0:ℝ) < H := by exact_mod_cast hH
  have hbound : 3/(H:ℝ) ≤ ε/2 := by
    have hH₀H : H₀ ≤ H := by dsimp [H]; omega
    have hh : 6/ε < (H:ℝ) := hH₀.trans_le (by exact_mod_cast hH₀H)
    have hh' := (div_lt_iff₀ hε).mp hh
    apply (div_le_iff₀ hHR).mpr
    linarith
  refine ⟨H,?_⟩
  filter_upwards [primeCounting_mul_eventually_le (a+b+c+1) (show 0 < ε/10 by positivity),
    eventually_ge_atTop 1] with N hpc hN
  have hcount := square_tail_count a b c 1 0 0 N H (a+b+c+1) hH
    (fun p hp hpH => ⟨by simp,regular_of_large a b c ha hdisc (by dsimp [H] at hpH; omega)⟩)
    (fun x hx hxpos => by simpa only [one_mul,add_zero] using box_value_bounds a b c N hc hx hxpos)
  simp only [one_mul,add_zero] at hcount
  have hmain := mul_le_mul_of_nonneg_right hbound (sq_nonneg (N:ℝ))
  have herror := mul_le_mul_of_nonneg_left hpc (show (0:ℝ) ≤ 4*N+1 by positivity)
  have hNR : (1:ℝ) ≤ N := by exact_mod_cast hN
  have hsmall : (ε/10)*(N:ℝ) ≤ (ε/10)*(N:ℝ)^2 :=
    mul_le_mul_of_nonneg_left (by nlinarith) (by positivity)
  change ((badTail a b c H N).card:ℝ) ≤ _ at hcount
  simp only [div_eq_mul_inv] at hcount hmain
  nlinarith only [hcount,hmain,herror,hsmall]

lemma badTail_mono {a b c H K N : ℕ} (hHK : H ≤ K) :
    badTail a b c K N ⊆ badTail a b c H N := by
  intro x hx
  obtain ⟨hxbox,hxpos,p,hp,hKp,hdiv⟩ := mem_filter.mp hx
  exact mem_filter.mpr ⟨hxbox,hxpos,p,hp,lt_of_le_of_lt hHK hKp,hdiv⟩

#print axioms uniform_square_tail
end Erdos1206.QuadraticSquareTail
