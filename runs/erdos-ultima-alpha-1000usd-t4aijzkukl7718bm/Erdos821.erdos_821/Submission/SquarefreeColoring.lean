import Submission.PolylogSpectrumInterval

/-!
# Coloring squarefree preimages and convolution of output fibers

The finite inequalities retain the cost of the possible divisor outputs.
They do not establish the extra lower bound needed for exponent amplification.
-/

open Nat Filter ArithmeticFunction
open scoped Classical BigOperators ArithmeticFunction.zeta
namespace Erdos821
open HigherDivisors
set_option maxHeartbeats 3000000

noncomputable def squarefreeFiber (n : ℕ) : Finset ℕ :=
  (finite_squarefree_totient_fiber n).toFinset

@[simp] lemma mem_squarefreeFiber (n m : ℕ) :
    m ∈ squarefreeFiber n ↔ Squarefree m ∧ totient m=n :=
  (finite_squarefree_totient_fiber n).mem_toFinset

lemma squarefreeFiber_card (n : ℕ) : (squarefreeFiber n).card=gSquarefree n :=
  (Set.ncard_eq_toFinset_card _ (finite_squarefree_totient_fiber n)).symm

noncomputable def coloredFiber (r n : ℕ) : ℕ :=
  ∑ m ∈ squarefreeFiber n, tau r m

lemma tau_squarefree (r m : ℕ) (hr : 1≤r) (hm : Squarefree m) :
    tau r m=r^m.primeFactors.card := by
  have hr' : r-1+1=r := Nat.sub_add_cancel hr
  have H := (tau_multiplicative r).multiplicative_factorization
    ((ζ : ArithmeticFunction ℕ)^r) hm.ne_zero
  change tau r m = _ at H
  rw [H]
  simp only [Finsupp.prod,Nat.support_factorization]
  calc
    _ = ∏ _p ∈ m.primeFactors, r := by
      apply Finset.prod_congr rfl
      intro p hp
      rw [Nat.factorization_eq_one_of_squarefree hm (Nat.prime_of_mem_primeFactors hp)
        (Nat.dvd_of_mem_primeFactors hp),pow_one]
      change tau r p=r
      rw [← hr']
      have h := tau_prime_pow (r-1) 1 p (Nat.prime_of_mem_primeFactors hp)
      simpa only [pow_one,Nat.add_comm 1 (r-1),Nat.choose_succ_self_right] using h
    _ = _ := Finset.prod_const _

lemma coloredFiber_eq_color_sum (r n : ℕ) (hr : 1≤r) :
    coloredFiber r n = ∑ m ∈ squarefreeFiber n, r^m.primeFactors.card := by
  apply Finset.sum_congr rfl
  intro m hm
  exact tau_squarefree r m hr (mem_squarefreeFiber n m |>.mp hm).1

lemma coloredFiber_one (n : ℕ) : coloredFiber 1 n=gSquarefree n := by
  rw [coloredFiber_eq_color_sum 1 n (by decide)]
  simp only [one_pow,Finset.sum_const,smul_eq_mul,mul_one,squarefreeFiber_card]

/-- Pushing a convolution through phi is bounded above by convolving the
pushed weights. Every divisor pair of a squarefree input is coprime. -/
lemma squarefree_convolution_push_le (f h : ArithmeticFunction ℕ) (n : ℕ) (hn : 0<n) :
    (∑ m ∈ squarefreeFiber n, (f*h) m) ≤
      ∑ d ∈ n.divisors,
        (∑ a ∈ squarefreeFiber d, f a)*(∑ b ∈ squarefreeFiber (n/d), h b) := by
  let A := (squarefreeFiber n).biUnion (fun m => m.divisorsAntidiagonal)
  let B := n.divisors.biUnion (fun d => squarefreeFiber d ×ˢ squarefreeFiber (n/d))
  have hAdis : (squarefreeFiber n : Set ℕ).Pairwise
      (fun a b => Disjoint a.divisorsAntidiagonal b.divisorsAntidiagonal) := by
    intro a _ b _ hab
    apply Finset.disjoint_left.mpr
    intro uv hu hv
    exact hab ((Nat.mem_divisorsAntidiagonal.mp hu).1.symm.trans
      (Nat.mem_divisorsAntidiagonal.mp hv).1)
  have hBdis : (n.divisors : Set ℕ).Pairwise
      (fun a b => Disjoint (squarefreeFiber a ×ˢ squarefreeFiber (n/a))
        (squarefreeFiber b ×ˢ squarefreeFiber (n/b))) := by
    intro a _ b _ hab
    apply Finset.disjoint_left.mpr
    intro uv hu hv
    have hU := (mem_squarefreeFiber a uv.1).mp (Finset.mem_product.mp hu).1
    have hV := (mem_squarefreeFiber b uv.1).mp (Finset.mem_product.mp hv).1
    exact hab (hU.2.symm.trans hV.2)
  have hsub : A⊆B := by
    intro uv huv
    obtain ⟨m,hm,huv⟩ := Finset.mem_biUnion.mp huv
    obtain ⟨hmsq,hmφ⟩ := (mem_squarefreeFiber n m).mp hm
    obtain ⟨huvprod,hm0⟩ := Nat.mem_divisorsAntidiagonal.mp huv
    have hu0 : 0<uv.1 := Nat.pos_of_ne_zero (fun h => hm0 (by rw [← huvprod,h,zero_mul]))
    have hmulSq : Squarefree (uv.1*uv.2) := huvprod.symm ▸ hmsq
    have hcop := Nat.coprime_of_squarefree_mul hmulSq
    have husq := hmulSq.squarefree_of_dvd (dvd_mul_right uv.1 uv.2)
    have hvsq := hmulSq.squarefree_of_dvd (dvd_mul_left uv.2 uv.1)
    have hφ : totient uv.1*totient uv.2=n := by
      rw [← Nat.totient_mul hcop,huvprod,hmφ]
    have hdu : totient uv.1 ∣ n := ⟨totient uv.2,hφ.symm⟩
    have hdv : totient uv.2=n/totient uv.1 :=
      Nat.eq_div_of_mul_eq_left (Nat.totient_pos.mpr hu0).ne' (by simpa only [mul_comm] using hφ)
    apply Finset.mem_biUnion.mpr
    refine ⟨totient uv.1,Nat.mem_divisors.mpr ⟨hdu,hn.ne'⟩,?_⟩
    exact Finset.mem_product.mpr
      ⟨(mem_squarefreeFiber _ _).mpr ⟨husq,rfl⟩,
       (mem_squarefreeFiber _ _).mpr ⟨hvsq,hdv⟩⟩
  calc
    _ = ∑ uv ∈ A, f uv.1*h uv.2 := by
      simp only [ArithmeticFunction.mul_apply]
      rw [Finset.sum_biUnion hAdis]
    _ ≤ ∑ uv ∈ B, f uv.1*h uv.2 := Finset.sum_le_sum_of_subset hsub
    _ = _ := by
      rw [Finset.sum_biUnion hBdis]
      apply Finset.sum_congr rfl
      intro d hd
      rw [Finset.sum_product,Finset.sum_mul_sum]

lemma coloredFiber_double_le (r n : ℕ) (hn : 0<n) :
    coloredFiber (2*r) n ≤ ∑ d ∈ n.divisors, coloredFiber r d*coloredFiber r (n/d) := by
  have H := squarefree_convolution_push_le ((ζ : ArithmeticFunction ℕ)^r)
    ((ζ : ArithmeticFunction ℕ)^r) n hn
  simpa only [← pow_add,← two_mul,coloredFiber,tau] using H

/-- At a fixed arity lower bound k, the count includes all r^k color choices
for every input. No small-output-tuple estimate is silently dropped. -/
lemma finite_squarefree_fiber_color_lower (F : Finset ℕ) (n r k : ℕ) (hr : 1≤r)
    (hF : ∀ m ∈ F, Squarefree m ∧ totient m=n ∧ k ≤ m.primeFactors.card) :
    F.card*r^k ≤ coloredFiber r n := by
  rw [coloredFiber_eq_color_sum r n hr]
  calc
    _ = ∑ _m ∈ F, r^k := by simp
    _ ≤ ∑ m ∈ F, r^m.primeFactors.card := Finset.sum_le_sum
      (fun m hm => Nat.pow_le_pow_right hr (hF m hm).2.2)
    _ ≤ _ := Finset.sum_le_sum_of_subset (fun m hm =>
      (mem_squarefreeFiber n m).mpr ⟨(hF m hm).1,(hF m hm).2.1⟩)


/-- Uniform in the number r=2^j of colors. Bounds on the divisor outputs imply this
bound on all squarefree coloring counts, including the divisor-tuple cost. -/
theorem coloredFiber_two_pow_le_of_divisor_bound (C s : ℝ) (hC : 0≤C)
    (j n : ℕ) (hn : 0<n)
    (H : ∀ d ∈ n.divisors, (g d : ℝ) ≤ C*(d : ℝ)^s) :
    (coloredFiber (2^j) n : ℝ) ≤ C^(2^j)*(n : ℝ)^s*
      (n.divisors.card : ℝ)^(2^j-1) := by
  induction j generalizing n with
  | zero =>
    simpa only [pow_zero,pow_one,coloredFiber_one,Nat.sub_self,mul_one] using
      (show (gSquarefree n : ℝ) ≤ C*(n : ℝ)^s from
        (show (gSquarefree n : ℝ) ≤ (g n : ℝ) by exact_mod_cast gSquarefree_le_g n).trans (H n (Nat.mem_divisors.mpr ⟨dvd_refl n,hn.ne'⟩)))
  | succ j ih =>
    let r := 2^j
    let T : ℝ := n.divisors.card
    let W : ℝ := C^r*T^(r-1)
    have hr : 1≤r := Nat.one_le_pow _ _ (by decide)
    have hT : 0≤T := Nat.cast_nonneg _
    have hτ (d : ℕ) (hd : d ∈ n.divisors) : (d.divisors.card : ℝ)≤T := by
      have h : d.divisors ⊆ n.divisors := by
        intro a ha
        exact Nat.mem_divisors.mpr
          ⟨(Nat.dvd_of_mem_divisors ha).trans (Nat.dvd_of_mem_divisors hd),hn.ne'⟩
      dsimp [T]
      exact_mod_cast Finset.card_le_card h
    have hbound (d : ℕ) (hd : d ∈ n.divisors) :
        (coloredFiber r d : ℝ) ≤ W*(d : ℝ)^s := by
      have hh := ih d (Nat.pos_of_mem_divisors hd) (fun a ha =>
        H a (Nat.mem_divisors.mpr
          ⟨(Nat.dvd_of_mem_divisors ha).trans (Nat.dvd_of_mem_divisors hd),hn.ne'⟩))
      calc
        _ ≤ C^r*(d : ℝ)^s*(d.divisors.card : ℝ)^(r-1) := hh
        _ ≤ C^r*(d : ℝ)^s*T^(r-1) :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (Nat.cast_nonneg _) (hτ d hd) _)
            (mul_nonneg (pow_nonneg hC _) (Real.rpow_nonneg (Nat.cast_nonneg _) _))
        _ = _ := by dsimp [W]; ring
    have hterm (d : ℕ) (hd : d ∈ n.divisors) :
        (coloredFiber r d : ℝ)*(coloredFiber r (n/d) : ℝ) ≤ W^2*(n : ℝ)^s := by
      have hdvd := Nat.dvd_of_mem_divisors hd
      have hd0 := Nat.pos_of_mem_divisors hd
      have hnd : n/d ∈ n.divisors := Nat.mem_divisors.mpr ⟨Nat.div_dvd_of_dvd hdvd,hn.ne'⟩
      have hprod : (d : ℝ)*((n/d : ℕ) : ℝ)=(n : ℝ) := by
        exact_mod_cast Nat.mul_div_cancel' hdvd
      calc
        _ ≤ (W*(d : ℝ)^s)*(W*((n/d : ℕ) : ℝ)^s) :=
          mul_le_mul (hbound d hd) (hbound (n/d) hnd) (Nat.cast_nonneg _)
            (by dsimp [W]; positivity)
        _ = W^2*((d : ℝ)^s*((n/d : ℕ) : ℝ)^s) := by ring
        _ = _ := by rw [← Real.mul_rpow (Nat.cast_nonneg _) (Nat.cast_nonneg _),hprod]
    have hmain : (coloredFiber (2*r) n : ℝ) ≤ T*W^2*(n : ℝ)^s := by
      calc
        _ ≤ ∑ d ∈ n.divisors, (coloredFiber r d : ℝ)*(coloredFiber r (n/d) : ℝ) := by
          exact_mod_cast coloredFiber_double_le r n hn
        _ ≤ ∑ _d ∈ n.divisors, W^2*(n : ℝ)^s := Finset.sum_le_sum hterm
        _ = _ := by simp only [Finset.sum_const,nsmul_eq_mul,T]; ring
    have hTeq : T*T^((r-1)*2)=T^(2*r-1) := by
      rw [← _root_.pow_succ']
      congr 1
      omega
    have heq : T*W^2*(n : ℝ)^s = C^(2*r)*(n : ℝ)^s*T^(2*r-1) := by
      dsimp [W]
      rw [mul_pow,← pow_mul,← pow_mul,mul_comm r 2]
      calc
        _ = C^(2*r)*(n : ℝ)^s*(T*T^((r-1)*2)) := by ring
        _ = _ := by rw [hTeq]
    simp only [_root_.pow_succ']
    exact hmain.trans_eq heq

/-- A global power bound is a sufficient hypothesis for the local estimate. -/
theorem coloredFiber_two_pow_le_of_power_bound (C s : ℝ) (hC : 0≤C)
    (H : ∀ n : ℕ, 0<n → (g n : ℝ) ≤ C*(n : ℝ)^s)
    (j n : ℕ) (hn : 0<n) :
    (coloredFiber (2^j) n : ℝ) ≤ C^(2^j)*(n : ℝ)^s*
      (n.divisors.card : ℝ)^(2^j-1) :=
  coloredFiber_two_pow_le_of_divisor_bound C s hC j n hn
    (fun d hd => H d (Nat.pos_of_mem_divisors hd))

/-- A finite test for a coloring amplification. The bound on g is an
explicit hypothesis and the coloring/divisor factors are both retained. -/
theorem finite_color_bound_of_g_power (C s : ℝ) (hC : 0≤C)
    (H : ∀ n : ℕ, 0<n → (g n : ℝ) ≤ C*(n : ℝ)^s)
    (F : Finset ℕ) (n j k : ℕ) (hn : 0<n)
    (hF : ∀ m ∈ F, Squarefree m ∧ totient m=n ∧ k ≤ m.primeFactors.card) :
    (F.card : ℝ)*(2^j : ℝ)^k ≤ C^(2^j)*(n : ℝ)^s*
      (n.divisors.card : ℝ)^(2^j-1) := by
  have h := finite_squarefree_fiber_color_lower F n (2^j) k
    (Nat.one_le_pow _ _ (by decide)) hF
  exact (by exact_mod_cast h : (F.card : ℝ)*(2^j : ℝ)^k ≤ coloredFiber (2^j) n).trans
    (coloredFiber_two_pow_le_of_power_bound C s hC H j n hn)

/-- Actual finite amplification is available if the coloring count exceeds
BOTH the putative fiber bound and the divisor-tuple cost. The excess is an
explicit arithmetic/combinatorial hypothesis, not asserted here. -/
theorem exists_divisor_large_g_of_coloring (C s : ℝ) (hC : 0≤C)
    (F : Finset ℕ) (n j k : ℕ) (hn : 0<n)
    (hF : ∀ m ∈ F, Squarefree m ∧ totient m=n ∧ k ≤ m.primeFactors.card)
    (hcolor : C^(2^j)*(n : ℝ)^s*(n.divisors.card : ℝ)^(2^j-1) <
      (F.card : ℝ)*(2^j : ℝ)^k) :
    ∃ d ∈ n.divisors, C*(d : ℝ)^s < (g d : ℝ) := by
  by_contra H
  push_neg at H
  have hb := coloredFiber_two_pow_le_of_divisor_bound C s hC j n hn H
  have hl : (F.card : ℝ)*(2^j : ℝ)^k ≤ (coloredFiber (2^j) n : ℝ) := by
    exact_mod_cast finite_squarefree_fiber_color_lower F n (2^j) k
      (Nat.one_le_pow _ _ (by decide)) hF
  exact hcolor.not_ge (hl.trans hb)

end Erdos821
