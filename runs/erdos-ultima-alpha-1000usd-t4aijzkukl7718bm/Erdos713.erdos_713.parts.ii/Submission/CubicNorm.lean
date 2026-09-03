import FormalConjecturesUtil
import Submission.UpToEdgeFans

/-! The cubic norm graph and its seven common-neighbor obstruction. -/

open Filter SimpleGraph Asymptotics

namespace Erdos713CubicNorm
open Polynomial Finset
variable {F : Type*} [Field F]

def normMap (σ τ : F →+* F) : F →*₀ F where
  toFun x := x * σ x * τ x
  map_zero' := by simp
  map_one' := by simp
  map_mul' x y := by simp only [map_mul]; ring

@[simp] lemma normMap_apply (σ τ : F →+* F) (x : F) : normMap σ τ x = x * σ x * τ x := rfl

lemma normMap_ne_zero (σ τ : F →+* F) {x : F} (hx : x ≠ 0) : normMap σ τ x ≠ 0 :=
  mul_ne_zero (mul_ne_zero hx ((_root_.map_ne_zero σ).mpr hx)) ((_root_.map_ne_zero τ).mpr hx)

noncomputable def numerator (a b a₁ a₂ A B : F) : F[X] :=
  (C B * X - C A * (X + C a) - C (a₁ * a₂) * X * (X + C a)) * (X + C b)

noncomputable def elimV (a b a₁ b₁ a₂ b₂ A B D : F) : F[X] :=
  C b₁ * numerator a b a₁ a₂ A B - C a₁ * numerator b a b₁ b₂ A D

noncomputable def elimW (a b a₁ b₁ a₂ b₂ A B D : F) : F[X] :=
  C a₂ * numerator b a b₁ b₂ A D - C b₂ * numerator a b a₁ a₂ A B

noncomputable def circlePoly (a b a₁ b₁ a₂ b₂ A B D : F) : F[X] :=
  elimV a b a₁ b₁ a₂ b₂ A B D * elimW a b a₁ b₁ a₂ b₂ A B D -
    C ((a₂ * b₁ - a₁ * b₂)^2 * A) * X * (X + C a)^2 * (X + C b)^2

lemma circlePoly_degree_le (a b a₁ b₁ a₂ b₂ A B D : F) :
    (circlePoly a b a₁ b₁ a₂ b₂ A B D).natDegree ≤ 6 := by
  unfold circlePoly elimV elimW numerator
  compute_degree

lemma circlePoly_coeff_six (a b a₁ b₁ a₂ b₂ A B D : F) :
    (circlePoly a b a₁ b₁ a₂ b₂ A B D).coeff 6 =
      (a₁ * b₁ * (b₂ - a₂)) * (a₂ * b₂ * (a₁ - b₁)) := by
  unfold circlePoly elimV elimW numerator
  compute_degree <;> norm_num <;> ring

lemma numerator_eval {a b a₁ a₂ A B u v w : F}
    (h0 : u*v*w = A) (h1 : (u+a)*(v+a₁)*(w+a₂) = B) :
    (numerator a b a₁ a₂ A B).eval u = u*(u+a)*(u+b)*(a₂*v+a₁*w) := by
  simp only [numerator, eval_mul, eval_sub, eval_add, eval_C, eval_X]
  linear_combination -(u+b)*u*h1 + (u+b)*(u+a)*h0

lemma circlePoly_eval {a b a₁ b₁ a₂ b₂ A B D u v w : F}
    (h0 : u*v*w = A) (h1 : (u+a)*(v+a₁)*(w+a₂) = B)
    (h2 : (u+b)*(v+b₁)*(w+b₂) = D) :
    (circlePoly a b a₁ b₁ a₂ b₂ A B D).eval u = 0 := by
  have hV : (elimV a b a₁ b₁ a₂ b₂ A B D).eval u =
      (a₂*b₁-a₁*b₂)*v*u*(u+a)*(u+b) := by
    simp only [elimV, eval_sub, eval_mul, eval_C, numerator_eval h0 h1, numerator_eval h0 h2]
    ring
  have hW : (elimW a b a₁ b₁ a₂ b₂ A B D).eval u =
      (a₂*b₁-a₁*b₂)*w*u*(u+a)*(u+b) := by
    simp only [elimW, eval_sub, eval_mul, eval_C, numerator_eval h0 h1, numerator_eval h0 h2]
    ring
  simp only [circlePoly, eval_sub, eval_mul, eval_pow, eval_add, eval_X, eval_C, hV, hW]
  linear_combination (a₂*b₁-a₁*b₂)^2*u*(u+a)^2*(u+b)^2*h0

lemma norm_circles_no_seven (σ τ : F →+* F) {c₀ c₁ c₂ A B D : F}
    (h01 : c₀ ≠ c₁) (h02 : c₀ ≠ c₂) (h12 : c₁ ≠ c₂)
    (x : Fin 7 → F) (hx : Function.Injective x)
    (h0 : ∀ j, normMap σ τ (x j + c₀) = A)
    (h1 : ∀ j, normMap σ τ (x j + c₁) = B)
    (h2 : ∀ j, normMap σ τ (x j + c₂) = D) : False := by
  let a := c₁-c₀
  let b := c₂-c₀
  let P := circlePoly a b (σ a) (σ b) (τ a) (τ b) A B D
  have ha : a ≠ 0 := sub_ne_zero.mpr h01.symm
  have hb : b ≠ 0 := sub_ne_zero.mpr h02.symm
  have hab : a ≠ b := fun hh => h12 (sub_left_injective hh)
  have hP : P ≠ 0 := by
    intro he
    have hc := circlePoly_coeff_six a b (σ a) (σ b) (τ a) (τ b) A B D
    change P.coeff 6 = _ at hc
    rw [he, coeff_zero] at hc
    exact (mul_ne_zero
      (mul_ne_zero (mul_ne_zero ((_root_.map_ne_zero σ).mpr ha) ((_root_.map_ne_zero σ).mpr hb))
        (sub_ne_zero.mpr (τ.injective.ne hab.symm)))
      (mul_ne_zero (mul_ne_zero ((_root_.map_ne_zero τ).mpr ha) ((_root_.map_ne_zero τ).mpr hb))
        (sub_ne_zero.mpr (σ.injective.ne hab)))) hc.symm
  apply hP
  apply Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero P
    (show Function.Injective (fun j : Fin 7 => x j + c₀) from fun i j hij => hx (add_right_cancel hij))
  · intro j
    apply circlePoly_eval (v := σ (x j+c₀)) (w := τ (x j+c₀))
    · exact h0 j
    · convert h1 j using 1 <;> simp only [a, b, normMap_apply, map_sub, map_add] <;> ring
    · convert h2 j using 1 <;> simp only [a, b, normMap_apply, map_sub, map_add] <;> ring
  · exact (circlePoly_degree_le ..).trans_lt (by decide : 6 < Fintype.card (Fin 7))


lemma normalized_circle (σ τ : F →+* F) {r s z a a₀ b : F}
    (hrs : r ≠ s) (hsz : s+z ≠ 0) (ha₀ : a₀ ≠ 0) (hb : b ≠ 0)
    (h1 : normMap σ τ (r+z) = a*b) (h2 : normMap σ τ (s+z) = a₀*b) :
    normMap σ τ ((s+z)⁻¹ + (r-s)⁻¹) = a / (a₀ * normMap σ τ (r-s)) := by
  have hdiff : r-s ≠ 0 := sub_ne_zero.mpr hrs
  have he : (s+z)⁻¹ + (r-s)⁻¹ = (r+z) / ((s+z)*(r-s)) := by field_simp; ring
  rw [he, map_div₀, map_mul, h1, h2]
  field_simp

lemma no_norm_rectangle (σ τ : F →+* F) (a A : Fin 4 → F) (b B : Fin 7 → F)
    (hA : ∀ i, A i ≠ 0) (hB : ∀ j, B j ≠ 0)
    (haA : Function.Injective (fun i => (a i,A i)))
    (hbB : Function.Injective (fun j => (b j,B j)))
    (he : ∀ i j, normMap σ τ (a i+b j) = A i*B j) : False := by
  have ha : Function.Injective a := by
    intro i k hik
    have hmul : A i*B 0 = A k*B 0 := by rw [← he, hik, he]
    exact haA (Prod.ext hik (mul_right_cancel₀ (hB 0) hmul))
  have hb : Function.Injective b := by
    intro j k hjk
    have hmul : A 0*B j = A 0*B k := by rw [← he, hjk, he]
    exact hbB (Prod.ext hjk (mul_left_cancel₀ (hA 0) hmul))
  have hsum (j : Fin 7) : a 3+b j ≠ 0 := by
    intro hz
    have hh := he 3 j
    rw [hz, map_zero] at hh
    exact mul_ne_zero (hA 3) (hB j) hh.symm
  let x : Fin 7 → F := fun j => (a 3+b j)⁻¹
  let c : Fin 4 → F := fun i => (a i-a 3)⁻¹
  have hc : Function.Injective c := by
    intro i k hik
    exact ha (sub_left_injective (inv_injective hik))
  have hcircle (i : Fin 4) (hi : i ≠ 3) (j : Fin 7) :
      normMap σ τ (x j+c i) = A i / (A 3 * normMap σ τ (a i-a 3)) :=
    normalized_circle σ τ (ha.ne hi) (hsum j) (hA 3) (hB j) (he i j) (he 3 j)
  have hx : Function.Injective x := fun i j hij => hb (add_left_cancel (inv_injective hij))
  exact norm_circles_no_seven σ τ (hc.ne (by decide : (0 : Fin 4) ≠ 1))
    (hc.ne (by decide : (0 : Fin 4) ≠ 2)) (hc.ne (by decide : (1 : Fin 4) ≠ 2)) x hx
    (hcircle 0 (by decide)) (hcircle 1 (by decide)) (hcircle 2 (by decide))

abbrev K47 := completeBipartiteGraph (Fin 4) (Fin 7)
abbrev K4t (t : ℕ) := completeBipartiteGraph (Fin 4) (Fin t)

section Graph
variable (K F : Type*) [Field K] [Field F] [Algebra K F]
open Erdos713Norm

lemma graph_free (σ τ : F →+* F)
    (hNorm : ∀ x : F, algebraMap K F (Algebra.norm K x) = Erdos713CubicNorm.normMap σ τ x) :
    K47.Free (graph K F) := by
  rintro ⟨f⟩
  have hAdj (i : Fin 4) (j : Fin 7) : (graph K F).Adj (f (Sum.inl i)) (f (Sum.inr j)) :=
    f.toHom.map_rel' (by simp [completeBipartiteGraph])
  let L : Fin 4 → Vertex K F := fun i => project K F (f (Sum.inl i))
  let R : Fin 7 → Vertex K F := fun j => project K F (f (Sum.inr j))
  have hL : Function.Injective L := by
    intro i k hik
    exact Sum.inl.inj (f.injective (eq_of_common_neighbor K F (hAdj i 0) (hAdj k 0) hik))
  have hR : Function.Injective R := by
    intro j k hjk
    exact Sum.inr.inj (f.injective (eq_of_common_neighbor K F (hAdj 0 j).symm (hAdj 0 k).symm hjk))
  apply no_norm_rectangle σ τ (fun i => (L i).1) (fun i => algebraMap K F ((L i).2 : K))
    (fun j => (R j).1) (fun j => algebraMap K F ((R j).2 : K))
  · intro i
    exact (_root_.map_ne_zero _).mpr (L i).2.ne_zero
  · intro j
    exact (_root_.map_ne_zero _).mpr (R j).2.ne_zero
  · exact (vertex_embed_injective K F).comp hL
  · exact (vertex_embed_injective K F).comp hR
  · intro i j
    rw [← hNorm, ← map_mul]
    exact congrArg (algebraMap K F) (norm_eq_of_adj K F (hAdj i j))

lemma extremal_lower [FiniteDimensional K F] [Fintype K] [Fintype F]
    (hfree : K47.Free (graph K F)) :
    Fintype.card F * (Fintype.card K-1) * (Fintype.card F-1) ≤
      extremalNumber (2 * Fintype.card F * (Fintype.card K-1)) K47 := by
  classical
  have hE := edge_lower K F
  have hExt := card_edgeFinset_le_extremalNumber hfree
  have hN : Fintype.card (Vertex K F ⊕ Vertex K F) = 2 * Fintype.card F * (Fintype.card K-1) := by
    simp only [Vertex, Fintype.card_sum, Fintype.card_prod, Fintype.card_units]
    ring
  rw [hN] at hExt
  exact hE.trans hExt

end Graph

section FiniteField
variable (p : ℕ) [Fact p.Prime]

lemma finite_norm_formula (x : GaloisField p 3) :
    algebraMap (ZMod p) (GaloisField p 3) (Algebra.norm (ZMod p) x) =
      normMap (frobenius (GaloisField p 3) p)
        ((frobenius (GaloisField p 3) p).comp (frobenius (GaloisField p 3) p)) x := by
  rw [FiniteField.algebraMap_norm_eq_prod_pow, GaloisField.finrank p (by decide : 3 ≠ 0)]
  simp only [Nat.card_zmod, Finset.prod_range_succ, Finset.prod_range_zero, pow_zero, pow_one,
    one_mul, normMap_apply, RingHom.comp_apply, frobenius_def]
  rw [← pow_mul, pow_two]

lemma finite_graph_free :
    K47.Free (Erdos713Norm.graph (ZMod p) (GaloisField p 3)) :=
  graph_free (ZMod p) (GaloisField p 3) (frobenius (GaloisField p 3) p)
    ((frobenius (GaloisField p 3) p).comp (frobenius (GaloisField p 3) p)) (finite_norm_formula p)

end FiniteField

lemma extremal_lower_prime (p : ℕ) (hp : p.Prime) :
    p^7 ≤ 4 * extremalNumber (2 * p^3 * (p-1)) K47 := by
  classical
  letI : Fact p.Prime := ⟨hp⟩
  letI : Fintype (GaloisField p 3) := Fintype.ofFinite _
  have hF : Fintype.card (GaloisField p 3) = p^3 := by
    rw [Fintype.card_eq_nat_card]
    exact GaloisField.card p 3 (by decide)
  have hBound := extremal_lower (ZMod p) (GaloisField p 3) (finite_graph_free p)
  rw [hF, ZMod.card] at hBound
  have hp1 : p ≤ 2 * (p-1) := by have := hp.two_le; omega
  have hp3 : p^3 ≤ 2 * (p^3-1) := by
    have hh : 2 ≤ p^3 := hp.two_le.trans (Nat.le_self_pow (by decide) p)
    omega
  have hprod := Nat.mul_le_mul_left (p^3) (Nat.mul_le_mul hp1 hp3)
  have hlow : p^7 ≤ 4 * (p^3 * (p-1) * (p^3-1)) := by nlinarith only [hprod]
  exact hlow.trans (Nat.mul_le_mul_left 4 hBound)

theorem lower_exponent_of_prime_bound {f : ℕ → ℕ} {a : ℝ} (ha : 0 ≤ a)
    (hO : (fun n : ℕ => (f n : ℝ)) =O[atTop] (fun n : ℕ => (n : ℝ) ^ a))
    (hlow : ∀ p : ℕ, p.Prime → p ^ 7 ≤ 4 * f (2 * p ^ 3 * (p - 1))) :
    (7 : ℝ) / 4 ≤ a := by
  by_contra hna
  have ha' : a < (7 : ℝ) / 4 := lt_of_not_ge hna
  obtain ⟨C, hCpos, hC⟩ := hO.exists_pos
  have ht : Tendsto (fun p : ℕ => 2 * p ^ 3 * (p - 1)) atTop atTop := by
    apply tendsto_atTop.2
    intro N
    filter_upwards [eventually_ge_atTop (max N 2)] with p hp
    have hp2 : 2 ≤ p := (le_max_right _ _).trans hp
    have hpN : N ≤ p := (le_max_left _ _).trans hp
    have hp1 : 1 ≤ p - 1 := by omega
    have hpow : p ≤ 2 * p ^ 3 := (Nat.le_self_pow (by decide : 3 ≠ 0) p).trans (by omega)
    have hprod := Nat.mul_le_mul_left (2 * p ^ 3) hp1
    omega
  have hratio : ∀ᶠ p : ℕ in atTop,
      p.Prime → (p : ℝ) ^ (7 - 4 * a) ≤ 4 * C * (2 : ℝ) ^ a := by
    filter_upwards [ht.eventually hC.bound, eventually_gt_atTop (0 : ℕ)] with p hp hpos
    intro hprime
    have hp0 : (0 : ℝ) < p := Nat.cast_pos.mpr hpos
    have hl : (p : ℝ) ^ 7 ≤ 4 * (f (2 * p ^ 3 * (p - 1)) : ℝ) := by
      exact_mod_cast hlow p hprime
    have hsize : ((2 * p ^ 3 * (p - 1) : ℕ) : ℝ) ≤ 2 * (p : ℝ) ^ 4 := by
      have hb := Nat.mul_le_mul_left (2 * p ^ 3) (Nat.sub_le p 1)
      have hb' : 2 * p ^ 3 * (p - 1) ≤ 2 * p ^ 4 := by nlinarith only [hb]
      exact_mod_cast hb'
    have hu : (f (2 * p ^ 3 * (p - 1)) : ℝ) ≤ C * (2 * (p : ℝ) ^ 4) ^ a := by
      rw [Real.norm_natCast, Real.norm_of_nonneg
        (Real.rpow_nonneg (Nat.cast_nonneg _) a)] at hp
      exact hp.trans (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (Nat.cast_nonneg _) hsize ha) hCpos.le)
    have he : (p : ℝ) ^ 7 ≤ 4 * C * (2 * (p : ℝ) ^ 4) ^ a := by
      nlinarith only [hl, hu]
    have hp3 : ((p : ℝ) ^ 4) ^ a = (p : ℝ) ^ (4 * a) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hp0.le]
      norm_num
    rw [Real.mul_rpow (by norm_num) (pow_nonneg hp0.le 4), hp3] at he
    rw [Real.rpow_sub hp0, div_le_iff₀ (Real.rpow_pos_of_pos hp0 (4 * a))]
    have hp5 : (p : ℝ) ^ (7 : ℝ) = (p : ℝ) ^ (7 : ℕ) := by
      exact_mod_cast Real.rpow_natCast (p : ℝ) 7
    rw [hp5]
    simpa only [mul_assoc] using he
  have htop : Tendsto (fun p : ℕ => (p : ℝ) ^ (7 - 4 * a)) atTop atTop :=
    (tendsto_rpow_atTop (by linarith : 0 < 7 - 4 * a)).comp tendsto_natCast_atTop_atTop
  obtain ⟨N, hN⟩ := eventually_atTop.mp
    (hratio.and (htop.eventually_gt_atTop (4 * C * (2 : ℝ) ^ a)))
  obtain ⟨p, hpN, hp⟩ := Nat.exists_infinite_primes N
  exact (not_lt_of_ge ((hN p hpN).1 hp)) ((hN p hpN).2)


open Erdos713Rate

lemma rate_of_K47_upper {W : Type*} {H : SimpleGraph W} (hlo : K47 ⊑ H)
    (hu : (fun n : ℕ => (extremalNumber n H : ℝ)) =O[atTop]
      (fun n : ℕ => (n : ℝ) ^ ((7 : ℝ)/4))) : HasRate H ((7 : ℝ)/4) := by
  refine ⟨by norm_num, hu, ?_⟩
  intro a ha h
  apply lower_exponent_of_prime_bound (by linarith) h
  intro p hp
  exact (extremal_lower_prime p hp).trans (Nat.mul_le_mul_left 4 hlo.extremalNumber_le)

lemma rate_of_containment {W : Type*} {H : SimpleGraph W} {t : ℕ}
    (hlo : K47 ⊑ H) (hhi : H ⊑ K4t t) : HasRate H ((7 : ℝ)/4) := by
  apply rate_of_K47_upper hlo
  apply (extremal_mono_bigO hhi).trans
  simpa only [Nat.cast_ofNat] using upper_of_power_bound (by decide : 4 ≠ 0)
    (fun n => Erdos713KST.extremal_pow_le 4 t n (by decide))

lemma contains_K47 {t : ℕ} (ht : 7 ≤ t) : K47 ⊑ K4t t := by
  refine ⟨⟨⟨Sum.map id (Fin.castLE ht), ?_⟩, ?_⟩⟩
  · intro u v huv
    cases u <;> cases v <;> simpa [K47, K4t, completeBipartiteGraph] using huv
  · exact Sum.map_injective.mpr ⟨Function.injective_id, Fin.castLE_injective ht⟩

lemma rate {t : ℕ} (ht : 7 ≤ t) : HasRate (K4t t) ((7 : ℝ)/4) :=
  rate_of_containment (contains_K47 ht) (.refl _)

lemma exponent_eq_of_containment {W : Type*} {H : SimpleGraph W} {t : ℕ}
    (hlo : K47 ⊑ H) (hhi : H ⊑ K4t t) {a c : ℝ} (ha : 1 ≤ a) (hc : c ≠ 0)
    (h : IsEquivalent atTop (fun n : ℕ => (extremalNumber n H : ℝ))
      (fun n : ℕ => c * (n : ℝ) ^ a)) : a = (7 : ℝ)/4 :=
  Erdos713Rate.exponent_eq (rate_of_containment hlo hhi) ha hc h

lemma rational_exponent_of_containment {W : Type*} {H : SimpleGraph W} {t : ℕ}
    (hlo : K47 ⊑ H) (hhi : H ⊑ K4t t) {a c : ℝ} (ha : 1 ≤ a) (hc : c ≠ 0)
    (h : IsEquivalent atTop (fun n : ℕ => (extremalNumber n H : ℝ))
      (fun n : ℕ => c * (n : ℝ) ^ a)) : a ∈ Set.range ((↑) : ℚ → ℝ) := by
  refine ⟨7/4, ?_⟩
  simpa using (exponent_eq_of_containment hlo hhi ha hc h).symm

lemma four_exceptions_rate {W : Type*} [Fintype W] (H : SimpleGraph W) (S E : Set W)
    (hB : H.IsBipartiteWith S Sᶜ) (hE : Nat.card E ≤ 4)
    (hdeg : ∀ v ∈ Sᶜ, v ∉ E → Nat.card (H.neighborSet v) ≤ 4)
    (hlo : K47 ⊑ H) : HasRate H ((7 : ℝ)/4) := by
  classical
  obtain ⟨f⟩ := hlo
  letI : Nonempty S := nonempty_left_of_copy H S hB f (u := Sum.inl 0) (v := Sum.inr 0)
    (by simp [K47, completeBipartiteGraph])
  apply rate_of_K47_upper ⟨f⟩
  simpa only [Nat.cast_ofNat] using upper_bipartition H S E hB (by decide : 1 ≤ 4) hE hdeg

#print axioms extremal_lower_prime
#print axioms rate
#print axioms four_exceptions_rate
end Erdos713CubicNorm
