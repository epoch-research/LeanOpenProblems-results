import Submission.QuadraticSquarefreeSieve

/-!
A simultaneous square-divisor sieve in arbitrary fixed residue classes for
both parameters. This gives parameter counts only, not a Sidon root set.
-/
namespace Erdos1206.AffineQuadraticSquarefreeSieve
open Finset Filter QuadraticSquarefreeSieve
open scoped Classical Topology

lemma bad_prime_pairs_count_nat {p : ℕ} (hp : p.Prime)
    (a b c M v w N : ℕ) (hM : M.Coprime p)
    (ha : (a : ZMod p) ≠ 0)
    (hd : (b : ZMod p)^2-4*a*c ≠ 0) :
    (((range N) ×ˢ (range N)).filter (fun x =>
      p^2 ∣ quad a b c (M*x.1+v) (M*x.2+w))).card ≤
      2*N*(N/(p^2)+1)+(N/p+1)^2 := by
  haveI : NeZero p := ⟨hp.ne_zero⟩
  haveI : Fact p.Prime := ⟨hp⟩
  let S := ((range N) ×ˢ (range N)).filter (fun x =>
    p^2 ∣ quad a b c (M*x.1+v) (M*x.2+w))
  let T := S.filter (fun x => ¬ p ∣ M*x.1+v)
  let U := (range N).filter (fun i => ((M*i+v : ℕ) : ZMod p)=0)
  let V := (range N).filter (fun j => ((M*j+w : ℕ) : ZMod p)=0)
  have hsub : S ⊆ T ∪ (U ×ˢ V) := by
    intro x hx
    by_cases ht : p ∣ M*x.1+v
    · apply mem_union_right
      apply mem_product.mpr
      have hxN := mem_product.mp (mem_filter.mp hx).1
      refine ⟨mem_filter.mpr ⟨hxN.1,?_⟩,mem_filter.mpr ⟨hxN.2,?_⟩⟩
      · exact (CharP.cast_eq_zero_iff (ZMod p) p (M*x.1+v)).mpr ht
      · exact (CharP.cast_eq_zero_iff (ZMod p) p (M*x.2+w)).mpr
          (prime_divides_other_coordinate hp a b c _ _ ha ht (mem_filter.mp hx).2)
    · exact mem_union_left _ (mem_filter.mpr ⟨hx,ht⟩)
  have hT : T.card ≤ 2*N*(N/(p^2)+1) := by
    have hmap : ∀ x ∈ T, x.1 ∈ range N := by
      intro x hx
      exact (mem_product.mp (mem_filter.mp (mem_filter.mp hx).1).1).1
    have hh := card_le_mul_card_image_of_maps_to hmap (2*(N/(p^2)+1)) (fun i hi => ?_)
    · simpa only [card_range,mul_assoc,mul_comm,mul_left_comm] using hh
    · by_cases ht : p ∣ M*i+v
      · have he : (T.filter (fun x => x.1=i))=∅ := by
          apply eq_empty_iff_forall_notMem.mpr
          intro x hx
          have hx' := mem_filter.mp hx
          have hn := (mem_filter.mp hx'.1).2
          exact hn (hx'.2 ▸ ht)
        simp [he]
      · have ht0 : ((M*i+v : ℕ) : ZMod p) ≠ 0 := by
          exact fun h => ht ((CharP.cast_eq_zero_iff (ZMod p) p (M*i+v)).mp h)
        have hd' : ((b*(M*i+v) : ℕ) : ZMod p)^2 - 4*a*(c*(M*i+v)^2 : ℕ) ≠ 0 := by
          convert mul_ne_zero hd (pow_ne_zero 2 ht0) using 1 <;> push_cast <;> ring
        have hrow := affine_quadratic_count hp a (b*(M*i+v)) (c*(M*i+v)^2) M w N hM ha hd'
        have hc : (T.filter (fun x => x.1=i)).card ≤
            ((range N).filter (fun j => p^2 ∣ a*(M*j+w)^2+(b*(M*i+v))*(M*j+w)+c*(M*i+v)^2)).card := by
          apply card_le_card_of_injOn Prod.snd
          · intro x hx
            obtain ⟨hxT,hxi⟩ := mem_filter.mp hx
            obtain ⟨hxS,_⟩ := mem_filter.mp hxT
            obtain ⟨hxN,hxf⟩ := mem_filter.mp hxS
            change x.2 ∈ (range N).filter _
            apply mem_filter.mpr
            refine ⟨(mem_product.mp hxN).2,?_⟩
            simpa only [quad,hxi] using hxf
          · intro x hx y hy he
            apply Prod.ext
            · exact (mem_filter.mp hx).2.trans (mem_filter.mp hy).2.symm
            · exact he
        exact hc.trans hrow
  have hU : U.card ≤ N/p+1 := by
    simpa only [U,Nat.add_zero] using affine_residue_count M v N hM (0 : ZMod p)
  have hV : V.card ≤ N/p+1 := affine_residue_count M w N hM (0 : ZMod p)
  calc
    S.card ≤ (T ∪ (U ×ˢ V)).card := card_le_card hsub
    _ ≤ T.card + (U ×ˢ V).card := card_union_le _ _
    _ = T.card + U.card*V.card := by rw [card_product]
    _ ≤ 2*N*(N/(p^2)+1)+(N/p+1)^2 := by
      have hh := Nat.mul_le_mul hU hV
      nlinarith

lemma bad_prime_pairs_count {p : ℕ} (hp : p.Prime)
    (a b c M v w N : ℕ) (hM : M.Coprime p)
    (ha : (a : ZMod p) ≠ 0)
    (hd : (b : ZMod p)^2-4*a*c ≠ 0) :
    ((((range N) ×ˢ (range N)).filter (fun x =>
      p^2 ∣ quad a b c (M*x.1+v) (M*x.2+w))).card : ℝ) ≤
      3*(N:ℝ)^2/(p:ℝ)^2+4*N+1 := by
  have hc : ((((range N) ×ˢ (range N)).filter (fun x =>
      p^2 ∣ quad a b c (M*x.1+v) (M*x.2+w))).card : ℝ) ≤
      2*N*((N/(p^2) : ℕ)+1)+((N/p : ℕ)+1)^2 := by
    exact_mod_cast bad_prime_pairs_count_nat hp a b c M v w N hM ha hd
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp.one_lt.le
  have hn0 : (0 : ℝ) ≤ N := by positivity
  have hx : ((N/(p^2) : ℕ) : ℝ) ≤ (N:ℝ)/(p:ℝ)^2 := by
    calc
      ((N/p^2:ℕ):ℝ) ≤ (N:ℝ)/((p^2:ℕ):ℝ) := Nat.cast_div_le
      _ = _ := by rw [Nat.cast_pow]
  have hy : ((N/p : ℕ) : ℝ) ≤ (N:ℝ)/p := Nat.cast_div_le
  have hysq : (((N/p:ℕ):ℝ)+1)^2 ≤ ((N:ℝ)/p+1)^2 := by
    apply pow_le_pow_left₀ (by positivity)
    linarith
  have hxb := mul_le_mul_of_nonneg_left
    (show ((N/p^2:ℕ):ℝ)+1 ≤ (N:ℝ)/(p:ℝ)^2+1 by linarith)
    (show (0:ℝ) ≤ 2*N by positivity)
  have he : 2*(N:ℝ)*((N:ℝ)/(p:ℝ)^2+1)+((N:ℝ)/p+1)^2 =
      3*(N:ℝ)^2/(p:ℝ)^2+2*N+2*((N:ℝ)/p)+1 := by
    field_simp
    <;> ring
  have hyN : (N:ℝ)/p ≤ N := div_le_self hn0 hp1
  linarith

lemma nonsquarefree_pairs_count (a b c M v w N K L : ℕ) (hK : 0<K)
    (hsmall : ∀ p : ℕ, p.Prime → p≤K → ∀ i j : ℕ,
      ¬ p^2 ∣ quad a b c (M*i+v) (M*j+w))
    (hlarge : ∀ p : ℕ, p.Prime → K<p →
      M.Coprime p ∧ (a : ZMod p) ≠ 0 ∧ (b : ZMod p)^2-4*a*c ≠ 0)
    (hbound : ∀ x ∈ (range N) ×ˢ (range N),
      0 < quad a b c (M*x.1+v) (M*x.2+w) ∧
      quad a b c (M*x.1+v) (M*x.2+w) ≤ (L*N)^2) :
    ((((range N) ×ˢ (range N)).filter (fun x =>
      ¬ Squarefree (quad a b c (M*x.1+v) (M*x.2+w)))).card : ℝ) ≤
      3*(N:ℝ)^2/K+(4*N+1)*Nat.primeCounting (L*N) := by
  let P := (range (L*N+1)).filter (fun p => p.Prime ∧ K<p)
  let B := fun p => ((range N) ×ˢ (range N)).filter (fun x =>
    p^2 ∣ quad a b c (M*x.1+v) (M*x.2+w))
  let S := ((range N) ×ˢ (range N)).filter (fun x =>
    ¬ Squarefree (quad a b c (M*x.1+v) (M*x.2+w)))
  have hsub : S ⊆ P.biUnion B := by
    intro x hx
    obtain ⟨hxN,hxS⟩ := mem_filter.mp hx
    rw [Nat.squarefree_iff_prime_squarefree] at hxS
    push_neg at hxS
    obtain ⟨p,hp,hpd⟩ := hxS
    have hpd' : p^2 ∣ quad a b c (M*x.1+v) (M*x.2+w) := by simpa only [pow_two] using hpd
    have hKp : K<p := by
      by_contra hn
      exact hsmall p hp (by omega) x.1 x.2 hpd'
    have hpN : p≤L*N := by
      have hh := (Nat.le_of_dvd (hbound x hxN).1 hpd').trans (hbound x hxN).2
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

def goodPairs {r : ℕ} (a b c : Fin r → ℕ) (M v w N : ℕ) : Finset (ℕ × ℕ) :=
  ((range N) ×ˢ (range N)).filter (fun x =>
    ∀ i, Squarefree (quad (a i) (b i) (c i) (M*x.1+v) (M*x.2+w)))

/-- A simultaneous square-divisor sieve in a fixed arithmetic progression
of the two parameters. The density asserted is parameter density, not root density. -/
theorem goodPairs_eventually_large {r : ℕ} (hr : 0<r)
    (a b c : Fin r → ℕ) (M v w K L : ℕ) (hK : 12*r≤K)
    (hsmall : ∀ i p, p.Prime → p≤K → ∀ t u : ℕ,
      ¬p^2 ∣ quad (a i) (b i) (c i) (M*t+v) (M*u+w))
    (hlarge : ∀ i p, p.Prime → K<p →
      M.Coprime p ∧ (a i : ZMod p) ≠ 0 ∧ (b i : ZMod p)^2-4*(a i)*(c i) ≠ 0)
    (hbound : ∀ N : ℕ, 0<N → ∀ i x, x∈(range N) ×ˢ (range N) →
      0 < quad (a i) (b i) (c i) (M*x.1+v) (M*x.2+w) ∧
      quad (a i) (b i) (c i) (M*x.1+v) (M*x.2+w) ≤ (L*N)^2) :
    ∀ᶠ N : ℕ in atTop, (N:ℝ)^2/2 ≤ (goodPairs a b c M v w N).card := by
  have hK0 : 0<K := by omega
  have hrR : (0:ℝ)<r := by exact_mod_cast hr
  have hprime := primeCounting_mul_eventually_le L (show (0:ℝ)<1/(20*r) by positivity)
  filter_upwards [hprime,eventually_ge_atTop 1] with N hN hN1
  let B := fun i : Fin r => ((range N) ×ˢ (range N)).filter (fun x =>
    ¬Squarefree (quad (a i) (b i) (c i) (M*x.1+v) (M*x.2+w)))
  have hsub : (((range N) ×ˢ (range N)) \ goodPairs a b c M v w N) ⊆ univ.biUnion B := by
    intro x hx
    obtain ⟨hxN,hxG⟩ := mem_sdiff.mp hx
    have hh : ¬∀i, Squarefree (quad (a i) (b i) (c i) (M*x.1+v) (M*x.2+w)) := by
      intro hh
      exact hxG (mem_filter.mpr ⟨hxN,hh⟩)
    obtain ⟨i,hi⟩ := not_forall.mp hh
    exact mem_biUnion.mpr ⟨i,mem_univ _,mem_filter.mpr ⟨hxN,hi⟩⟩
  have hnat : (((range N) ×ˢ (range N)) \ goodPairs a b c M v w N).card ≤ ∑ i, (B i).card :=
    (card_le_card hsub).trans card_biUnion_le
  have hbc : ((((range N) ×ˢ (range N)) \ goodPairs a b c M v w N).card : ℝ) ≤
      (r:ℝ)*(3*(N:ℝ)^2/K+(4*N+1)*Nat.primeCounting (L*N)) := by
    have hh : (∑ i, ((B i).card : ℝ)) ≤
        ∑ i : Fin r, (3*(N:ℝ)^2/K+(4*N+1)*Nat.primeCounting (L*N)) := by
      apply sum_le_sum
      intro i hi
      exact nonsquarefree_pairs_count (a i) (b i) (c i) M v w N K L hK0
        (hsmall i) (hlarge i) (hbound N hN1 i)
    have hnatR : ((((range N) ×ˢ (range N)) \ goodPairs a b c M v w N).card : ℝ) ≤
        ∑ i, ((B i).card:ℝ) := by exact_mod_cast hnat
    exact hnatR.trans (by simpa only [sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul] using hh)
  have hcard := card_sdiff_add_card_eq_card
    (show goodPairs a b c M v w N ⊆ (range N) ×ˢ (range N) from filter_subset _ _)
  have hcardR : ((((range N) ×ˢ (range N)) \ goodPairs a b c M v w N).card : ℝ)+
      (goodPairs a b c M v w N).card=(N:ℝ)^2 := by
    simpa only [card_product,card_range,Nat.cast_add,Nat.cast_mul,pow_two] using
      congrArg (fun n : ℕ => (n:ℝ)) hcard
  have hKbound : (r:ℝ)*3/K ≤ 1/4 := by
    apply (div_le_iff₀ (show (0:ℝ)<K by exact_mod_cast hK0)).mpr
    have hh : 12*(r:ℝ)≤K := by exact_mod_cast hK
    linarith
  have hmain : (r:ℝ)*(3*(N:ℝ)^2/K) ≤ (N:ℝ)^2/4 := by
    have hh := mul_le_mul_of_nonneg_right hKbound (show (0:ℝ)≤(N:ℝ)^2 by positivity)
    convert hh using 1 <;> ring
  have hNR : (1:ℝ)≤N := by exact_mod_cast hN1
  have herror : (r:ℝ)*(4*N+1)*Nat.primeCounting (L*N) ≤ (N:ℝ)^2/4 := by
    have hh := mul_le_mul_of_nonneg_left hN (show (0:ℝ)≤(r:ℝ)*(4*N+1) by positivity)
    have hid : (r:ℝ)*(4*N+1)*(1/(20*r)*N) = (4*(N:ℝ)+1)*N/20 := by
      field_simp
    rw [hid] at hh
    nlinarith only [hh,hNR]
  nlinarith only [hbc,hcardR,hmain,herror]



lemma quad_modEq {m t u v w : ℕ} (a b c : ℕ)
    (ht : Nat.ModEq m t v) (hu : Nat.ModEq m u w) :
    Nat.ModEq m (quad a b c t u) (quad a b c v w) := by
  exact (((Nat.ModEq.refl a).mul (hu.pow 2)).add
    (((Nat.ModEq.refl b).mul ht).mul hu)).add
      ((Nat.ModEq.refl c).mul (ht.pow 2))

/-- Finitely many locally admissible pairs are combined by CRT. Adding one
full modulus ensures that the second parameter is positive. -/
theorem exists_small_prime_progression {r : ℕ} (a b c : Fin r → ℕ) (K : ℕ)
    (hlocal : ∀ p : ℕ, p.Prime → p ≤ K →
      ∃ t u : ℕ, ∀ i, ¬ p^2 ∣ quad (a i) (b i) (c i) t u) :
    ∃ v w : ℕ, 0 < w ∧ ∀ i p, p.Prime → p ≤ K → ∀ t u : ℕ,
      ¬ p^2 ∣ quad (a i) (b i) (c i)
        (sieveModulus K*t+v) (sieveModulus K*u+w) := by
  have hx : ∀ p : ℕ, ∃ t u : ℕ, p.Prime → p ≤ K →
      ∀ i, ¬ p^2 ∣ quad (a i) (b i) (c i) t u := by
    intro p
    by_cases hp : p.Prime ∧ p ≤ K
    · obtain ⟨t,u,h⟩ := hlocal p hp.1 hp.2
      exact ⟨t,u,fun _ _ => h⟩
    · exact ⟨0,0,fun h₁ h₂ => (hp ⟨h₁,h₂⟩).elim⟩
  choose T U hTU using hx
  let P := (range (K+1)).filter Nat.Prime
  have hP {p : ℕ} (hp : p ∈ P) : p.Prime ∧ p ≤ K := by
    simpa only [P,mem_filter,mem_range,Nat.lt_succ_iff,and_comm] using hp
  have hn : ∀ p ∈ P, p^2 ≠ 0 := fun p hp => pow_ne_zero _ (hP hp).1.ne_zero
  have hc : (P : Set ℕ).Pairwise (Function.onFun Nat.Coprime (fun p => p^2)) := by
    intro p hp q hq hpq
    exact Nat.coprime_pow_primes 2 2 (hP hp).1 (hP hq).1 hpq
  let v := Nat.chineseRemainderOfFinset T (fun p => p^2) P hn hc
  let w := Nat.chineseRemainderOfFinset U (fun p => p^2) P hn hc
  refine ⟨v,w+sieveModulus K,by have := sieveModulus_pos K; omega,?_⟩
  intro i p hp hpK t u hd
  have hpP : p ∈ P := mem_filter.mpr ⟨mem_range.mpr (by omega),hp⟩
  have hM : p^2 ∣ sieveModulus K :=
    pow_dvd_pow_of_dvd (Nat.dvd_factorial hp.pos hpK) 2
  have hM0 : Nat.ModEq (p^2) (sieveModulus K) 0 := Nat.modEq_zero_iff_dvd.mpr hM
  have ht : Nat.ModEq (p^2) (sieveModulus K*t+v) (T p) := by
    simpa only [zero_mul,zero_add] using (hM0.mul (Nat.ModEq.refl t)).add (v.property p hpP)
  have hu : Nat.ModEq (p^2) (sieveModulus K*u+(w+sieveModulus K)) (U p) := by
    simpa only [zero_mul,zero_add,add_zero] using
      (hM0.mul (Nat.ModEq.refl u)).add ((w.property p hpP).add hM0)
  exact hTU p hp hpK i ((quad_modEq (a i) (b i) (c i) ht hu).dvd_iff dvd_rfl |>.mp hd)

lemma quad_size_bound (a b c M v w N S : ℕ) (ha : 0 < a) (hw : 0 < w)
    (hS : a+b+c ≤ S) (hN : 0 < N) {x : ℕ × ℕ}
    (hx : x ∈ (range N) ×ˢ (range N)) :
    0 < quad a b c (M*x.1+v) (M*x.2+w) ∧
      quad a b c (M*x.1+v) (M*x.2+w) ≤ (S*(M+v+w+1)*N)^2 := by
  obtain ⟨hx₁,hx₂⟩ := mem_product.mp hx
  have hx1 : x.1 < N := mem_range.mp hx₁
  have hx2 : x.2 < N := mem_range.mp hx₂
  have hS0 : 0 < S := by omega
  have ht : M*x.1+v ≤ (M+v+w+1)*N := by nlinarith
  have hu : M*x.2+w ≤ (M+v+w+1)*N := by nlinarith
  constructor
  · dsimp [quad]
    positivity
  · have ht2 := Nat.pow_le_pow_left ht 2
    have hu2 := Nat.pow_le_pow_left hu 2
    have htu := Nat.mul_le_mul ht hu
    have hq : quad a b c (M*x.1+v) (M*x.2+w) ≤
        (a+b+c)*((M+v+w+1)*N)^2 := by
      dsimp [quad]
      have h₁ := Nat.mul_le_mul_left a hu2
      have h₂ := Nat.mul_le_mul_left b htu
      have h₃ := Nat.mul_le_mul_left c ht2
      nlinarith only [h₁,h₂,h₃]
    calc
      _ ≤ (a+b+c)*((M+v+w+1)*N)^2 := hq
      _ ≤ S*((M+v+w+1)*N)^2 := Nat.mul_le_mul_right _ hS
      _ ≤ S^2*((M+v+w+1)*N)^2 :=
        Nat.mul_le_mul_right _ (by nlinarith : S ≤ S^2)
      _ = _ := by ring

/-- Finite local admissibility replaces a pre-existing squarefree common
specialization. The conclusion is a positive proportion in ONE fixed
parameter progression, not positive density of the resulting root values. -/
theorem local_progression_sieve {r : ℕ} (hr : 0 < r)
    (a b c : Fin r → ℕ) (K S : ℕ) (hK : 12*r ≤ K)
    (ha : ∀ i, 0 < a i ∧ a i ≤ K)
    (hd : ∀ i, discriminant (a i) (b i) (c i) ≠ 0 ∧
      (discriminant (a i) (b i) (c i)).natAbs ≤ K)
    (hS : ∀ i, a i+b i+c i ≤ S)
    (hlocal : ∀ p : ℕ, p.Prime → p ≤ K →
      ∃ t u : ℕ, ∀ i, ¬ p^2 ∣ quad (a i) (b i) (c i) t u) :
    ∃ v w : ℕ, 0 < w ∧ ∀ᶠ N : ℕ in atTop,
      (N:ℝ)^2/2 ≤ (goodPairs a b c (sieveModulus K) v w N).card := by
  obtain ⟨v,w,hw,hsmall⟩ := exists_small_prime_progression a b c K hlocal
  refine ⟨v,w,hw,goodPairs_eventually_large hr a b c (sieveModulus K) v w K
    (S*(sieveModulus K+v+w+1)) hK hsmall ?_ ?_⟩
  · intro i p hp hpK
    exact large_prime_regular (a i) (b i) (c i) K (ha i).1 (ha i).2
      (hd i).1 (hd i).2 hp hpK
  · intro N hN i x hx
    exact quad_size_bound (a i) (b i) (c i) (sieveModulus K) v w N S
      (ha i).1 hw (hS i) hN hx


/-- A locally admissible finite collection of nondegenerate positive-leading
binary quadratics has simultaneously squarefree values on a positive
proportion of one fixed affine lattice. -/
theorem exists_squarefree_progression {r : ℕ} (hr : 0 < r)
    (a b c : Fin r → ℕ) (ha : ∀ i, 0 < a i)
    (hd : ∀ i, discriminant (a i) (b i) (c i) ≠ 0)
    (hlocal : ∀ p : ℕ, p.Prime →
      ∃ t u : ℕ, ∀ i, ¬ p^2 ∣ quad (a i) (b i) (c i) t u) :
    ∃ M v w : ℕ, 0 < M ∧ 0 < w ∧ ∀ᶠ N : ℕ in atTop,
      (N:ℝ)^2/2 ≤ (goodPairs a b c M v w N).card := by
  let K := 12*r+(∑ i, (a i+(discriminant (a i) (b i) (c i)).natAbs))+1
  let S := ∑ i, (a i+b i+c i)
  have hK : 12*r ≤ K := by dsimp [K]; omega
  have hb (i : Fin r) :
      a i+(discriminant (a i) (b i) (c i)).natAbs ≤ K := by
    have hh := single_le_sum (f := fun j : Fin r =>
      a j+(discriminant (a j) (b j) (c j)).natAbs)
      (fun _ _ => Nat.zero_le _) (mem_univ i)
    dsimp only at hh
    dsimp only [K]
    omega
  have haK (i : Fin r) : 0 < a i ∧ a i ≤ K := ⟨ha i,by have := hb i; omega⟩
  have hdK (i : Fin r) : discriminant (a i) (b i) (c i) ≠ 0 ∧
      (discriminant (a i) (b i) (c i)).natAbs ≤ K := ⟨hd i,by have := hb i; omega⟩
  have hS (i : Fin r) : a i+b i+c i ≤ S :=
    single_le_sum (f := fun j => a j+b j+c j) (fun _ _ => Nat.zero_le _) (mem_univ i)
  obtain ⟨v,w,hw,h⟩ := local_progression_sieve hr a b c K S hK haK hdK hS
    (fun p hp _ => hlocal p hp)
  exact ⟨sieveModulus K,v,w,sieveModulus_pos K,hw,h⟩

#print axioms goodPairs_eventually_large
#print axioms exists_small_prime_progression
#print axioms local_progression_sieve
#print axioms exists_squarefree_progression
end Erdos1206.AffineQuadraticSquarefreeSieve
