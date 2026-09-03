import FormalConjecturesUtil

/-! Local root bounds for a simultaneous square-divisor sieve. -/
namespace Erdos1206.QuadraticSquarefreeSieve
open Finset
open scoped Classical

lemma unit_of_reduction_ne_zero {p : ℕ} (hp : p.Prime)
    (z : ZMod (p^2))
    (hz : ZMod.castHom (dvd_pow_self p (by decide : 2 ≠ 0)) (ZMod p) z ≠ 0) :
    IsUnit z := by
  haveI : NeZero (p^2) := ⟨pow_ne_zero _ hp.ne_zero⟩
  have hn : ¬ p ∣ z.val := by
    intro h
    apply hz
    rw [← ZMod.natCast_zmod_val z, map_natCast]
    exact (CharP.cast_eq_zero_iff (ZMod p) p z.val).mpr h
  have hc : z.val.Coprime (p^2) :=
    ((hp.coprime_iff_not_dvd.mpr hn).symm).pow_right 2
  have hu := (ZMod.isUnit_iff_coprime z.val (p^2)).mpr hc
  simpa only [ZMod.natCast_zmod_val] using hu

lemma quadratic_roots_reduce_injective {p : ℕ} (hp : p.Prime)
    (a b c : ZMod (p^2))
    (hdisc : ZMod.castHom (dvd_pow_self p (by decide : 2 ≠ 0)) (ZMod p)
      (b^2-4*a*c) ≠ 0) :
    Set.InjOn (ZMod.castHom (dvd_pow_self p (by decide : 2 ≠ 0)) (ZMod p))
      {x | a*x^2+b*x+c=0} := by
  haveI : Fact p.Prime := ⟨hp⟩
  let r := ZMod.castHom (dvd_pow_self p (by decide : 2 ≠ 0)) (ZMod p)
  intro x hx y hy hxy
  have he : (x-y)*(a*(x+y)+b)=0 := by
    change a*x^2+b*x+c=0 at hx
    change a*y^2+b*y+c=0 at hy
    calc
      (x-y)*(a*(x+y)+b) = (a*x^2+b*x+c)-(a*y^2+b*y+c) := by ring
      _ = 0 := by rw [hx,hy,sub_self]
  have hu : IsUnit (a*(x+y)+b) := by
    apply unit_of_reduction_ne_zero hp
    intro hh
    have hrx : r a*(r x)^2+r b*r x+r c=0 := by
      simpa only [map_add,map_mul,map_pow,map_zero] using congrArg r hx
    have hdr : (r b)^2-4*r a*r c ≠ 0 := by
      simpa only [map_sub,map_mul,map_pow,map_ofNat] using hdisc
    change r x=r y at hxy
    have hder : 2*r a*r x+r b=0 := by
      change r (a*(x+y)+b)=0 at hh
      rw [map_add,map_mul,map_add,← hxy] at hh
      linear_combination hh
    apply hdr
    linear_combination (2*r a*r x+r b)*hder - 4*r a*hrx
  exact sub_eq_zero.mp (hu.mul_left_eq_zero.mp he)

lemma quadratic_roots_card {p : ℕ} [NeZero p] (hp : p.Prime)
    (a b c : ZMod (p^2))
    (ha : ZMod.castHom (dvd_pow_self p (by decide : 2 ≠ 0)) (ZMod p) a ≠ 0)
    (hdisc : ZMod.castHom (dvd_pow_self p (by decide : 2 ≠ 0)) (ZMod p)
      (b^2-4*a*c) ≠ 0) :
    ((univ : Finset (ZMod (p^2))).filter (fun x => a*x^2+b*x+c=0)).card ≤ 2 := by
  haveI : Fact p.Prime := ⟨hp⟩
  let r := ZMod.castHom (dvd_pow_self p (by decide : 2 ≠ 0)) (ZMod p)
  let f : Polynomial (ZMod p) :=
    Polynomial.C (r a)*Polynomial.X^2+Polynomial.C (r b)*Polynomial.X+Polynomial.C (r c)
  have hdeg : f.natDegree=2 := Polynomial.natDegree_quadratic ha
  have hf : f ≠ 0 := by
    intro hz
    rw [hz,Polynomial.natDegree_zero] at hdeg
    omega
  have hcard := card_le_card_of_injOn (s := univ.filter (fun x => a*x^2+b*x+c=0))
    (t := f.roots.toFinset) r
    (fun x hx => ?_)
    (fun x hx y hy he => quadratic_roots_reduce_injective hp a b c hdisc
      (mem_filter.mp hx).2 (mem_filter.mp hy).2 he)
  · exact hcard.trans ((Multiset.toFinset_card_le _).trans ((Polynomial.card_roots' f).trans_eq hdeg))
  · change r x ∈ f.roots.toFinset
    rw [Multiset.mem_toFinset,Polynomial.mem_roots hf]
    have he := congrArg r (mem_filter.mp hx).2
    simpa [f,Polynomial.IsRoot, map_add,map_mul,map_pow] using he

lemma affine_residue_count {m : ℕ} [NeZero m] (M v N : ℕ)
    (hM : M.Coprime m) (z : ZMod m) :
    ((range N).filter (fun j => (M*j+v : ℕ) = z)).card ≤ N/m+1 := by
  let S := (range N).filter (fun j => (M*j+v : ℕ) = z)
  by_cases hs : S.Nonempty
  · obtain ⟨j₀,hj₀⟩ := hs
    have hsub : S ⊆ (range N).filter (fun j => Nat.ModEq m j j₀) := by
      intro j hj
      have h₀ := (mem_filter.mp hj₀).2
      have h₁ := (mem_filter.mp hj).2
      have hcast : ((M*j+v : ℕ) : ZMod m) = ((M*j₀+v : ℕ) : ZMod m) := h₁.trans h₀.symm
      have hmod := (ZMod.natCast_eq_natCast_iff _ _ _).mp hcast
      have he := (Nat.ModEq.refl v).add_right_cancel hmod
      exact mem_filter.mpr ⟨(mem_filter.mp hj).1,
        Nat.ModEq.cancel_left_of_coprime hM.symm he⟩
    have hc := card_le_card hsub
    rw [← Nat.count_eq_card_filter_range (fun j => Nat.ModEq m j j₀) N,
      Nat.count_modEq_card _ (Nat.pos_of_ne_zero (NeZero.ne m))] at hc
    change S.card ≤ _
    split_ifs at hc <;> omega
  · have he : S=∅ := not_nonempty_iff_eq_empty.mp hs
    change S.card ≤ _
    simp [he]

lemma affine_quadratic_count {p : ℕ} (hp : p.Prime)
    (a b c M v N : ℕ) (hM : M.Coprime p)
    (ha : (a : ZMod p) ≠ 0)
    (hd : (b : ZMod p)^2-4*a*c ≠ 0) :
    ((range N).filter (fun j => p^2 ∣ a*(M*j+v)^2+b*(M*j+v)+c)).card ≤
      2*(N/(p^2)+1) := by
  haveI : NeZero p := ⟨hp.ne_zero⟩
  haveI : Fact p.Prime := ⟨hp⟩
  let R := (univ : Finset (ZMod (p^2))).filter
    (fun x => (a : ZMod (p^2))*x^2+b*x+c=0)
  have hR : R.card ≤ 2 := quadratic_roots_card hp a b c (by simpa only [map_natCast] using ha)
    (by simpa only [map_sub,map_mul,map_pow,map_ofNat,map_natCast] using hd)
  let S := (range N).filter (fun j => p^2 ∣ a*(M*j+v)^2+b*(M*j+v)+c)
  have hf : ∀ j ∈ S, ((M*j+v : ℕ) : ZMod (p^2)) ∈ R := by
    intro j hj
    simp only [R,mem_filter,mem_univ,true_and]
    have hh := (CharP.cast_eq_zero_iff (ZMod (p^2)) (p^2)
      (a*(M*j+v)^2+b*(M*j+v)+c)).mpr (mem_filter.mp hj).2
    simpa only [Nat.cast_add,Nat.cast_mul,Nat.cast_pow] using hh
  have hc := card_le_mul_card_image_of_maps_to hf (N/(p^2)+1) (fun z hz => ?_)
  · exact hc.trans ((Nat.mul_le_mul_left _ hR).trans_eq (mul_comm _ _))
  · apply le_trans (card_le_card ?_) (affine_residue_count M v N (hM.pow_right 2) z)
    intro j hj
    simp only [mem_filter] at hj ⊢
    exact ⟨(mem_filter.mp hj.1).1,hj.2⟩

def quad (a b c t u : ℕ) : ℕ := a*u^2+b*t*u+c*t^2

lemma prime_divides_other_coordinate {p : ℕ} (hp : p.Prime)
    (a b c t u : ℕ) (ha : (a : ZMod p) ≠ 0)
    (ht : p ∣ t) (hf : p^2 ∣ quad a b c t u) : p ∣ u := by
  haveI : Fact p.Prime := ⟨hp⟩
  have ht0 : (t : ZMod p)=0 := (CharP.cast_eq_zero_iff (ZMod p) p t).mpr ht
  have hfp : p ∣ quad a b c t u := (dvd_pow_self p (by decide : 2 ≠ 0)).trans hf
  have hq := (CharP.cast_eq_zero_iff (ZMod p) p (quad a b c t u)).mpr hfp
  have hu : (u : ZMod p)=0 := by
    simp only [quad,Nat.cast_add,Nat.cast_mul,Nat.cast_pow,ht0,mul_zero,zero_mul,
      zero_pow (by decide : 2 ≠ 0),add_zero] at hq
    exact (pow_eq_zero_iff (by decide : 2 ≠ 0)).mp ((mul_eq_zero.mp hq).resolve_left ha)
  exact (CharP.cast_eq_zero_iff (ZMod p) p u).mp hu

lemma bad_prime_pairs_count_nat {p : ℕ} (hp : p.Prime)
    (a b c M N : ℕ) (hM : M.Coprime p)
    (ha : (a : ZMod p) ≠ 0)
    (hd : (b : ZMod p)^2-4*a*c ≠ 0) :
    (((range N) ×ˢ (range N)).filter (fun x =>
      p^2 ∣ quad a b c (M*x.1) (M*x.2+1))).card ≤
      2*N*(N/(p^2)+1)+(N/p+1)^2 := by
  haveI : NeZero p := ⟨hp.ne_zero⟩
  haveI : Fact p.Prime := ⟨hp⟩
  let S := ((range N) ×ˢ (range N)).filter (fun x =>
    p^2 ∣ quad a b c (M*x.1) (M*x.2+1))
  let T := S.filter (fun x => ¬ p ∣ M*x.1)
  let U := (range N).filter (fun i => ((M*i : ℕ) : ZMod p)=0)
  let V := (range N).filter (fun j => ((M*j+1 : ℕ) : ZMod p)=0)
  have hsub : S ⊆ T ∪ (U ×ˢ V) := by
    intro x hx
    by_cases ht : p ∣ M*x.1
    · apply mem_union_right
      apply mem_product.mpr
      have hxN := mem_product.mp (mem_filter.mp hx).1
      refine ⟨mem_filter.mpr ⟨hxN.1,?_⟩,mem_filter.mpr ⟨hxN.2,?_⟩⟩
      · exact (CharP.cast_eq_zero_iff (ZMod p) p (M*x.1)).mpr ht
      · exact (CharP.cast_eq_zero_iff (ZMod p) p (M*x.2+1)).mpr
          (prime_divides_other_coordinate hp a b c _ _ ha ht (mem_filter.mp hx).2)
    · exact mem_union_left _ (mem_filter.mpr ⟨hx,ht⟩)
  have hT : T.card ≤ 2*N*(N/(p^2)+1) := by
    have hmap : ∀ x ∈ T, x.1 ∈ range N := by
      intro x hx
      exact (mem_product.mp (mem_filter.mp (mem_filter.mp hx).1).1).1
    have hh := card_le_mul_card_image_of_maps_to hmap (2*(N/(p^2)+1)) (fun i hi => ?_)
    · simpa only [card_range,mul_assoc,mul_comm,mul_left_comm] using hh
    · by_cases ht : p ∣ M*i
      · have he : (T.filter (fun x => x.1=i))=∅ := by
          apply eq_empty_iff_forall_notMem.mpr
          intro x hx
          have hx' := mem_filter.mp hx
          have hn := (mem_filter.mp hx'.1).2
          exact hn (hx'.2 ▸ ht)
        simp [he]
      · have ht0 : ((M*i : ℕ) : ZMod p) ≠ 0 := by
          exact fun h => ht ((CharP.cast_eq_zero_iff (ZMod p) p (M*i)).mp h)
        have hd' : ((b*(M*i) : ℕ) : ZMod p)^2 - 4*a*(c*(M*i)^2 : ℕ) ≠ 0 := by
          convert mul_ne_zero hd (pow_ne_zero 2 ht0) using 1 <;> push_cast <;> ring
        have hrow := affine_quadratic_count hp a (b*(M*i)) (c*(M*i)^2) M 1 N hM ha hd'
        have hc : (T.filter (fun x => x.1=i)).card ≤
            ((range N).filter (fun j => p^2 ∣ a*(M*j+1)^2+(b*(M*i))*(M*j+1)+c*(M*i)^2)).card := by
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
    simpa only [U,Nat.add_zero] using affine_residue_count M 0 N hM (0 : ZMod p)
  have hV : V.card ≤ N/p+1 := affine_residue_count M 1 N hM (0 : ZMod p)
  calc
    S.card ≤ (T ∪ (U ×ˢ V)).card := card_le_card hsub
    _ ≤ T.card + (U ×ˢ V).card := card_union_le _ _
    _ = T.card + U.card*V.card := by rw [card_product]
    _ ≤ 2*N*(N/(p^2)+1)+(N/p+1)^2 := by
      have hh := Nat.mul_le_mul hU hV
      nlinarith

lemma bad_prime_pairs_count {p : ℕ} (hp : p.Prime)
    (a b c M N : ℕ) (hM : M.Coprime p)
    (ha : (a : ZMod p) ≠ 0)
    (hd : (b : ZMod p)^2-4*a*c ≠ 0) :
    ((((range N) ×ˢ (range N)).filter (fun x =>
      p^2 ∣ quad a b c (M*x.1) (M*x.2+1))).card : ℝ) ≤
      3*(N:ℝ)^2/(p:ℝ)^2+4*N+1 := by
  have hc : ((((range N) ×ˢ (range N)).filter (fun x =>
      p^2 ∣ quad a b c (M*x.1) (M*x.2+1))).card : ℝ) ≤
      2*N*((N/(p^2) : ℕ)+1)+((N/p : ℕ)+1)^2 := by
    exact_mod_cast bad_prime_pairs_count_nat hp a b c M N hM ha hd
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

lemma prime_reciprocal_square_tail (K T : ℕ) (hK : 0 < K) :
    (∑ p ∈ (range (T+1)).filter (fun p => p.Prime ∧ K<p), (1:ℝ)/(p:ℝ)^2) ≤ 1/K := by
  have hsub : (range (T+1)).filter (fun p => p.Prime ∧ K<p) ⊆ Ioc K (max K T) := by
    intro p hp
    simp only [mem_filter,mem_range,mem_Ioc] at hp ⊢
    exact ⟨hp.2.2,(Nat.le_of_lt_succ hp.1).trans (le_max_right _ _)⟩
  have hh := sum_le_sum_of_subset_of_nonneg hsub
    (fun p hp hnot => by positivity : ∀ p ∈ Ioc K (max K T),
      p ∉ (range (T+1)).filter (fun p => p.Prime ∧ K<p) → 0 ≤ (1:ℝ)/(p:ℝ)^2)
  have ht := sum_Ioc_inv_sq_le_sub (α := ℝ) hK.ne' (le_max_left K T)
  simp only [one_div] at hh ⊢
  exact hh.trans (ht.trans (sub_le_self _ (by positivity)))

open Filter
open scoped Topology

lemma primeCounting_mul_eventually_le (L : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, (Nat.primeCounting (L*N) : ℝ) ≤ ε*N := by
  by_cases hL : L=0
  · subst L
    exact Filter.Eventually.of_forall (fun N => by simp; positivity)
  have hL0 : (0:ℝ)<L := by exact_mod_cast Nat.pos_of_ne_zero hL
  have ht : Tendsto (fun N : ℕ => (L:ℝ)*N) atTop atTop :=
    tendsto_natCast_atTop_atTop.const_mul_atTop hL0
  have hlog := (Real.tendsto_log_atTop.comp ht).eventually
    (eventually_ge_atTop (max 1 ((Real.log 4+1)*(L:ℝ)/ε)))
  have hcount := ht.eventually (Chebyshev.eventually_primeCounting_le (by norm_num : (0:ℝ)<1))
  filter_upwards [hlog,hcount,eventually_ge_atTop 1] with N hN hc hN1
  have hl0 : 0 < Real.log ((L:ℝ)*N) := lt_of_lt_of_le (by norm_num) ((le_max_left _ _).trans hN)
  have hbound : (Real.log 4+1)*(L:ℝ) ≤ ε*Real.log ((L:ℝ)*N) := by
    have := (le_max_right _ _).trans hN
    exact (div_le_iff₀ hε).mp this |>.trans_eq (mul_comm _ _)
  have hf : ⌊(L:ℝ)*N⌋₊=L*N := by rw [← Nat.cast_mul,Nat.floor_natCast]
  rw [hf] at hc
  calc
    (Nat.primeCounting (L*N) : ℝ) ≤ (Real.log 4+1)*((L:ℝ)*N)/Real.log ((L:ℝ)*N) := hc
    _ ≤ ε*N := by
      apply (div_le_iff₀ hl0).mpr
      have := mul_le_mul_of_nonneg_right hbound (show (0:ℝ)≤N by positivity)
      nlinarith only [this]

lemma nonsquarefree_pairs_count (a b c M N K L : ℕ) (hK : 0<K)
    (hsmall : ∀ p : ℕ, p.Prime → p≤K → ∀ i j : ℕ,
      ¬ p^2 ∣ quad a b c (M*i) (M*j+1))
    (hlarge : ∀ p : ℕ, p.Prime → K<p →
      M.Coprime p ∧ (a : ZMod p) ≠ 0 ∧ (b : ZMod p)^2-4*a*c ≠ 0)
    (hbound : ∀ x ∈ (range N) ×ˢ (range N),
      0 < quad a b c (M*x.1) (M*x.2+1) ∧
      quad a b c (M*x.1) (M*x.2+1) ≤ (L*N)^2) :
    ((((range N) ×ˢ (range N)).filter (fun x =>
      ¬ Squarefree (quad a b c (M*x.1) (M*x.2+1)))).card : ℝ) ≤
      3*(N:ℝ)^2/K+(4*N+1)*Nat.primeCounting (L*N) := by
  let P := (range (L*N+1)).filter (fun p => p.Prime ∧ K<p)
  let B := fun p => ((range N) ×ˢ (range N)).filter (fun x =>
    p^2 ∣ quad a b c (M*x.1) (M*x.2+1))
  let S := ((range N) ×ˢ (range N)).filter (fun x =>
    ¬ Squarefree (quad a b c (M*x.1) (M*x.2+1)))
  have hsub : S ⊆ P.biUnion B := by
    intro x hx
    obtain ⟨hxN,hxS⟩ := mem_filter.mp hx
    rw [Nat.squarefree_iff_prime_squarefree] at hxS
    push_neg at hxS
    obtain ⟨p,hp,hpd⟩ := hxS
    have hpd' : p^2 ∣ quad a b c (M*x.1) (M*x.2+1) := by simpa only [pow_two] using hpd
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
    exact bad_prime_pairs_count hh.1 a b c M N hM ha hd
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

def goodPairs {r : ℕ} (a b c : Fin r → ℕ) (M N : ℕ) : Finset (ℕ × ℕ) :=
  ((range N) ×ˢ (range N)).filter (fun x =>
    ∀ i, Squarefree (quad (a i) (b i) (c i) (M*x.1) (M*x.2+1)))

/-- A simultaneous square-divisor sieve in a fixed arithmetic progression
of the two parameters. The density asserted is parameter density, not root density. -/
theorem goodPairs_eventually_large {r : ℕ} (hr : 0<r)
    (a b c : Fin r → ℕ) (M K L : ℕ) (hK : 12*r≤K)
    (hsmall : ∀ i p, p.Prime → p≤K → ∀ t u : ℕ,
      ¬p^2 ∣ quad (a i) (b i) (c i) (M*t) (M*u+1))
    (hlarge : ∀ i p, p.Prime → K<p →
      M.Coprime p ∧ (a i : ZMod p) ≠ 0 ∧ (b i : ZMod p)^2-4*(a i)*(c i) ≠ 0)
    (hbound : ∀ N : ℕ, 0<N → ∀ i x, x∈(range N) ×ˢ (range N) →
      0 < quad (a i) (b i) (c i) (M*x.1) (M*x.2+1) ∧
      quad (a i) (b i) (c i) (M*x.1) (M*x.2+1) ≤ (L*N)^2) :
    ∀ᶠ N : ℕ in atTop, (N:ℝ)^2/2 ≤ (goodPairs a b c M N).card := by
  have hK0 : 0<K := by omega
  have hrR : (0:ℝ)<r := by exact_mod_cast hr
  have hprime := primeCounting_mul_eventually_le L (show (0:ℝ)<1/(20*r) by positivity)
  filter_upwards [hprime,eventually_ge_atTop 1] with N hN hN1
  let B := fun i : Fin r => ((range N) ×ˢ (range N)).filter (fun x =>
    ¬Squarefree (quad (a i) (b i) (c i) (M*x.1) (M*x.2+1)))
  have hsub : (((range N) ×ˢ (range N)) \ goodPairs a b c M N) ⊆ univ.biUnion B := by
    intro x hx
    obtain ⟨hxN,hxG⟩ := mem_sdiff.mp hx
    have hh : ¬∀i, Squarefree (quad (a i) (b i) (c i) (M*x.1) (M*x.2+1)) := by
      intro hh
      exact hxG (mem_filter.mpr ⟨hxN,hh⟩)
    obtain ⟨i,hi⟩ := not_forall.mp hh
    exact mem_biUnion.mpr ⟨i,mem_univ _,mem_filter.mpr ⟨hxN,hi⟩⟩
  have hnat : (((range N) ×ˢ (range N)) \ goodPairs a b c M N).card ≤ ∑ i, (B i).card :=
    (card_le_card hsub).trans card_biUnion_le
  have hbc : ((((range N) ×ˢ (range N)) \ goodPairs a b c M N).card : ℝ) ≤
      (r:ℝ)*(3*(N:ℝ)^2/K+(4*N+1)*Nat.primeCounting (L*N)) := by
    have hh : (∑ i, ((B i).card : ℝ)) ≤
        ∑ i : Fin r, (3*(N:ℝ)^2/K+(4*N+1)*Nat.primeCounting (L*N)) := by
      apply sum_le_sum
      intro i hi
      exact nonsquarefree_pairs_count (a i) (b i) (c i) M N K L hK0
        (hsmall i) (hlarge i) (hbound N hN1 i)
    have hnatR : ((((range N) ×ˢ (range N)) \ goodPairs a b c M N).card : ℝ) ≤
        ∑ i, ((B i).card:ℝ) := by exact_mod_cast hnat
    exact hnatR.trans (by simpa only [sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul] using hh)
  have hcard := card_sdiff_add_card_eq_card
    (show goodPairs a b c M N ⊆ (range N) ×ˢ (range N) from filter_subset _ _)
  have hcardR : ((((range N) ×ˢ (range N)) \ goodPairs a b c M N).card : ℝ)+
      (goodPairs a b c M N).card=(N:ℝ)^2 := by
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
      <;> ring
    rw [hid] at hh
    nlinarith only [hh,hNR]
  nlinarith only [hbc,hcardR,hmain,herror]

def discriminant (a b c : ℕ) : ℤ := (b:ℤ)^2-4*a*c

def sieveModulus (K : ℕ) : ℕ := K.factorial^2

lemma sieveModulus_pos (K : ℕ) : 0<sieveModulus K := pow_pos (Nat.factorial_pos K) 2

lemma small_prime_avoided (a b c K : ℕ) (ha : Squarefree a)
    {p : ℕ} (hp : p.Prime) (hpK : p≤K) (t u : ℕ) :
    ¬p^2 ∣ quad a b c (sieveModulus K*t) (sieveModulus K*u+1) := by
  intro hh
  have hm : p^2 ∣ sieveModulus K := pow_dvd_pow_of_dvd (Nat.dvd_factorial hp.pos hpK) 2
  have hm0 := (CharP.cast_eq_zero_iff (ZMod (p^2)) (p^2) (sieveModulus K)).mpr hm
  have hq := (CharP.cast_eq_zero_iff (ZMod (p^2)) (p^2) _).mpr hh
  have ha0 : (a : ZMod (p^2))=0 := by
    simpa only [quad,Nat.cast_add,Nat.cast_mul,Nat.cast_pow,Nat.cast_one,hm0,
      zero_mul,zero_add,one_pow,mul_one,mul_zero,zero_pow (by decide : 2 ≠ 0),add_zero] using hq
  have hpa := (CharP.cast_eq_zero_iff (ZMod (p^2)) (p^2) a).mp ha0
  exact (Nat.squarefree_iff_prime_squarefree.mp ha p hp) (by simpa only [pow_two] using hpa)

lemma large_prime_regular (a b c K : ℕ) (ha : 0<a) (haK : a≤K)
    (hd : discriminant a b c ≠ 0) (hdK : (discriminant a b c).natAbs≤K)
    {p : ℕ} (hp : p.Prime) (hKp : K<p) :
    (sieveModulus K).Coprime p ∧ (a : ZMod p) ≠ 0 ∧
      (b : ZMod p)^2-4*a*c ≠ 0 := by
  refine ⟨?_,?_,?_⟩
  · apply (hp.coprime_iff_not_dvd.mpr ?_).symm
    intro hh
    have hh' := hp.dvd_of_dvd_pow hh
    have hpK := hp.dvd_factorial.mp hh'
    omega
  · intro hh
    have hpa := (CharP.cast_eq_zero_iff (ZMod p) p a).mp hh
    have := Nat.le_of_dvd ha hpa
    omega
  · intro hh
    have he : ((discriminant a b c : ℤ) : ZMod p)=0 := by
      simpa only [discriminant,Int.cast_sub,Int.cast_mul,Int.cast_pow,Int.cast_ofNat,
        Int.cast_natCast] using hh
    have hpabs := Int.natCast_dvd.mp ((ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp he)
    have := Nat.le_of_dvd (Int.natAbs_pos.mpr hd) hpabs
    omega

lemma quad_size_bound (a b c M N S : ℕ) (ha : 0<a) (hS : a+b+c≤S)
    (hN : 0<N) {x : ℕ × ℕ} (hx : x∈(range N) ×ˢ (range N)) :
    0<quad a b c (M*x.1) (M*x.2+1) ∧
      quad a b c (M*x.1) (M*x.2+1) ≤ (S*(M+1)*N)^2 := by
  obtain ⟨hx₁,hx₂⟩ := mem_product.mp hx
  have hx1 : x.1<N := mem_range.mp hx₁
  have hx2 : x.2<N := mem_range.mp hx₂
  have hS0 : 0<S := by omega
  have ht : M*x.1 ≤ (M+1)*N := by nlinarith
  have hu : M*x.2+1 ≤ (M+1)*N := by nlinarith
  constructor
  · dsimp [quad]
    positivity
  · have ht2 := Nat.pow_le_pow_left ht 2
    have hu2 := Nat.pow_le_pow_left hu 2
    have htu := Nat.mul_le_mul ht hu
    have hq : quad a b c (M*x.1) (M*x.2+1) ≤ (a+b+c)*((M+1)*N)^2 := by
      dsimp [quad]
      have h₁ := Nat.mul_le_mul_left a hu2
      have h₂ := Nat.mul_le_mul_left b htu
      have h₃ := Nat.mul_le_mul_left c ht2
      nlinarith only [h₁,h₂,h₃]
    calc
      _ ≤ (a+b+c)*((M+1)*N)^2 := hq
      _ ≤ S*((M+1)*N)^2 := Nat.mul_le_mul_right _ hS
      _ ≤ S^2*((M+1)*N)^2 := Nat.mul_le_mul_right _ (by nlinarith : S≤S^2)
      _ = _ := by ring

/-- A squarefree specialization at (0,1) and nonzero discriminants suffice
for a positive proportion of simultaneously squarefree parameter pairs. -/
theorem factorial_progression_sieve {r : ℕ} (hr : 0<r)
    (a b c : Fin r → ℕ) (K S : ℕ) (hK : 12*r≤K)
    (ha : ∀ i, 0<a i ∧ a i≤K ∧ Squarefree (a i))
    (hd : ∀ i, discriminant (a i) (b i) (c i) ≠ 0 ∧
      (discriminant (a i) (b i) (c i)).natAbs≤K)
    (hS : ∀ i, a i+b i+c i≤S) :
    ∀ᶠ N : ℕ in atTop, (N:ℝ)^2/2 ≤ (goodPairs a b c (sieveModulus K) N).card := by
  apply goodPairs_eventually_large hr a b c (sieveModulus K) K (S*(sieveModulus K+1)) hK
  · intro i p hp hpK t u
    exact small_prime_avoided (a i) (b i) (c i) K (ha i).2.2 hp hpK t u
  · intro i p hp hpK
    exact large_prime_regular (a i) (b i) (c i) K (ha i).1 (ha i).2.1
      (hd i).1 (hd i).2 hp hpK
  · intro N hN i x hx
    exact quad_size_bound (a i) (b i) (c i) (sieveModulus K) N S (ha i).1 (hS i) hN hx

#print axioms factorial_progression_sieve
end Erdos1206.QuadraticSquarefreeSieve
