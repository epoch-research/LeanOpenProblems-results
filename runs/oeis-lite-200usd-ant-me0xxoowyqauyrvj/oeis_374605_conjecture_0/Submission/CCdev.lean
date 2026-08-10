import FormalConjectures.Util.ProblemImports
open Finset Nat

lemma pmul_congr (p : ℕ) [NeZero (p^2)] (a b : ℕ) (h : a % p = b % p) :
    (p : ZMod (p^2)) * (a : ZMod (p^2)) = (p : ZMod (p^2)) * (b : ZMod (p^2)) := by
  have hp20 : ((p:ZMod (p^2)))*p = 0 := by
    have e : ((p:ZMod (p^2)))*p = ((p^2:ℕ):ZMod (p^2)) := by push_cast; ring
    rw [e, ZMod.natCast_self]
  have ha : (a:ZMod (p^2)) = (p:ZMod (p^2)) * ((a/p:ℕ):ZMod (p^2)) + ((a%p:ℕ):ZMod (p^2)) := by
    conv_lhs => rw [← Nat.div_add_mod a p]
    push_cast; ring
  have hb : (b:ZMod (p^2)) = (p:ZMod (p^2)) * ((b/p:ℕ):ZMod (p^2)) + ((b%p:ℕ):ZMod (p^2)) := by
    conv_lhs => rw [← Nat.div_add_mod b p]
    push_cast; ring
  rw [ha, hb, h]
  linear_combination (((a/p:ℕ):ZMod (p^2)) - ((b/p:ℕ):ZMod (p^2))) * hp20

-- ∏_{i=p+1}^{2p-2} i ≡ (p-2)! mod p
lemma block_mod (p : ℕ) (hp : Nat.Prime p) (hp5 : 5 ≤ p) :
    (∏ i ∈ Finset.Icc (p+1) (2*p-2), i) % p = (Nat.factorial (p-2)) % p := by
  haveI : Fact (Nat.Prime p) := ⟨hp⟩
  rw [← Nat.ModEq, ← ZMod.natCast_eq_natCast_iff]
  push_cast [Nat.cast_prod]
  have hmap : Finset.Icc (p+1) (2*p-2) = Finset.map (addLeftEmbedding p) (Finset.Icc 1 (p-2)) := by
    rw [Finset.map_add_left_Icc]; congr 1 <;> omega
  rw [hmap, Finset.prod_map]
  have e1 : ∏ i ∈ Finset.Icc 1 (p-2), ((addLeftEmbedding p i : ℕ) : ZMod p)
      = ∏ i ∈ Finset.Icc 1 (p-2), ((i:ℕ):ZMod p) := by
    apply Finset.prod_congr rfl; intro i _
    simp [addLeftEmbedding_apply]
  rw [e1, ← Nat.cast_prod]
  congr 1
  rw [show Finset.Icc 1 (p-2) = Finset.Ico 1 ((p-2)+1) from by
    ext x; simp only [Finset.mem_Icc, Finset.mem_Ico]; omega]
  exact Finset.prod_Ico_id_eq_factorial (p-2)

lemma C2pm2 (p : ℕ) (hp : Nat.Prime p) (hp5 : 5 ≤ p) :
    ((Nat.choose (2*p-2) (p-1) : ℕ) : ZMod (p^2)) = -(p : ZMod (p^2)) := by
  haveI : NeZero (p^2) := ⟨pow_ne_zero 2 hp.pos.ne'⟩
  have hp20 : ((p:ZMod (p^2)))^2 = 0 := by rw [← Nat.cast_pow, ZMod.natCast_self]
  have hch : Nat.choose (2*p-2) (p-1) * (p-1)! * (p-1)! = (2*p-2)! := by
    have h := Nat.choose_mul_factorial_mul_factorial (show p-1 ≤ 2*p-2 from by omega)
    rwa [show 2*p-2-(p-1) = p-1 from by omega] at h
  -- factorial split
  have hfact : (2*p-2)! = (p-1)! * (p * ∏ i ∈ Finset.Icc (p+1) (2*p-2), i) := by
    have d1 : (2*p-2)! = ∏ i ∈ Finset.Icc 1 (2*p-2), i := by
      rw [show Finset.Icc 1 (2*p-2) = Finset.Ico 1 ((2*p-2)+1) from by
        ext x; simp only [Finset.mem_Icc, Finset.mem_Ico]; omega, Finset.prod_Ico_id_eq_factorial]
    have d2 : (p-1)! = ∏ i ∈ Finset.Icc 1 (p-1), i := by
      rw [show Finset.Icc 1 (p-1) = Finset.Ico 1 ((p-1)+1) from by
        ext x; simp only [Finset.mem_Icc, Finset.mem_Ico]; omega]
      exact (Finset.prod_Ico_id_eq_factorial (p-1)).symm
    have hu1 : Finset.Icc 1 (2*p-2) = Finset.Icc 1 (p-1) ∪ Finset.Icc p (2*p-2) := by
      ext x; simp only [Finset.mem_union, Finset.mem_Icc]; omega
    have hd1 : Disjoint (Finset.Icc 1 (p-1)) (Finset.Icc p (2*p-2)) := by
      rw [Finset.disjoint_left]; intro x hx hy
      simp only [Finset.mem_Icc] at hx hy; omega
    have hu2 : Finset.Icc p (2*p-2) = insert p (Finset.Icc (p+1) (2*p-2)) := by
      ext x; simp only [Finset.mem_insert, Finset.mem_Icc]; omega
    have hnm : p ∉ Finset.Icc (p+1) (2*p-2) := by simp only [Finset.mem_Icc]; omega
    rw [d1, hu1, Finset.prod_union hd1, hu2, Finset.prod_insert hnm, ← d2]
  -- cast
  have hcZ : (Nat.choose (2*p-2) (p-1) : ZMod (p^2)) * ((p-1)! : ZMod (p^2)) * ((p-1)! : ZMod (p^2))
      = (p:ZMod (p^2)) * ((p-1)! : ZMod (p^2)) * ((p-2)! : ZMod (p^2)) := by
    have e := congrArg (fun z : ℕ => (z : ZMod (p^2))) hch
    simp only [Nat.cast_mul] at e
    rw [e, hfact]
    push_cast
    have hpc := pmul_congr p (∏ i ∈ Finset.Icc (p+1) (2*p-2), i) (Nat.factorial (p-2))
      (block_mod p hp hp5)
    push_cast at hpc
    rw [hpc]; ring
  -- (p-1)! = (p-1)*(p-2)!
  have hfac21 : ((p-1)! : ZMod (p^2)) = ((p:ZMod (p^2))-1) * ((p-2)! : ZMod (p^2)) := by
    have : (p-1)! = (p-1) * (p-2)! := by
      rw [show p-1 = (p-2)+1 from by omega, Nat.factorial_succ, show (p-2)+1 = p-1 from by omega]
    rw [this]; push_cast [show (1:ℕ) ≤ p from by omega]; ring
  -- (p-2)! is a unit, (p-1) ... combine
  have hu2 : IsUnit (((p-2)! : ℕ) : ZMod (p^2)) := by
    apply (ZMod.isUnit_iff_coprime _ _).mpr
    apply Nat.Coprime.pow_right
    rw [Nat.coprime_comm]
    apply (Nat.Prime.coprime_iff_not_dvd hp).mpr
    rw [Nat.Prime.dvd_factorial hp]; omega
  rw [hfac21] at hcZ
  have key : (Nat.choose (2*p-2) (p-1) : ZMod (p^2))*((p:ZMod (p^2))-1)^2
      = (p:ZMod (p^2))*((p:ZMod (p^2))-1) := by
    have h0 : ((Nat.choose (2*p-2) (p-1) : ZMod (p^2))*((p:ZMod (p^2))-1)^2
        - (p:ZMod (p^2))*((p:ZMod (p^2))-1)) * ((p-2)!:ZMod (p^2))^2 = 0 := by
      linear_combination hcZ
    have hk := (hu2.pow 2).mul_left_eq_zero.mp h0
    linear_combination hk
  have hunitb : IsUnit ((p:ZMod (p^2))-1) := by
    have he : ((p-1:ℕ):ZMod (p^2)) = (p:ZMod (p^2))-1 := by
      push_cast [show (1:ℕ)≤p from by omega]; ring
    rw [← he]
    apply (ZMod.isUnit_iff_coprime _ _).mpr
    apply Nat.Coprime.pow_right
    rw [show p = (p-1)+1 from by omega]
    exact Nat.coprime_self_add_right.mpr (by simp [Nat.Coprime])
  have hzero : ((Nat.choose (2*p-2) (p-1) : ZMod (p^2)) + (p:ZMod (p^2)))*((p:ZMod (p^2))-1)^2 = 0 := by
    linear_combination key + ((p:ZMod (p^2))-1)*hp20
  have hfin := (hunitb.pow 2).mul_left_eq_zero.mp hzero
  exact eq_neg_of_add_eq_zero_left hfin

lemma C5pm5 (p : ℕ) (hp : Nat.Prime p) (hp5 : 5 ≤ p) :
    ((Nat.choose (5*p-5) (p-1) : ℕ) : ZMod (p^2)) = -(p : ZMod (p^2)) := by
  haveI : Fact (Nat.Prime p) := ⟨hp⟩
  haveI : NeZero (p^2) := ⟨pow_ne_zero 2 hp.pos.ne'⟩
  haveI : NeZero p := ⟨hp.pos.ne'⟩
  have hch : Nat.choose (5*p-5) (p-1) * (p-1)! * (4*p-4)! = (5*p-5)! := by
    have h := Nat.choose_mul_factorial_mul_factorial (show p-1 ≤ 5*p-5 from by omega)
    rwa [show 5*p-5-(p-1) = 4*p-4 from by omega] at h
  have hsplit : (5*p-5)! = (4*p-4)! * ∏ i ∈ Finset.Icc (4*p-3) (5*p-5), i := by
    have d1 : (5*p-5)! = ∏ i ∈ Finset.Icc 1 (5*p-5), i := by
      rw [show Finset.Icc 1 (5*p-5) = Finset.Ico 1 ((5*p-5)+1) from by
        ext x; simp only [Finset.mem_Icc, Finset.mem_Ico]; omega, Finset.prod_Ico_id_eq_factorial]
    have d2 : (4*p-4)! = ∏ i ∈ Finset.Icc 1 (4*p-4), i := by
      rw [show Finset.Icc 1 (4*p-4) = Finset.Ico 1 ((4*p-4)+1) from by
        ext x; simp only [Finset.mem_Icc, Finset.mem_Ico]; omega]
      exact (Finset.prod_Ico_id_eq_factorial (4*p-4)).symm
    have hu1 : Finset.Icc 1 (5*p-5) = Finset.Icc 1 (4*p-4) ∪ Finset.Icc (4*p-3) (5*p-5) := by
      ext x; simp only [Finset.mem_union, Finset.mem_Icc]; omega
    have hd1 : Disjoint (Finset.Icc 1 (4*p-4)) (Finset.Icc (4*p-3) (5*p-5)) := by
      rw [Finset.disjoint_left]; intro x hx hy
      simp only [Finset.mem_Icc] at hx hy; omega
    rw [d1, hu1, Finset.prod_union hd1, ← d2]
  have hC : Nat.choose (5*p-5) (p-1) * (p-1)! = ∏ i ∈ Finset.Icc (4*p-3) (5*p-5), i := by
    have heq : Nat.choose (5*p-5) (p-1) * (p-1)! * (4*p-4)!
        = (∏ i ∈ Finset.Icc (4*p-3) (5*p-5), i) * (4*p-4)! := by
      rw [hch, hsplit]; ring
    exact Nat.eq_of_mul_eq_mul_right (Nat.factorial_pos _) heq
  have hprodsplit : ∏ i ∈ Finset.Icc (4*p-3) (5*p-5), i
      = (∏ i ∈ Finset.Icc (4*p-3) (4*p-1), i) * ((4*p) * ∏ i ∈ Finset.Icc (4*p+1) (5*p-5), i) := by
    have hu1 : Finset.Icc (4*p-3) (5*p-5) = Finset.Icc (4*p-3) (4*p-1) ∪ Finset.Icc (4*p) (5*p-5) := by
      ext x; simp only [Finset.mem_union, Finset.mem_Icc]; omega
    have hd1 : Disjoint (Finset.Icc (4*p-3) (4*p-1)) (Finset.Icc (4*p) (5*p-5)) := by
      rw [Finset.disjoint_left]; intro x hx hy
      simp only [Finset.mem_Icc] at hx hy; omega
    have hu2 : Finset.Icc (4*p) (5*p-5) = insert (4*p) (Finset.Icc (4*p+1) (5*p-5)) := by
      ext x; simp only [Finset.mem_insert, Finset.mem_Icc]; omega
    have hnm : (4*p) ∉ Finset.Icc (4*p+1) (5*p-5) := by simp only [Finset.mem_Icc]; omega
    rw [hu1, Finset.prod_union hd1, hu2, Finset.prod_insert hnm]
  rw [hprodsplit] at hC
  set Q1 := ∏ i ∈ Finset.Icc (4*p-3) (4*p-1), i with hQ1def
  set Q2 := ∏ i ∈ Finset.Icc (4*p+1) (5*p-5), i with hQ2def
  -- mod p sub-facts
  have hQ1p : (Q1 : ZMod p) = (-3)*(-2)*(-1) := by
    rw [hQ1def]
    have hset : Finset.Icc (4*p-3) (4*p-1) = {4*p-3, 4*p-2, 4*p-1} := by
      ext x; simp only [Finset.mem_Icc, Finset.mem_insert, Finset.mem_singleton]; omega
    rw [hset, Finset.prod_insert (by simp only [Finset.mem_insert, Finset.mem_singleton]; omega),
        Finset.prod_insert (by simp only [Finset.mem_singleton]; omega), Finset.prod_singleton]
    push_cast [Nat.cast_sub (show (3:ℕ) ≤ 4*p by omega), Nat.cast_sub (show (2:ℕ) ≤ 4*p by omega),
      Nat.cast_sub (show (1:ℕ) ≤ 4*p by omega)]
    rw [ZMod.natCast_self]; ring
  have hQ2p : (Q2 : ZMod p) = ((p-5)! : ZMod p) := by
    rw [hQ2def, show Finset.Icc (4*p+1) (5*p-5) = Finset.map (addLeftEmbedding (4*p)) (Finset.Icc 1 (p-5)) from by
      rw [Finset.map_add_left_Icc]; congr 1 <;> omega, Nat.cast_prod, Finset.prod_map]
    have e1 : ∏ i ∈ Finset.Icc 1 (p-5), ((addLeftEmbedding (4*p) i : ℕ) : ZMod p)
        = ∏ i ∈ Finset.Icc 1 (p-5), ((i:ℕ):ZMod p) := by
      apply Finset.prod_congr rfl; intro i _
      simp only [addLeftEmbedding_apply]
      push_cast; rw [ZMod.natCast_self]; ring
    rw [e1, ← Nat.cast_prod]
    congr 1
    rw [show Finset.Icc 1 (p-5) = Finset.Ico 1 ((p-5)+1) from by
      ext x; simp only [Finset.mem_Icc, Finset.mem_Ico]; omega]
    exact Finset.prod_Ico_id_eq_factorial (p-5)
  have hfacp : ((p-1)! : ZMod p) = 24 * ((p-5)! : ZMod p) := by
    have hf : (p-1)! = (p-1)*(p-2)*(p-3)*(p-4)*(p-5)! := by
      have e1 : (p-1)! = (p-1)*(p-2)! := by
        rw [show p-1=(p-2)+1 from by omega, Nat.factorial_succ, show (p-2)+1=p-1 from by omega]
      have e2 : (p-2)! = (p-2)*(p-3)! := by
        rw [show p-2=(p-3)+1 from by omega, Nat.factorial_succ, show (p-3)+1=p-2 from by omega]
      have e3 : (p-3)! = (p-3)*(p-4)! := by
        rw [show p-3=(p-4)+1 from by omega, Nat.factorial_succ, show (p-4)+1=p-3 from by omega]
      have e4 : (p-4)! = (p-4)*(p-5)! := by
        rw [show p-4=(p-5)+1 from by omega, Nat.factorial_succ, show (p-5)+1=p-4 from by omega]
      rw [e1, e2, e3, e4]; ring
    rw [hf]
    push_cast [Nat.cast_sub (show (1:ℕ)≤p by omega), Nat.cast_sub (show (2:ℕ)≤p by omega),
      Nat.cast_sub (show (3:ℕ)≤p by omega), Nat.cast_sub (show (4:ℕ)≤p by omega)]
    rw [ZMod.natCast_self]; ring
  have hmodp : p ∣ (4 * Q1 * Q2 + (p-1)!) := by
    rw [← ZMod.natCast_eq_zero_iff]
    have hcast : ((4*Q1*Q2 + (p-1)! : ℕ) : ZMod p)
        = 4 * (Q1:ZMod p) * (Q2:ZMod p) + ((p-1)!:ZMod p) := by push_cast; ring
    rw [hcast, hQ1p, hQ2p, hfacp]; ring
  obtain ⟨m, hm⟩ := hmodp
  have hzero2 : (p:ZMod (p^2)) * ((4*Q1*Q2:ℕ):ZMod (p^2)) + (p:ZMod (p^2)) * (((p-1)!:ℕ):ZMod (p^2)) = 0 := by
    have hcomb : (p:ZMod (p^2)) * ((4*Q1*Q2:ℕ):ZMod (p^2)) + (p:ZMod (p^2)) * (((p-1)!:ℕ):ZMod (p^2))
        = ((p * (4*Q1*Q2 + (p-1)!) : ℕ):ZMod (p^2)) := by push_cast; ring
    have hpm : (p * (4*Q1*Q2 + (p-1)!) : ℕ) = p^2 * m := by rw [hm]; ring
    rw [hcomb, hpm, Nat.cast_mul, ZMod.natCast_self, zero_mul]
  have eqA : (Nat.choose (5*p-5) (p-1) : ZMod (p^2)) * ((p-1)!:ZMod (p^2))
      = (p:ZMod (p^2)) * ((4*Q1*Q2:ℕ):ZMod (p^2)) := by
    have h := congrArg (fun z:ℕ => (z:ZMod (p^2))) hC
    simp only at h
    push_cast at h ⊢
    linear_combination h
  have eqB : (Nat.choose (5*p-5) (p-1) : ZMod (p^2)) * ((p-1)!:ZMod (p^2))
      = -(p:ZMod (p^2)) * ((p-1)!:ZMod (p^2)) := by
    rw [eqA]; linear_combination hzero2
  have hunit : IsUnit (((p-1)! : ℕ):ZMod (p^2)) := by
    apply (ZMod.isUnit_iff_coprime _ _).mpr
    apply Nat.Coprime.pow_right
    rw [Nat.coprime_comm]
    apply (Nat.Prime.coprime_iff_not_dvd hp).mpr
    rw [Nat.Prime.dvd_factorial hp]; omega
  have hsub : ((Nat.choose (5*p-5) (p-1):ZMod (p^2)) - (-(p:ZMod (p^2)))) * ((p-1)!:ZMod (p^2)) = 0 := by
    linear_combination eqB
  exact sub_eq_zero.mp (hunit.mul_left_eq_zero.mp hsub)

/-- If `C ≡ -p (mod p²)` then in `ZMod (p^3)`, `C = p²·a - p` for some natural `a`. -/
lemma lift_negp (p C : ℕ) (h : ((C:ℕ):ZMod (p^2)) = -(p:ZMod (p^2))) :
    ∃ a : ℕ, (C : ZMod (p^3)) = (p:ZMod (p^3))^2 * (a:ZMod (p^3)) - (p:ZMod (p^3)) := by
  have hdvd : p^2 ∣ (C + p) := by
    rw [← ZMod.natCast_eq_zero_iff]
    push_cast
    rw [h]; ring
  obtain ⟨a, ha⟩ := hdvd
  refine ⟨a, ?_⟩
  have hcast : ((C + p : ℕ) : ZMod (p^3)) = ((p^2 * a : ℕ) : ZMod (p^3)) := by rw [ha]
  push_cast at hcast
  linear_combination hcast

lemma cc_pm1_raw (p : ℕ) (hp : Nat.Prime p) (hp5 : 5 ≤ p) :
    (Nat.choose (2*p-2) (p-1) : ZMod (p^3)) * (Nat.choose (5*p-5) (p-1) : ZMod (p^3))
      = (p:ZMod (p^3))^2 := by
  obtain ⟨a, ha⟩ := lift_negp p _ (C2pm2 p hp hp5)
  obtain ⟨b, hb⟩ := lift_negp p _ (C5pm5 p hp hp5)
  have hp3 : (p:ZMod (p^3))^3 = 0 := by rw [← Nat.cast_pow, ZMod.natCast_self]
  rw [ha, hb]
  linear_combination ((p:ZMod (p^3)) * (a:ZMod (p^3)) * (b:ZMod (p^3)) - (a:ZMod (p^3)) - (b:ZMod (p^3))) * hp3

lemma cc_pm1_conn (p : ℕ) (hp : Nat.Prime p) (hp5 : 5 ≤ p) :
    ((( ((p-1).choose (p-1))^2 * (((p-1)+(p-1)).choose (p-1)) * ((3*(p-1)+2*(p-1)).choose (p-1)) : ℕ) : ℤ) : ZMod (p^3)) = (p:ZMod (p^3))^2 := by
  have h1 : (p-1).choose (p-1) = 1 := Nat.choose_self _
  have h2 : (p-1)+(p-1) = 2*p-2 := by omega
  have h3 : 3*(p-1)+2*(p-1) = 5*p-5 := by omega
  rw [h1, h2, h3]
  push_cast
  rw [← cc_pm1_raw p hp hp5]
  ring
