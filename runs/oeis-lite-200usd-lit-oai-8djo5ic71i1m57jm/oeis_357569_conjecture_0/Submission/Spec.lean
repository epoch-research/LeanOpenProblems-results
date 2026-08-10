import FormalConjectures.Util.ProblemImports
set_option linter.unusedTactic false
set_option linter.unnecessarySimpa false

open Nat Finset

/--
A357569: $a(n) = \binom{3n}{n}^2 - 27 \binom{2n}{n}$.
-/
def a (n : ℕ) : ℤ :=
  (Int.ofNat ((3 * n).choose n)) ^ 2 - (27 : ℤ) * Int.ofNat ((2 * n).choose n)


lemma unit_sum_sq_zmod_prime_power (p r : ℕ) (hp : Nat.Prime p) (hp5 : 5 ≤ p) :
    (letI : Fintype (ZMod (p^r))ˣ := Fintype.ofFinite _
     ∑ x : (ZMod (p^r))ˣ, ((x : (ZMod (p^r))ˣ) : ZMod (p^r)) ^ 2) = 0 := by
  classical
  let n := p^r
  letI : Fintype (ZMod n)ˣ := Fintype.ofFinite _
  have hcop2 : Nat.Coprime 2 n := by
    dsimp [n]
    exact (Nat.coprime_of_lt_prime (by decide : (2:ℕ) ≠ 0) (by omega) hp).symm.pow_right r
  let u : (ZMod n)ˣ := ZMod.unitOfCoprime 2 hcop2
  let S : ZMod n := ∑ x : (ZMod n)ˣ, (x : ZMod n)^2
  have hSperm : S = ∑ x : (ZMod n)ˣ, ((u * x : (ZMod n)ˣ) : ZMod n)^2 := by
    dsimp [S]
    symm
    exact Fintype.sum_equiv (Equiv.mulLeft u) (fun x : (ZMod n)ˣ => ((u * x : (ZMod n)ˣ) : ZMod n)^2)
      (fun y : (ZMod n)ˣ => (y : ZMod n)^2) (by intro x; rfl)
  have hS : S = (u : ZMod n)^2 * S := by
    calc
      S = ∑ x : (ZMod n)ˣ, ((u * x : (ZMod n)ˣ) : ZMod n)^2 := hSperm
      _ = ∑ x : (ZMod n)ˣ, ((u : ZMod n) * (x : ZMod n))^2 := by rfl
      _ = ∑ x : (ZMod n)ˣ, (u : ZMod n)^2 * (x : ZMod n)^2 := by
        apply Finset.sum_congr rfl; intro x hx; ring
      _ = (u : ZMod n)^2 * S := by simp [S, Finset.mul_sum]
  have hzero : (((u : ZMod n)^2 - 1) * S) = 0 := by
    rw [sub_mul, one_mul, ← hS, sub_self]
  have hunit3 : IsUnit (((u : ZMod n)^2 - 1) : ZMod n) := by
    have hu : (u : ZMod n) = (2 : ZMod n) := by simp [u, ZMod.coe_unitOfCoprime]
    rw [hu]; norm_num
    have hcop3 : Nat.Coprime 3 n := by
      dsimp [n]
      exact (Nat.coprime_of_lt_prime (by decide : (3:ℕ) ≠ 0) (by omega) hp).symm.pow_right r
    simpa [ZMod.coe_unitOfCoprime] using (ZMod.unitOfCoprime 3 hcop3).isUnit
  have hS0 : S = 0 := hunit3.mul_right_eq_zero.mp hzero
  simpa [n, S]

lemma unit_sum_inv_sq_zmod_prime_power (p r : ℕ) (hp : Nat.Prime p) (hp5 : 5 ≤ p) :
    (letI : Fintype (ZMod (p^r))ˣ := Fintype.ofFinite _
     ∑ x : (ZMod (p^r))ˣ, (((x⁻¹ : (ZMod (p^r))ˣ) : ZMod (p^r)) ^ 2)) = 0 := by
  classical
  let n := p^r
  letI : Fintype (ZMod n)ˣ := Fintype.ofFinite _
  have h := unit_sum_sq_zmod_prime_power p r hp hp5
  change (∑ x : (ZMod n)ˣ, ((x⁻¹ : (ZMod n)ˣ) : ZMod n)^2) = 0
  calc
    (∑ x : (ZMod n)ˣ, ((x⁻¹ : (ZMod n)ˣ) : ZMod n)^2)
        = ∑ x : (ZMod n)ˣ, ((x : (ZMod n)ˣ) : ZMod n)^2 := by
          exact Fintype.sum_equiv (Equiv.inv (ZMod n)ˣ) (fun x : (ZMod n)ˣ => ((x⁻¹ : (ZMod n)ˣ) : ZMod n)^2)
            (fun y : (ZMod n)ˣ => ((y : (ZMod n)ˣ) : ZMod n)^2) (by intro x; rfl)
    _ = 0 := by simpa [n] using h

lemma sum_units_pair {M : Type*} [AddCommMonoid M] (p q : ℕ) (hpq : p ∣ q) (hqodd : q % 2 = 1) (f : ℕ → M) :
    (∑ i ∈ (Finset.range q).filter (fun i => ¬ p ∣ i+1), f (i+1)) =
      ∑ i ∈ (Finset.range (q/2)).filter (fun i => ¬ p ∣ i+1), (f (i+1) + f (q - (i+1))) := by
  classical
  let S := (Finset.range q).filter (fun i => ¬ p ∣ i+1)
  let L0 := (Finset.range (q/2)).filter (fun i => ¬ p ∣ i+1)
  have hq : q = 2*(q/2)+1 := by
    have := Nat.div_add_mod q 2
    omega
  have hS : (∑ i ∈ (Finset.range q).filter (fun i => ¬ p ∣ i+1), f (i+1)) = ∑ i ∈ S, f (i+1) := rfl
  rw [hS]
  have hsplit : (∑ i ∈ S, f (i+1)) =
      (∑ i ∈ S.filter (fun i => i < q/2), f (i+1)) +
      (∑ i ∈ S.filter (fun i => ¬ i < q/2), f (i+1)) := by
    exact (Finset.sum_filter_add_sum_filter_not (s:=S) (p:=fun i => i < q/2) (f:=fun i => f (i+1))).symm
  rw [hsplit]
  have hlower : S.filter (fun i => i < q/2) = L0 := by
    ext i; simp [S,L0]
    constructor
    · intro h; exact ⟨h.2, h.1.2⟩
    · intro h
      have hiq : i < q := by omega
      exact ⟨⟨hiq,h.2⟩,h.1⟩
  have hupper : (∑ i ∈ S.filter (fun i => ¬ i < q/2), f (i+1)) =
      ∑ i ∈ L0, f (q - (i+1)) := by
    refine Finset.sum_bij (fun i hi => q - (i+1) - 1) ?mem ?inj ?surj ?val
    · intro i hi
      simp [L0,S] at hi ⊢
      rcases hi with ⟨⟨hiq,hndvd⟩, hnotlt⟩
      have hi_ge : q/2 ≤ i := by omega
      have hi_lt_qm1 : i + 1 < q := by
        by_contra h
        have : i + 1 = q := by omega
        apply hndvd
        rw [this]
        exact hpq
      have hpos : 0 < q - (i+1) := by omega
      have hltlower : q - (i+1) - 1 < q/2 := by omega
      have hndvd_pair : ¬ p ∣ (q - (i+1) - 1) + 1 := by
        intro hd
        apply hndvd
        have hqe : (q - (i+1) - 1) + 1 = q - (i+1) := by omega
        rw [hqe] at hd
        have hsub : q - (q - (i+1)) = i+1 := by omega
        simpa [hsub] using Nat.dvd_sub hpq hd
      exact ⟨hltlower, hndvd_pair⟩
    · intro i hi j hj heq
      simp [S] at hi hj
      rcases hi with ⟨⟨hiq0,hndi⟩, hnoti⟩
      rcases hj with ⟨⟨hjq0,hndj⟩, hnotj⟩
      have hiq : i + 1 < q := by
        by_contra h
        have : i + 1 = q := by omega
        exact hndi (by rw [this]; exact hpq)
      have hjq : j + 1 < q := by
        by_contra h
        have : j + 1 = q := by omega
        exact hndj (by rw [this]; exact hpq)
      change q - (i+1) - 1 = q - (j+1) - 1 at heq
      omega
    · intro j hj
      simp [L0,S] at hj ⊢
      rcases hj with ⟨hlt,hndvd⟩
      refine ⟨q - (j+1) - 1, ?_, ?_⟩
      · have hjpos : 0 < j+1 := by omega
        have hjltq : j+1 < q := by omega
        have hidxltq : q - (j+1) - 1 < q := by omega
        have hnotlower : ¬ q - (j+1) - 1 < q/2 := by omega
        have hndvd_pair : ¬ p ∣ (q - (j+1) - 1) + 1 := by
          intro hd
          apply hndvd
          have hqe : (q - (j+1) - 1) + 1 = q - (j+1) := by omega
          rw [hqe] at hd
          have hsub : q - (q - (j+1)) = j+1 := by omega
          simpa [hsub] using Nat.dvd_sub hpq hd
        exact ⟨⟨hidxltq,hndvd_pair⟩,(by omega)⟩
      · omega
    · intro i hi
      simp [S] at hi
      rcases hi with ⟨⟨hiq0,hndi⟩, hnoti⟩
      have hiq : i + 1 < q := by
        by_contra h
        have : i + 1 = q := by omega
        exact hndi (by rw [this]; exact hpq)
      have hcalc : (q - (i + 1) - 1) + 1 = q - (i+1) := by omega
      simp [hcalc]
      have : q - (q - (i + 1)) = i + 1 := by omega
      rw [this]
  rw [hlower, hupper]
  rw [← Finset.sum_add_distrib]

lemma unit_sum_eq_range_filter_prime_power (p r : ℕ) (hp : Nat.Prime p) (hr : 1 ≤ r)
    (F : (ZMod (p^r))ˣ → ZMod (p^r)) :
    (letI : Fintype (ZMod (p^r))ˣ := Fintype.ofFinite _
     ∑ x : (ZMod (p^r))ˣ, F x) =
      ∑ i ∈ (Finset.range (p^r)).filter (fun i => ¬ p ∣ i+1),
        (if h : p ∣ i+1 then 0 else F (ZMod.unitOfCoprime (i+1) (hp.coprime_pow_of_not_dvd h))) := by
  classical
  let q := p^r
  have hqpos : 0 < q := by dsimp [q]; exact pow_pos hp.pos r
  have hq_ne0 : q ≠ 0 := Nat.ne_of_gt hqpos
  have hq_gt1 : 1 < q := by
    dsimp [q]
    have hpge2 : 2 ≤ p := hp.two_le
    cases r with
    | zero => omega
    | succ r =>
      exact one_lt_pow₀ (by omega) (Nat.succ_ne_zero r)
  haveI : NeZero q := ⟨hq_ne0⟩
  haveI : Fact (1 < q) := ⟨hq_gt1⟩
  haveI : Nontrivial (ZMod q) := ZMod.nontrivial q
  letI : Fintype (ZMod q)ˣ := Fintype.ofFinite _
  let S := (Finset.range q).filter (fun i => ¬ p ∣ i+1)
  let Fq : (ZMod q)ˣ → ZMod q := by simpa [q] using F
  let G : ℕ → ZMod q := fun i =>
    if h : p ∣ i+1 then 0 else Fq (ZMod.unitOfCoprime (i+1) (by exact hp.coprime_pow_of_not_dvd h))
  let g : (ZMod q)ˣ → ℕ := fun x => (x : ZMod q).val - 1
  change (∑ x : (ZMod q)ˣ, Fq x) = ∑ i ∈ S, G i
  refine Finset.sum_bij (fun x _ => g x) ?mem ?inj ?surj ?val
  · intro x hx
    simp [S, g]
    have hlt : (x : ZMod q).val < q := ZMod.val_lt (x : ZMod q)
    have hcop : Nat.Coprime (x : ZMod q).val q := ZMod.val_coe_unit_coprime x
    have hne0 : (x : ZMod q).val ≠ 0 := by
      intro hv
      have hx0 : (x : ZMod q) = 0 := by rwa [← ZMod.val_eq_zero]
      exact (Units.ne_zero x) hx0
    constructor
    · omega
    · intro hpd
      have hpq : p ∣ q := by dsimp [q]; exact dvd_pow_self p (by omega)
      have hpd1 : p ∣ (x : ZMod q).val := by
        have hvadd : (x : ZMod q).val - 1 + 1 = (x : ZMod q).val := by omega
        simpa [hvadd] using hpd
      have : p ∣ Nat.gcd (x : ZMod q).val q := Nat.dvd_gcd hpd1 hpq
      rw [Nat.coprime_iff_gcd_eq_one.mp hcop] at this
      exact hp.not_dvd_one this
  · intro x hx y hy hxy
    apply Units.ext
    have hxv : (x : ZMod q).val ≠ 0 := by
      intro hv; exact Units.ne_zero x (by rwa [← ZMod.val_eq_zero])
    have hyv : (y : ZMod q).val ≠ 0 := by
      intro hv; exact Units.ne_zero y (by rwa [← ZMod.val_eq_zero])
    have hxvy : (x : ZMod q).val - 1 = (y : ZMod q).val - 1 := hxy
    have : (x : ZMod q).val = (y : ZMod q).val := by omega
    rw [← ZMod.natCast_zmod_val (x : ZMod q), ← ZMod.natCast_zmod_val (y : ZMod q), this]
  · intro i hi
    refine ⟨ZMod.unitOfCoprime (i+1) ?hc, by simp, ?_⟩
    · simp [S] at hi
      exact hp.coprime_pow_of_not_dvd hi.2
    · simp [g, ZMod.coe_unitOfCoprime]
      simp [S] at hi
      have hiq : i+1 < q := by
        have hi_lt : i < q := hi.1
        by_contra h
        have hieq : i+1 = q := by omega
        apply hi.2
        rw [hieq]
        dsimp [q]
        exact dvd_pow_self p (by omega)
      have hcast : ((i : ZMod q) + 1) = ((i + 1 : ℕ) : ZMod q) := by norm_num
      rw [hcast, ZMod.val_cast_of_lt hiq]
      omega
  · intro x hx
    simp [G, g]
    have hne0 : (x : ZMod q).val ≠ 0 := by
      intro hv
      have hx0 : (x : ZMod q) = 0 := by rwa [← ZMod.val_eq_zero]
      exact (Units.ne_zero x) hx0
    have hnot : ¬ p ∣ (x : ZMod q).val - 1 + 1 := by
      intro hpd0
      have hvadd : (x : ZMod q).val - 1 + 1 = (x : ZMod q).val := by omega
      have hpd : p ∣ (x : ZMod q).val := by simpa [hvadd] using hpd0
      have hpq : p ∣ q := by dsimp [q]; exact dvd_pow_self p (by omega)
      have hcop : Nat.Coprime (x : ZMod q).val q := ZMod.val_coe_unit_coprime x
      have : p ∣ Nat.gcd (x : ZMod q).val q := Nat.dvd_gcd hpd hpq
      rw [Nat.coprime_iff_gcd_eq_one.mp hcop] at this
      exact hp.not_dvd_one this
    rw [dif_neg hnot]
    apply congrArg Fq
    apply Units.ext
    simp [ZMod.coe_unitOfCoprime]

lemma lower_inv_sq_sum_zmod_zero (p r : ℕ) (hp : Nat.Prime p) (hp5 : 5 ≤ p) (hr : 1 ≤ r) :
    (let q := p^r
     ∑ i ∈ (Finset.range (q/2)).filter (fun i => ¬ p ∣ i+1),
       (if h : p ∣ i+1 then 0 else (((ZMod.unitOfCoprime (i+1) (by dsimp [q]; exact hp.coprime_pow_of_not_dvd h))⁻¹ : (ZMod q)ˣ) : ZMod q)^2)) = 0 := by
  classical
  let q := p^r
  have hqpos : 0 < q := by dsimp [q]; exact pow_pos hp.pos r
  have hq_ne0 : q ≠ 0 := Nat.ne_of_gt hqpos
  have hq_gt1 : 1 < q := by
    dsimp [q]
    cases r with
    | zero => omega
    | succ r => exact one_lt_pow₀ (by omega) (Nat.succ_ne_zero r)
  haveI : NeZero q := ⟨hq_ne0⟩
  haveI : Fact (1 < q) := ⟨hq_gt1⟩
  haveI : Nontrivial (ZMod q) := ZMod.nontrivial q
  letI : Fintype (ZMod q)ˣ := Fintype.ofFinite _
  let f : ℕ → ZMod q := fun u =>
    if h : p ∣ u then 0 else
      (((ZMod.unitOfCoprime u (by dsimp [q]; exact hp.coprime_pow_of_not_dvd h))⁻¹ : (ZMod q)ˣ) : ZMod q)^2
  have hfull0 : (∑ i ∈ (Finset.range q).filter (fun i => ¬ p ∣ i+1), f (i+1)) = 0 := by
    have hunit := unit_sum_inv_sq_zmod_prime_power p r hp hp5
    have htransfer := unit_sum_eq_range_filter_prime_power p r hp hr (fun x : (ZMod (p^r))ˣ => (((x⁻¹ : (ZMod (p^r))ˣ) : ZMod (p^r))^2))
    change (∑ i ∈ (Finset.range q).filter (fun i => ¬ p ∣ i+1), f (i+1)) = 0
    rw [← htransfer]
    simpa [q] using hunit
  have hpq : p ∣ q := by dsimp [q]; exact dvd_pow_self p (by omega)
  have hqodd : q % 2 = 1 := by
    have hpodd : p % 2 = 1 := by
      rw [hp.mod_two_eq_one_iff_ne_two]
      omega
    dsimp [q]
    rw [Nat.pow_mod]
    simp [hpodd]
  have hpair := sum_units_pair (M:=ZMod q) p q hpq hqodd f
  have hfull_pair : (∑ i ∈ (Finset.range q).filter (fun i => ¬ p ∣ i+1), f (i+1)) =
      ∑ i ∈ (Finset.range (q/2)).filter (fun i => ¬ p ∣ i+1), (f (i+1) + f (q-(i+1))) := hpair
  have hupper_eq : ∀ i ∈ (Finset.range (q/2)).filter (fun i => ¬ p ∣ i+1), f (q-(i+1)) = f (i+1) := by
    intro i hi
    simp only [f]
    simp only [mem_filter, mem_range] at hi
    have hiq : i + 1 < q := by omega
    have hnoti : ¬ p ∣ i+1 := hi.2
    have hnotq : ¬ p ∣ q - (i+1) := by
      intro hd
      apply hnoti
      have hsub : q - (q - (i+1)) = i+1 := by omega
      simpa [hsub] using Nat.dvd_sub hpq hd
    rw [dif_neg hnotq, dif_neg hnoti]
    have hcast : ((q - (i+1) : ℕ) : ZMod q) = - ((i+1 : ℕ) : ZMod q) := by
      apply eq_neg_of_add_eq_zero_left
      rw [← Nat.cast_add]
      have hadd : q - (i+1) + (i+1) = q := by omega
      rw [hadd]
      exact CharP.cast_eq_zero (ZMod q) q
    let u : (ZMod q)ˣ := ZMod.unitOfCoprime (i+1) (hp.coprime_pow_of_not_dvd hnoti)
    let negUnit : (ZMod q)ˣ :=
      ⟨-(u : ZMod q), -((u⁻¹ : (ZMod q)ˣ) : ZMod q), by simp, by simp⟩
    have hunitneg : ZMod.unitOfCoprime (q - (i+1)) (hp.coprime_pow_of_not_dvd hnotq) = negUnit := by
      apply Units.ext
      dsimp [negUnit, u]
      simpa [ZMod.coe_unitOfCoprime] using hcast
    rw [hunitneg]
    dsimp [negUnit]
    simp
    ring
  have hunit2 : IsUnit (2 : ZMod q) := by
    change IsUnit ((2:ℕ) : ZMod q)
    rw [ZMod.isUnit_iff_coprime]
    dsimp [q]
    exact (Nat.coprime_of_lt_prime (by decide : (2:ℕ) ≠ 0) (by omega) hp).symm.pow_right r
  have hfull_pair0 : (∑ i ∈ (Finset.range (q/2)).filter (fun i => ¬ p ∣ i+1), (f (i+1) + f (q-(i+1)))) = 0 := by
    rw [← hfull_pair, hfull0]
  have hlower2 : (2 : ZMod q) * (∑ i ∈ (Finset.range (q/2)).filter (fun i => ¬ p ∣ i+1), f (i+1)) = 0 := by
    rw [← hfull_pair0]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [hupper_eq i hi]
    ring
  have hlower0 : (∑ i ∈ (Finset.range (q/2)).filter (fun i => ¬ p ∣ i+1), f (i+1)) = 0 := by
    exact hunit2.mul_right_eq_zero.mp hlower2
  simpa [q, f] using hlower0
lemma prod_congr_dvd (s : Finset ℕ) (A D : ℕ → ℤ) (q : ℤ)
    (hD : ∀ i ∈ s, q ∣ D i) :
    q ∣ (∏ i ∈ s, (A i + D i)) - (∏ i ∈ s, A i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
      simp [ha]
      have hDa : q ∣ D a := hD a (by simp)
      have hDs : ∀ i ∈ s, q ∣ D i := by intro i hi; exact hD i (by simp [hi])
      have ih' := ih hDs
      obtain ⟨u,hu⟩ := hDa
      obtain ⟨v,hv⟩ := ih'
      use u * (∏ i ∈ s, (A i + D i)) + (A a) * v
      have hv' : (∏ i ∈ s, (A i + D i)) = (∏ i ∈ s, A i) + q*v := by linarith
      rw [hu, hv']
      ring

lemma prod_linear_first_refined' (s : Finset ℕ) (A B : ℕ → ℤ) (q c : ℤ)
    (hAB : ∀ i ∈ s, q ∣ A i * B i - 1) :
    q^3 ∣ (∏ i ∈ s, (A i + c * q^2)) - (∏ i ∈ s, A i) * (1 + c*q^2 * ∑ i ∈ s, B i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
      simp [ha]
      let Psh := ∏ i ∈ s, (A i + c*q^2)
      let PA := ∏ i ∈ s, A i
      let SB := ∑ i ∈ s, B i
      have hABa : q ∣ A a * B a - 1 := hAB a (by simp)
      have hABs : ∀ i ∈ s, q ∣ A i * B i - 1 := by intro i hi; exact hAB i (by simp [hi])
      have ih' := ih hABs
      have hprodq : q ∣ Psh - PA := by
        dsimp [Psh, PA]
        apply prod_congr_dvd s A (fun i => c*q^2) q
        intro i hi
        use c*q
        ring
      have hprodq2 : q ∣ Psh - (A a * B a) * PA := by
        have htmp : q ∣ (Psh - PA) + (PA - (A a * B a) * PA) := dvd_add hprodq ?_
        · simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc, mul_assoc] using htmp
        · obtain ⟨w,hw⟩ := hABa
          use -PA*w
          calc
            PA - A a * B a * PA = -PA * (A a * B a - 1) := by ring
            _ = -PA * (q*w) := by rw [hw]
            _ = q * (-PA*w) := by ring
      obtain ⟨u,hu⟩ := ih'
      obtain ⟨v,hv⟩ := hprodq2
      use A a * u + c * v
      dsimp [Psh, PA, SB] at hu hv ⊢
      have hdecomp :
        (A a + c * q ^ 2) * (∏ i ∈ s, (A i + c * q ^ 2)) -
          (A a * ∏ i ∈ s, A i) * (1 + c * q ^ 2 * (B a + ∑ i ∈ s, B i)) =
        A a * ((∏ i ∈ s, (A i + c * q ^ 2)) - (∏ i ∈ s, A i) * (1 + c * q ^ 2 * ∑ i ∈ s, B i)) +
          c*q^2 * ((∏ i ∈ s, (A i + c * q ^ 2)) - A a * B a * (∏ i ∈ s, A i)) := by
        ring
      rw [hdecomp, hu, hv]
      ring

lemma prod_units_pair {M : Type*} [CommMonoid M] (p q : ℕ) (hpq : p ∣ q) (hqodd : q % 2 = 1) (f : ℕ → M) :
    (∏ i ∈ (Finset.range q).filter (fun i => ¬ p ∣ i+1), f (i+1)) =
      ∏ i ∈ (Finset.range (q/2)).filter (fun i => ¬ p ∣ i+1), f (i+1) * f (q - (i+1)) := by
  classical
  let S := (Finset.range q).filter (fun i => ¬ p ∣ i+1)
  let L0 := (Finset.range (q/2)).filter (fun i => ¬ p ∣ i+1)
  have hq : q = 2*(q/2)+1 := by
    have := Nat.div_add_mod q 2
    omega
  have hS : (∏ i ∈ (Finset.range q).filter (fun i => ¬ p ∣ i+1), f (i+1)) = ∏ i ∈ S, f (i+1) := rfl
  rw [hS]
  have hsplit : (∏ i ∈ S, f (i+1)) =
      (∏ i ∈ S.filter (fun i => i < q/2), f (i+1)) *
      (∏ i ∈ S.filter (fun i => ¬ i < q/2), f (i+1)) := by
    exact (Finset.prod_filter_mul_prod_filter_not (s:=S) (p:=fun i => i < q/2) (f:=fun i => f (i+1))).symm
  rw [hsplit]
  have hlower : S.filter (fun i => i < q/2) = L0 := by
    ext i; simp [S,L0]
    constructor
    · intro h; exact ⟨h.2, h.1.2⟩
    · intro h
      have hiq : i < q := by omega
      exact ⟨⟨hiq,h.2⟩,h.1⟩
  have hupper : (∏ i ∈ S.filter (fun i => ¬ i < q/2), f (i+1)) =
      ∏ i ∈ L0, f (q - (i+1)) := by
    refine Finset.prod_bij (fun i hi => q - (i+1) - 1) ?mem ?inj ?surj ?val
    · intro i hi
      simp [L0,S] at hi ⊢
      rcases hi with ⟨⟨hiq,hndvd⟩, hnotlt⟩
      have hi_lt_qm1 : i + 1 < q := by
        by_contra h
        have : i + 1 = q := by omega
        apply hndvd
        rw [this]
        exact hpq
      have hltlower : q - (i+1) - 1 < q/2 := by omega
      have hndvd_pair : ¬ p ∣ (q - (i+1) - 1) + 1 := by
        intro hd
        apply hndvd
        have hqe : (q - (i+1) - 1) + 1 = q - (i+1) := by omega
        rw [hqe] at hd
        have hsub : q - (q - (i+1)) = i+1 := by omega
        simpa [hsub] using Nat.dvd_sub hpq hd
      exact ⟨hltlower, hndvd_pair⟩
    · intro i hi j hj heq
      simp [S] at hi hj
      rcases hi with ⟨⟨hiq0,hndi⟩, hnoti⟩
      rcases hj with ⟨⟨hjq0,hndj⟩, hnotj⟩
      have hiq : i + 1 < q := by
        by_contra h
        have : i + 1 = q := by omega
        exact hndi (by rw [this]; exact hpq)
      have hjq : j + 1 < q := by
        by_contra h
        have : j + 1 = q := by omega
        exact hndj (by rw [this]; exact hpq)
      change q - (i+1) - 1 = q - (j+1) - 1 at heq
      omega
    · intro j hj
      simp [L0,S] at hj ⊢
      rcases hj with ⟨hlt,hndvd⟩
      refine ⟨q - (j+1) - 1, ?_, ?_⟩
      · have hjltq : j+1 < q := by omega
        have hidxltq : q - (j+1) - 1 < q := by omega
        have hndvd_pair : ¬ p ∣ (q - (j+1) - 1) + 1 := by
          intro hd
          apply hndvd
          have hqe : (q - (j+1) - 1) + 1 = q - (j+1) := by omega
          rw [hqe] at hd
          have hsub : q - (q - (j+1)) = j+1 := by omega
          simpa [hsub] using Nat.dvd_sub hpq hd
        exact ⟨⟨hidxltq,hndvd_pair⟩,(by omega)⟩
      · omega
    · intro i hi
      simp [S] at hi
      rcases hi with ⟨⟨hiq0,hndi⟩, hnoti⟩
      have hiq : i + 1 < q := by
        by_contra h
        have : i + 1 = q := by omega
        exact hndi (by rw [this]; exact hpq)
      have hcalc : (q - (i + 1) - 1) + 1 = q - (i+1) := by omega
      simp [hcalc]
      have : q - (q - (i + 1)) = i + 1 := by omega
      rw [this]
  rw [hlower, hupper]
  rw [← Finset.prod_mul_distrib]

lemma paired_product_identity (p q t : ℕ) (hpq : p ∣ q) (hqodd : q % 2 = 1) :
    (∏ i ∈ (Finset.range q).filter (fun i => ¬ p ∣ i+1), ((i+1 : ℤ) + (t:ℤ) * q)) =
      ∏ i ∈ (Finset.range (q/2)).filter (fun i => ¬ p ∣ i+1),
        ((i+1 : ℤ) * (q - (i+1) : ℤ) + (t:ℤ) * ((t:ℤ)+1) * (q:ℤ)^2) := by
  trans ∏ i ∈ (Finset.range (q/2)).filter (fun i => ¬ p ∣ i+1),
        (((i+1:ℤ) + (t:ℤ)*(q:ℤ)) * (((q - (i+1) : ℕ) : ℤ) + (t:ℤ)*(q:ℤ)))
  · exact prod_units_pair p q hpq hqodd (fun u : ℕ => ((u:ℤ) + (t:ℤ)*(q:ℤ)))
  · apply Finset.prod_congr rfl
    intro i hi
    simp only [mem_filter, mem_range] at hi
    have hiq : i + 1 < q := by omega
    have hcast : ((q - (i + 1) : ℕ) : ℤ) = (q : ℤ) - (i+1 : ℤ) := by omega
    rw [hcast]
    ring

lemma prod_linear_diff_dvd (s : Finset ℕ) (f : ℕ → ℤ) (x c d : ℤ) :
    x ∣ (∏ i ∈ s, (f i + c * x)) - (∏ i ∈ s, (f i + d * x)) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s has ih =>
      rw [Finset.prod_insert has, Finset.prod_insert has]
      set Ac : ℤ := ∏ i ∈ s, (f i + c * x)
      set Ad : ℤ := ∏ i ∈ s, (f i + d * x)
      have hdiff : x ∣ Ac - Ad := by simpa [Ac, Ad] using ih
      rcases hdiff with ⟨k, hk⟩
      refine ⟨f a * k + (c * Ac - d * Ad), ?_⟩
      calc
        (f a + c * x) * Ac - (f a + d * x) * Ad
            = f a * (Ac - Ad) + x * (c * Ac - d * Ad) := by ring
        _ = f a * (x * k) + x * (c * Ac - d * Ad) := by rw [hk]
        _ = x * (f a * k + (c * Ac - d * Ad)) := by ring

lemma prod_linear_second_dvd (s : Finset ℕ) (f : ℕ → ℤ) (x : ℤ) :
    x ^ 2 ∣ (∏ i ∈ s, (f i + 6 * x)) - 3 * (∏ i ∈ s, (f i + 2 * x)) + 2 * (∏ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp
  | insert a s has ih =>
      rw [Finset.prod_insert has, Finset.prod_insert has, Finset.prod_insert has]
      set A6 : ℤ := ∏ i ∈ s, (f i + 6 * x)
      set A2 : ℤ := ∏ i ∈ s, (f i + 2 * x)
      set A0 : ℤ := ∏ i ∈ s, f i
      have hE : x ^ 2 ∣ A6 - 3 * A2 + 2 * A0 := by simpa [A6, A2, A0] using ih
      have hD : x ∣ A6 - A2 := by simpa [A6, A2] using prod_linear_diff_dvd s f x 6 2
      rcases hE with ⟨k, hk⟩
      rcases hD with ⟨l, hl⟩
      refine ⟨f a * k + 6 * l, ?_⟩
      calc
        (f a + 6 * x) * A6 - 3 * ((f a + 2 * x) * A2) + 2 * (f a * A0)
            = f a * (A6 - 3 * A2 + 2 * A0) + 6 * x * (A6 - A2) := by ring
        _ = f a * (x ^ 2 * k) + 6 * x * (x * l) := by rw [hk, hl]
        _ = x ^ 2 * (f a * k + 6 * l) := by ring

lemma U_second_dvd_rge3 (p r : ℕ) (hp : Nat.Prime p) (hp3 : 3 ≤ p) (hr : 3 ≤ r) :
    ((p:ℤ)^(3*r+3)) ∣
      (∏ i ∈ (Finset.range (p^r)).filter (fun i => ¬ p ∣ i+1), ((i+1:ℤ) + 2*(p^r:ℤ)))
      - 3 * (∏ i ∈ (Finset.range (p^r)).filter (fun i => ¬ p ∣ i+1), ((i+1:ℤ) + 1*(p^r:ℤ)))
      + 2 * (∏ i ∈ (Finset.range (p^r)).filter (fun i => ¬ p ∣ i+1), ((i+1:ℤ))) := by
  classical
  let q := p^r
  let L := (Finset.range (q/2)).filter (fun i => ¬ p ∣ i+1)
  have hpq : p ∣ q := by
    dsimp [q]
    exact dvd_pow_self p (by omega)
  have hqodd : q % 2 = 1 := by
    have hpodd : p % 2 = 1 := by
      have hpne2 : p ≠ 2 := by omega
      exact (hp.mod_two_eq_one_iff_ne_two).2 hpne2
    dsimp [q]
    rw [Nat.pow_mod]
    rw [hpodd]
    simp
  have h2 := paired_product_identity p q 2 hpq hqodd
  have h1 := paired_product_identity p q 1 hpq hqodd
  have h0 := paired_product_identity p q 0 hpq hqodd
  have hmain := prod_linear_second_dvd L (fun i => ((i+1:ℤ) * (q - (i+1):ℤ))) ((q:ℤ)^2)
  have h2' :
      (∏ i ∈ L, ((i + 1 : ℤ) * (q - (i + 1) : ℤ) + 6 * (q : ℤ) ^ 2)) =
      (∏ i ∈ (Finset.range q).filter (fun i => ¬p ∣ i + 1), ((i+1:ℤ) + 2*(q:ℤ))) := by
    simpa [L] using h2.symm
  have h1' :
      (∏ i ∈ L, ((i + 1 : ℤ) * (q - (i + 1) : ℤ) + 2 * (q : ℤ) ^ 2)) =
      (∏ i ∈ (Finset.range q).filter (fun i => ¬p ∣ i + 1), ((i+1:ℤ) + 1*(q:ℤ))) := by
    simpa [L] using h1.symm
  have h0' :
      (∏ i ∈ L, (i + 1 : ℤ) * (q - (i + 1) : ℤ)) =
      (∏ i ∈ (Finset.range q).filter (fun i => ¬p ∣ i + 1), ((i+1:ℤ))) := by
    simpa [L] using h0.symm
  have hrewrite :
      (∏ i ∈ L, ((i + 1 : ℤ) * (q - (i + 1) : ℤ) + 6 * (q : ℤ) ^ 2)) -
          3 * (∏ i ∈ L, ((i + 1 : ℤ) * (q - (i + 1) : ℤ) + 2 * (q : ℤ) ^ 2)) +
        2 * (∏ i ∈ L, (i + 1 : ℤ) * (q - (i + 1) : ℤ)) =
      (∏ i ∈ (Finset.range q).filter (fun i => ¬p ∣ i + 1), ((i+1:ℤ) + 2*(q:ℤ)))
      - 3*(∏ i ∈ (Finset.range q).filter (fun i => ¬p ∣ i + 1), ((i+1:ℤ) + 1*(q:ℤ)))
      + 2*(∏ i ∈ (Finset.range q).filter (fun i => ¬p ∣ i + 1), ((i+1:ℤ))) := by
    rw [h2', h1', h0']
  have hq4 : ((q:ℤ)^2)^2 = (p:ℤ)^(4*r) := by
    dsimp [q]
    norm_cast
    rw [← pow_mul]
    ring_nf
  have hdivq4 : (p:ℤ)^(4*r) ∣
      (∏ i ∈ (Finset.range q).filter (fun i => ¬p ∣ i + 1), ((i+1:ℤ) + 2*(q:ℤ)))
      - 3*(∏ i ∈ (Finset.range q).filter (fun i => ¬p ∣ i + 1), ((i+1:ℤ) + 1*(q:ℤ)))
      + 2*(∏ i ∈ (Finset.range q).filter (fun i => ¬p ∣ i + 1), ((i+1:ℤ))) := by
    rw [← hrewrite]
    simpa [hq4] using hmain
  have hexp : 3*r+3 ≤ 4*r := by omega
  exact dvd_trans (pow_dvd_pow (p:ℤ) hexp) hdivq4


lemma choose_mul_prod_formula (m q : ℕ) (hm : 1 ≤ m) :
    (Nat.choose (m*q) q) * (∏ i ∈ Finset.range q, (i+1)) =
      ∏ i ∈ Finset.range q, ((m-1)*q + (i+1)) := by
  calc
    (Nat.choose (m*q) q) * (∏ i ∈ Finset.range q, (i+1))
        = (Nat.choose (m*q) q) * q ! := by rw [Finset.prod_range_add_one_eq_factorial]
    _ = q ! * Nat.choose (m*q) q := by rw [mul_comm]
    _ = q ! * Nat.choose ((m-1)*q + q) q := by
      congr 2
      have hm' : m = (m - 1) + 1 := (Nat.sub_add_cancel hm).symm
      rw [hm']; simp; ring
    _ = ((m-1)*q + 1).ascFactorial q := by rw [Nat.ascFactorial_eq_factorial_mul_choose]
    _ = ∏ i ∈ Finset.range q, ((m-1)*q + 1 + i) := by rw [Nat.ascFactorial_eq_prod_range]
    _ = ∏ i ∈ Finset.range q, ((m-1)*q + (i+1)) := by
      apply Finset.prod_congr rfl; intro i hi; omega

lemma prod_multiples_range (p q' : ℕ) (hp : 0 < p) (f : ℕ → ℕ) :
    (∏ i ∈ (Finset.range (p*q')).filter (fun i => p ∣ i+1), f (i+1)) =
      ∏ j ∈ Finset.range q', f (p*(j+1)) := by
  classical
  refine Finset.prod_bij (fun i hi => (i+1)/p - 1) ?hi ?hinj ?hsurj ?hfg
  · intro i hi
    simp only [mem_filter, mem_range] at hi ⊢
    rcases hi with ⟨hi_lt, hdvd⟩
    have hpos : 0 < (i+1)/p := Nat.div_pos (le_of_dvd (Nat.succ_pos i) hdvd) hp
    have hle : (i+1)/p ≤ q' := by
      have hdiv : (i+1)/p * p = i+1 := by rw [Nat.div_mul_cancel hdvd]
      have : i+1 ≤ p*q' := by omega
      have : ((i+1)/p) * p ≤ q' * p := by rw [hdiv]; simpa [mul_comm] using this
      exact Nat.le_of_mul_le_mul_right this hp
    omega
  · intro i hi k hk heq
    simp only [mem_filter, mem_range] at hi hk
    rcases hi with ⟨hi_lt, hi_dvd⟩
    rcases hk with ⟨hk_lt, hk_dvd⟩
    have hposi : 0 < (i+1)/p := Nat.div_pos (le_of_dvd (Nat.succ_pos i) hi_dvd) hp
    have hposk : 0 < (k+1)/p := Nat.div_pos (le_of_dvd (Nat.succ_pos k) hk_dvd) hp
    have hdivi : ((i+1)/p) * p = i+1 := by rw [Nat.div_mul_cancel hi_dvd]
    have hdivk : ((k+1)/p) * p = k+1 := by rw [Nat.div_mul_cancel hk_dvd]
    have hq0 := congrArg (fun x : ℕ => x + 1) heq
    have hsubi : ((i+1)/p - 1) + 1 = (i+1)/p := Nat.sub_add_cancel (Nat.succ_le_of_lt hposi)
    have hsubk : ((k+1)/p - 1) + 1 = (k+1)/p := Nat.sub_add_cancel (Nat.succ_le_of_lt hposk)
    change ((i+1)/p - 1) + 1 = ((k+1)/p - 1) + 1 at hq0
    rw [hsubi, hsubk] at hq0
    have hq : (i+1)/p = (k+1)/p := hq0
    have : i+1 = k+1 := by rw [← hdivi, ← hdivk, hq]
    exact Nat.succ.inj this
  · intro j hj
    simp only [mem_range] at hj
    refine ⟨p*(j+1)-1, ?_, ?_⟩
    · simp only [mem_filter, mem_range]
      have hpospj : 0 < p*(j+1) := mul_pos hp (Nat.succ_pos j)
      constructor
      · have hjle : j + 1 ≤ q' := by omega
        have hmulle : p * (j + 1) ≤ p * q' := Nat.mul_le_mul_left p hjle
        omega
      · have : (p*(j+1)-1)+1 = p*(j+1) := by omega
        rw [this]
        exact dvd_mul_right p (j+1)
    · have hpospj : 0 < p*(j+1) := mul_pos hp (Nat.succ_pos j)
      have hsucc : (p*(j+1)-1)+1 = p*(j+1) := by omega
      change ((p * (j + 1) - 1 + 1) / p - 1) = j
      rw [hsucc]
      rw [Nat.mul_div_right _ hp]
      omega
  · intro i hi
    simp only [mem_filter, mem_range] at hi
    rcases hi with ⟨hi_lt, hi_dvd⟩
    have hdivi : ((i+1)/p) * p = i+1 := by rw [Nat.div_mul_cancel hi_dvd]
    have hposi : 0 < (i+1)/p := Nat.div_pos (le_of_dvd (Nat.succ_pos i) hi_dvd) hp
    have : p * (((i+1)/p - 1) + 1) = i+1 := by
      have : ((i+1)/p - 1) + 1 = (i+1)/p := by omega
      rw [this, mul_comm, hdivi]
    simp [this]


lemma prod_split_filter (p q' : ℕ) (f : ℕ → ℕ) :
    (∏ i ∈ Finset.range (p*q'), f (i+1)) =
      (∏ i ∈ (Finset.range (p*q')).filter (fun i => p ∣ i+1), f (i+1)) *
      (∏ i ∈ (Finset.range (p*q')).filter (fun i => ¬ p ∣ i+1), f (i+1)) := by
  classical
  rw [← Finset.prod_filter_mul_prod_filter_not (s := Finset.range (p*q')) (p := fun i => p ∣ i+1) (f := fun i => f (i+1))]

lemma quotient_identity (m p q' : ℕ) (hm : 1 ≤ m) (hp : 0 < p) :
    (Nat.choose (m*(p*q')) (p*q')) *
      (∏ i ∈ (Finset.range (p*q')).filter (fun i => ¬ p ∣ i+1), (i+1)) =
    (Nat.choose (m*q') q') *
      (∏ i ∈ (Finset.range (p*q')).filter (fun i => ¬ p ∣ i+1), ((m-1)*(p*q') + (i+1))) := by
  classical
  let q := p*q'
  let unitDen := ∏ i ∈ (Finset.range q).filter (fun i => ¬ p ∣ i+1), (i+1)
  let unitNum := ∏ i ∈ (Finset.range q).filter (fun i => ¬ p ∣ i+1), ((m-1)*q + (i+1))
  let den' := ∏ j ∈ Finset.range q', (j+1)
  let num' := ∏ j ∈ Finset.range q', ((m-1)*q' + (j+1))
  have hqform := choose_mul_prod_formula m q hm
  have hq'form := choose_mul_prod_formula m q' hm
  have hdenSplit : (∏ i ∈ Finset.range q, (i+1)) =
      (∏ i ∈ (Finset.range q).filter (fun i => p ∣ i+1), (i+1)) * unitDen := by
    dsimp [unitDen]
    exact prod_split_filter p q' (fun k => k)
  have hnumSplit : (∏ i ∈ Finset.range q, ((m-1)*q + (i+1))) =
      (∏ i ∈ (Finset.range q).filter (fun i => p ∣ i+1), ((m-1)*q + (i+1))) * unitNum := by
    dsimp [unitNum]
    exact prod_split_filter p q' (fun k => (m-1)*q + k)
  have hmultDen0 : (∏ i ∈ (Finset.range q).filter (fun i => p ∣ i+1), (i+1)) =
      ∏ j ∈ Finset.range q', p*(j+1) := by
    simpa [q] using prod_multiples_range p q' hp (fun k => k)
  have hmultDen : (∏ i ∈ (Finset.range q).filter (fun i => p ∣ i+1), (i+1)) =
      p ^ q' * den' := by
    rw [hmultDen0]
    dsimp [den']
    calc
      (∏ j ∈ Finset.range q', p * (j + 1)) = (∏ j ∈ Finset.range q', p) * (∏ j ∈ Finset.range q', (j + 1)) := by
        rw [Finset.prod_mul_distrib]
      _ = p ^ q' * ∏ j ∈ Finset.range q', (j + 1) := by simp
  have hmultNum0 : (∏ i ∈ (Finset.range q).filter (fun i => p ∣ i+1), ((m-1)*q + (i+1))) =
      ∏ j ∈ Finset.range q', ((m-1)*q + p*(j+1)) := by
    simpa [q] using prod_multiples_range p q' hp (fun k => (m-1)*q + k)
  have hterm (j : ℕ) : ((m-1)*q + p*(j+1)) = p*((m-1)*q' + (j+1)) := by
    dsimp [q]
    ring
  have hmultNum : (∏ i ∈ (Finset.range q).filter (fun i => p ∣ i+1), ((m-1)*q + (i+1))) =
      p ^ q' * num' := by
    rw [hmultNum0]
    conv_lhs =>
      arg 2
      intro j
      rw [hterm j]
    dsimp [num']
    calc
      (∏ j ∈ Finset.range q', p * ((m - 1) * q' + (j + 1))) =
          (∏ j ∈ Finset.range q', p) * (∏ j ∈ Finset.range q', ((m - 1) * q' + (j + 1))) := by
        rw [Finset.prod_mul_distrib]
      _ = p ^ q' * ∏ j ∈ Finset.range q', ((m - 1) * q' + (j + 1)) := by simp
  have hmain : (Nat.choose (m*q) q) * (p ^ q' * den' * unitDen) =
      (p ^ q' * num') * unitNum := by
    calc
      (Nat.choose (m*q) q) * (p ^ q' * den' * unitDen)
          = (Nat.choose (m*q) q) * ((∏ i ∈ Finset.range q, (i+1))) := by
              rw [hdenSplit, hmultDen]
      _ = (∏ i ∈ Finset.range q, ((m-1)*q + (i+1))) := hqform
      _ = (p ^ q' * num') * unitNum := by rw [hnumSplit, hmultNum]
  have hnum' : num' = (Nat.choose (m*q') q') * den' := by
    dsimp [num'] at hq'form ⊢
    exact hq'form.symm
  rw [hnum'] at hmain
  have hcancel : p ^ q' * den' * ((Nat.choose (m*q) q) * unitDen) =
      p ^ q' * den' * ((Nat.choose (m*q') q') * unitNum) := by
    nlinarith [hmain]
  have hposDen : 0 < den' := by
    dsimp [den']
    apply Finset.prod_pos
    intro j hj; omega
  have hposF : 0 < p ^ q' * den' := by
    exact mul_pos (pow_pos hp q') hposDen
  exact Nat.mul_left_cancel hposF hcancel


lemma int_dvd_mul_of_dvd_left {a b c : ℤ} (h : a ∣ b) : a ∣ b * c := h.mul_right c
lemma int_dvd_mul_of_dvd_right {a b c : ℤ} (h : a ∣ c) : a ∣ b * c := h.mul_left b

lemma assemble_core (p r : ℕ) (B0 D0 P0 P1 P2 : ℤ)
    (hD1 : (p : ℤ) ^ (3*r) ∣ P1 - P0)
    (hD2 : (p : ℤ) ^ (3*r+3) ∣ P2 - 3*P1 + 2*P0)
    (hC : (p : ℤ)^3 ∣ 2*B0^2 - 9*D0)
    (hP20 : (p : ℤ)^3 ∣ P2 - P0) :
    (p : ℤ) ^ (3*r+3) ∣
      (B0^2 * (P2^2 - P0^2) - 27 * D0 * P0 * (P1 - P0)) := by
  let pp : ℤ := (p : ℤ)
  have hpow : pp ^ (3*r+3) = pp^(3*r) * pp^3 := by
    rw [← pow_add]

  rw [hpow]
  -- show expression = (P1-P0)*coef + D2*coef
  let D1 := P1 - P0
  let D2 := P2 - 3*P1 + 2*P0
  have hP2 : P2 - P0 = 3*D1 + D2 := by dsimp [D1,D2]; ring
  have hfac : P2^2 - P0^2 = (P2 - P0) * (P2 + P0) := by ring
  have hexp : B0^2 * (P2^2 - P0^2) - 27 * D0 * P0 * (P1 - P0)
      = D1 * (3*B0^2*(P2+P0) - 27*D0*P0) + D2 * (B0^2*(P2+P0)) := by
    dsimp [D1,D2]
    ring
  rw [hexp]
  apply dvd_add
  ·
    -- need pp^3 divides coefficient
    have hcoef : pp^3 ∣ (3*B0^2*(P2+P0) - 27*D0*P0) := by
      have hrewrite : 3*B0^2*(P2+P0) - 27*D0*P0 =
          3*P0*(2*B0^2 - 9*D0) + 3*B0^2*(P2-P0) := by ring
      rw [hrewrite]
      apply dvd_add
      · exact (hC.mul_left (3*P0))
      · exact (hP20.mul_left (3*B0^2))
    simpa [D1, mul_comm, mul_left_comm, mul_assoc] using mul_dvd_mul hD1 hcoef
  · -- D2 term has high divisibility, but current modulus factored pp^(3r)*pp^3 = pp^(3r+3); hD2 matches original not factored
    rw [← hpow]
    exact hD2.mul_right (B0 ^ 2 * (P2 + P0))


lemma prod_pair_first_diff_dvd_c (s : Finset ℕ) (A B : ℕ → ℤ) (q c : ℤ)
    (hAB : ∀ i ∈ s, q ∣ A i * B i - 1)
    (hSum : q ∣ ∑ i ∈ s, B i) :
    q^3 ∣ (∏ i ∈ s, (A i + c * q^2)) - (∏ i ∈ s, A i) := by
  classical
  have h := prod_linear_first_refined' s A B q c hAB
  obtain ⟨k,hk⟩ := h
  obtain ⟨l,hl⟩ := hSum
  use k + c * (∏ i ∈ s, A i) * l
  calc
    (∏ i ∈ s, (A i + c * q ^ 2)) - ∏ i ∈ s, A i
      = ((∏ i ∈ s, (A i + c * q ^ 2)) - (∏ i ∈ s, A i) * (1 + c * q ^ 2 * ∑ i ∈ s, B i))
        + (∏ i ∈ s, A i) * (c * q ^ 2 * ∑ i ∈ s, B i) := by ring
    _ = q^3*k + (∏ i ∈ s, A i) * (c * q^2 * (q*l)) := by rw [hk, hl]
    _ = q^3 * (k + c * (∏ i ∈ s, A i) * l) := by ring

lemma U_offset_dvd_pge5 (p r t : ℕ) (hp : Nat.Prime p) (hp5 : 5 ≤ p) (hr : 1 ≤ r) :
    ((p:ℤ)^(3*r)) ∣
      (∏ i ∈ (Finset.range (p^r)).filter (fun i => ¬ p ∣ i+1), ((i+1:ℤ) + (t:ℤ)*(p^r:ℤ)))
      - (∏ i ∈ (Finset.range (p^r)).filter (fun i => ¬ p ∣ i+1), ((i+1:ℤ))) := by
  classical
  let q := p^r
  have hqpos : 0 < q := by dsimp [q]; exact pow_pos hp.pos r
  have hpq : p ∣ q := by dsimp [q]; exact dvd_pow_self p (by omega)
  have hqodd : q % 2 = 1 := by
    have hpodd : p % 2 = 1 := by rw [hp.mod_two_eq_one_iff_ne_two]; omega
    dsimp [q]; rw [Nat.pow_mod]; simp [hpodd]
  let S := (Finset.range (q/2)).filter (fun i => ¬ p ∣ i+1)
  let A : ℕ → ℤ := fun i => (i+1:ℤ) * (q - (i+1) : ℤ)
  let B : ℕ → ℤ := fun i =>
    if h : p ∣ i+1 then 0 else
      - (((((ZMod.unitOfCoprime (i+1) (by dsimp [q]; exact hp.coprime_pow_of_not_dvd h))⁻¹ : (ZMod q)ˣ) : ZMod q)^2).valMinAbs)
  have hAB : ∀ i ∈ S, (q:ℤ) ∣ A i * B i - 1 := by
    intro i hi
    simp only [S, mem_filter, mem_range] at hi
    have hnot : ¬ p ∣ i+1 := hi.2
    have hiq : i+1 < q := by omega
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    change ((A i * B i - 1 : ℤ) : ZMod q) = 0
    simp [A, B, dif_neg hnot]
    have hcastq : ((q - (i+1) : ℕ) : ZMod q) = - ((i+1 : ℕ) : ZMod q) := by
      apply eq_neg_of_add_eq_zero_left
      rw [← Nat.cast_add]
      have hadd : q - (i+1) + (i+1) = q := by omega
      rw [hadd]
      exact CharP.cast_eq_zero (ZMod q) q
    let u : (ZMod q)ˣ := ZMod.unitOfCoprime (i+1) (hp.coprime_pow_of_not_dvd hnot)
    have hu : (u : ZMod q) = ((i+1:ℕ):ZMod q) := by simp [u, ZMod.coe_unitOfCoprime]
    have hu' : (u : ZMod q) = (i : ZMod q) + 1 := by simpa using hu
    change (-(((i : ZMod q) + 1) * (-1 + -(i : ZMod q)) * (((u⁻¹ : (ZMod q)ˣ) : ZMod q)^2)) - 1) = 0
    have hneg : (-1 + -(i : ZMod q)) = -(u : ZMod q) := by
      rw [hu']
      ring
    rw [← hu', hneg]
    ring_nf
    rw [add_comm]
    rw [← mul_pow]
    simp
  have hSum : (q:ℤ) ∣ ∑ i ∈ S, B i := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    change (((∑ i ∈ S, B i : ℤ) : ZMod q) = 0)
    rw [Int.cast_sum]
    simp only [B]
    have hlower := lower_inv_sq_sum_zmod_zero p r hp hp5 hr
    trans - (∑ i ∈ S, (if h : p ∣ i+1 then 0 else (((ZMod.unitOfCoprime (i+1) (by dsimp [q]; exact hp.coprime_pow_of_not_dvd h))⁻¹ : (ZMod q)ˣ) : ZMod q)^2))
    · rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro i hi
      by_cases h : p ∣ i+1
      · simp [h]
      · simp [h, ZMod.coe_valMinAbs]
    · rw [show (∑ i ∈ S, (if h : p ∣ i+1 then 0 else (((ZMod.unitOfCoprime (i+1) (by dsimp [q]; exact hp.coprime_pow_of_not_dvd h))⁻¹ : (ZMod q)ˣ) : ZMod q)^2)) = 0 by simpa [q,S] using hlower]
      simp
  have hcore := prod_pair_first_diff_dvd_c S A B (q:ℤ) ((t:ℤ)*((t:ℤ)+1)) hAB hSum
  have hPt := paired_product_identity p q t hpq hqodd
  have hP0 := paired_product_identity p q 0 hpq hqodd
  have hcore' : (q:ℤ)^3 ∣
      (∏ i ∈ S, (A i + ((t:ℤ)*((t:ℤ)+1)) * (q:ℤ)^2)) - (∏ i ∈ S, A i) := by simpa [A] using hcore
  have htargetq : (q:ℤ)^3 ∣
      (∏ i ∈ (Finset.range q).filter (fun i => ¬ p ∣ i+1), ((i+1:ℤ) + (t:ℤ)*(q:ℤ)))
      - (∏ i ∈ (Finset.range q).filter (fun i => ¬ p ∣ i+1), ((i+1:ℤ) + ((0:ℕ):ℤ)*(q:ℤ))) := by
    rw [hPt, hP0]
    simpa [S, A, mul_assoc] using hcore'
  have htargetq' : (q:ℤ)^3 ∣
      (∏ i ∈ (Finset.range q).filter (fun i => ¬ p ∣ i+1), ((i+1:ℤ) + (t:ℤ)*(q:ℤ)))
      - (∏ i ∈ (Finset.range q).filter (fun i => ¬ p ∣ i+1), ((i+1:ℤ))) := by
    simpa using htargetq
  have hpowe : (q:ℤ)^3 = (p:ℤ)^(3*r) := by
    dsimp [q]
    rw [← pow_mul]
    congr 1
    omega
  rw [← hpowe]
  simpa [q] using htargetq'

lemma unit_prod_coprime_pow (p q N : ℕ) (hp : Nat.Prime p) :
    Nat.Coprime (p^N) (∏ i ∈ (Finset.range q).filter (fun i => ¬ p ∣ i+1), (i+1)) := by
  classical
  apply Nat.Coprime.prod_right
  intro i hi
  simp only [mem_filter, mem_range] at hi
  exact (hp.coprime_pow_of_not_dvd hi.2).symm

lemma unit_prod_isCoprime_int_pow (p q N : ℕ) (hp : Nat.Prime p) :
    IsCoprime ((p:ℤ)^N) ((∏ i ∈ (Finset.range q).filter (fun i => ¬ p ∣ i+1), (i+1) : ℕ) : ℤ) := by
  have hnat := unit_prod_coprime_pow p q N hp
  simpa [Int.natCast_pow] using hnat.isCoprime

lemma pow_mul_pow_sub_one (p r : ℕ) (hr : 1 ≤ r) : p * p ^ (r - 1) = p ^ r := by
  have hr' : r = (r - 1) + 1 := (Nat.sub_add_cancel hr).symm
  rw [hr']
  simp [pow_succ, mul_comm]

lemma choose_mul_primepow_stable_mod_p3_pge5 (p s m t : ℕ) (hp : Nat.Prime p) (hp5 : 5 ≤ p)
    (hm : 1 ≤ m) (hmt : t = m - 1) (hs : 1 ≤ s) :
    (Int.ofNat ((m * p^s).choose (p^s))) ≡ (Int.ofNat ((m * p^(s-1)).choose (p^(s-1)))) [ZMOD ((p:ℤ)^3)] := by
  classical
  let q0 := p^(s-1)
  let q := p^s
  let P0n : ℕ := ∏ i ∈ (Finset.range q).filter (fun i => ¬ p ∣ i+1), (i+1)
  let Ptn : ℕ := ∏ i ∈ (Finset.range q).filter (fun i => ¬ p ∣ i+1), ((m-1)*q + (i+1))
  let B : ℤ := Int.ofNat ((m*q).choose q)
  let B0 : ℤ := Int.ofNat ((m*q0).choose q0)
  let P0 : ℤ := Int.ofNat P0n
  let Pt : ℤ := Int.ofNat Ptn
  have hqeq : p * q0 = q := by
    dsimp [q0,q]
    exact pow_mul_pow_sub_one p s hs
  have hquot_nat := quotient_identity m p q0 hm hp.pos
  have hquot : B * P0 = B0 * Pt := by
    dsimp [B,B0,P0,Pt,P0n,Ptn]
    norm_cast
    simpa [q0, q, hqeq, mul_assoc] using hquot_nat
  have hU0 : ((p:ℤ)^3) ∣ Pt - P0 := by
    have hoff := U_offset_dvd_pge5 p s t hp hp5 hs
    have hpow : (p:ℤ)^3 ∣ (p:ℤ)^(3*s) := pow_dvd_pow (p:ℤ) (by omega)
    have hdiv := dvd_trans hpow hoff
    rw [hmt] at hdiv
    dsimp [Pt,P0,Ptn,P0n,q]
    simpa [mul_assoc, add_comm, add_left_comm, add_assoc, Nat.cast_add, Nat.cast_mul] using hdiv
  have hmain : ((p:ℤ)^3) ∣ (B - B0) * P0 := by
    have hcalc : (B - B0) * P0 = B0 * (Pt - P0) := by
      calc
        (B - B0) * P0 = B * P0 - B0 * P0 := by ring
        _ = B0 * Pt - B0 * P0 := by rw [hquot]
        _ = B0 * (Pt - P0) := by ring
    rw [hcalc]
    exact hU0.mul_left B0
  rw [Int.modEq_iff_dvd]
  -- orientation: modulus ∣ rhs - lhs
  change ((p:ℤ)^3) ∣ Int.ofNat ((m * p ^ (s - 1)).choose (p ^ (s - 1))) - Int.ofNat ((m * p ^ s).choose (p ^ s))
  have hcop : IsCoprime ((p:ℤ)^3) P0 := by
    dsimp [P0,P0n,q]
    exact unit_prod_isCoprime_int_pow p (p^s) 3 hp
  have hcancel : ((p:ℤ)^3) ∣ B - B0 := by
    exact hcop.dvd_of_dvd_mul_right hmain
  dsimp [B,B0,q,q0] at hcancel
  exact dvd_neg.mp (by simpa [sub_eq_add_neg, add_comm] using hcancel)

lemma choose_mul_primepow_mod_p3_pge5 (p s m t : ℕ) (hp : Nat.Prime p) (hp5 : 5 ≤ p)
    (hm : 1 ≤ m) (hmt : t = m - 1) :
    (Int.ofNat ((m * p^s).choose (p^s))) ≡ (m : ℤ) [ZMOD ((p:ℤ)^3)] := by
  induction s with
  | zero =>
      simp
  | succ s ih =>
      have hstab := choose_mul_primepow_stable_mod_p3_pge5 p (s+1) m t hp hp5 hm hmt (by omega)
      exact hstab.trans ih

lemma coeff_cancel_pge5 (p s : ℕ) (hp : Nat.Prime p) (hp5 : 5 ≤ p) :
    ((p:ℤ)^3) ∣
      2 * (Int.ofNat ((3 * p^s).choose (p^s)))^2 - 9 * (Int.ofNat ((2 * p^s).choose (p^s))) := by
  have hB := choose_mul_primepow_mod_p3_pge5 p s 3 2 hp hp5 (by omega) (by rfl)
  have hD := choose_mul_primepow_mod_p3_pge5 p s 2 1 hp hp5 (by omega) (by rfl)
  rw [Int.modEq_iff_dvd] at hB hD
  -- hB/hD orientations: modulus divides target - value, so B-3 and D-2 up to sign.
  have hB' : (p:ℤ)^3 ∣ Int.ofNat ((3 * p ^ s).choose (p ^ s)) - 3 := dvd_neg.mp (by simpa using hB)
  have hD' : (p:ℤ)^3 ∣ Int.ofNat ((2 * p ^ s).choose (p ^ s)) - 2 := dvd_neg.mp (by simpa using hD)
  obtain ⟨u, hu⟩ := hB'
  obtain ⟨v, hv⟩ := hD'
  use (12*u + 2*((p:ℤ)^3)*u^2 - 9*v)
  have hBexpr : Int.ofNat ((3 * p ^ s).choose (p ^ s)) = 3 + (p:ℤ)^3*u := by linarith
  have hDexpr : Int.ofNat ((2 * p ^ s).choose (p ^ s)) = 2 + (p:ℤ)^3*v := by linarith
  rw [hBexpr, hDexpr]
  ring

lemma unit_sum_sq_zmod_three_power_mul_three (r : ℕ) :
    (letI : Fintype (ZMod (3^r))ˣ := Fintype.ofFinite _
     ((3 : ZMod (3^r)) * (∑ x : (ZMod (3^r))ˣ, ((x : (ZMod (3^r))ˣ) : ZMod (3^r)) ^ 2)) = 0) := by
  classical
  let n := 3^r
  letI : Fintype (ZMod n)ˣ := Fintype.ofFinite _
  have hcop2 : Nat.Coprime 2 n := by
    dsimp [n]
    exact (Nat.coprime_of_lt_prime (by decide : (2:ℕ) ≠ 0) (by decide : 2 < 3) Nat.prime_three).symm.pow_right r
  let u : (ZMod n)ˣ := ZMod.unitOfCoprime 2 hcop2
  let S : ZMod n := ∑ x : (ZMod n)ˣ, (x : ZMod n)^2
  have hSperm : S = ∑ x : (ZMod n)ˣ, ((u * x : (ZMod n)ˣ) : ZMod n)^2 := by
    dsimp [S]
    symm
    exact Fintype.sum_equiv (Equiv.mulLeft u) (fun x : (ZMod n)ˣ => ((u * x : (ZMod n)ˣ) : ZMod n)^2)
      (fun y : (ZMod n)ˣ => (y : ZMod n)^2) (by intro x; rfl)
  have hS : S = (u : ZMod n)^2 * S := by
    calc
      S = ∑ x : (ZMod n)ˣ, ((u * x : (ZMod n)ˣ) : ZMod n)^2 := hSperm
      _ = ∑ x : (ZMod n)ˣ, ((u : ZMod n) * (x : ZMod n))^2 := by rfl
      _ = ∑ x : (ZMod n)ˣ, (u : ZMod n)^2 * (x : ZMod n)^2 := by
        apply Finset.sum_congr rfl; intro x hx; ring
      _ = (u : ZMod n)^2 * S := by simp [S, Finset.mul_sum]
  have hzero : (((u : ZMod n)^2 - 1) * S) = 0 := by
    rw [sub_mul, one_mul, ← hS, sub_self]
  have hu : (u : ZMod n) = (2 : ZMod n) := by simp [u, ZMod.coe_unitOfCoprime]
  rw [hu] at hzero
  norm_num at hzero
  simpa [n, S, mul_comm] using hzero

lemma unit_sum_inv_sq_zmod_three_power_mul_three (r : ℕ) :
    (letI : Fintype (ZMod (3^r))ˣ := Fintype.ofFinite _
     ((3 : ZMod (3^r)) * (∑ x : (ZMod (3^r))ˣ,
       (((x⁻¹ : (ZMod (3^r))ˣ) : ZMod (3^r)) ^ 2))) = 0) := by
  classical
  let n := 3^r
  letI : Fintype (ZMod n)ˣ := Fintype.ofFinite _
  have h := unit_sum_sq_zmod_three_power_mul_three r
  change (3 : ZMod n) * (∑ x : (ZMod n)ˣ, ((x⁻¹ : (ZMod n)ˣ) : ZMod n)^2) = 0
  calc
    (3 : ZMod n) * (∑ x : (ZMod n)ˣ, ((x⁻¹ : (ZMod n)ˣ) : ZMod n)^2)
        = (3 : ZMod n) * (∑ x : (ZMod n)ˣ, ((x : (ZMod n)ˣ) : ZMod n)^2) := by
          congr 1
          exact Fintype.sum_equiv (Equiv.inv (ZMod n)ˣ) (fun x : (ZMod n)ˣ => ((x⁻¹ : (ZMod n)ˣ) : ZMod n)^2)
            (fun y : (ZMod n)ˣ => ((y : (ZMod n)ˣ) : ZMod n)^2) (by intro x; rfl)
    _ = 0 := by simpa [n] using h

lemma lower_inv_sq_sum_zmod_three_mul_three (r : ℕ) (hr : 1 ≤ r) :
    (let q := 3^r
     (3 : ZMod q) * ∑ i ∈ (Finset.range (q/2)).filter (fun i => ¬ 3 ∣ i+1),
       (if h : 3 ∣ i+1 then 0 else (((ZMod.unitOfCoprime (i+1) (by dsimp [q]; exact Nat.prime_three.coprime_pow_of_not_dvd h))⁻¹ : (ZMod q)ˣ) : ZMod q)^2)) = 0 := by
  classical
  let q := 3^r
  have hqpos : 0 < q := by dsimp [q]; exact pow_pos (by decide : 0 < 3) r
  have hq_ne0 : q ≠ 0 := Nat.ne_of_gt hqpos
  have hq_gt1 : 1 < q := by
    dsimp [q]
    cases r with
    | zero => omega
    | succ r => exact one_lt_pow₀ (by decide : 1 < 3) (Nat.succ_ne_zero r)
  haveI : NeZero q := ⟨hq_ne0⟩
  haveI : Fact (1 < q) := ⟨hq_gt1⟩
  haveI : Nontrivial (ZMod q) := ZMod.nontrivial q
  letI : Fintype (ZMod q)ˣ := Fintype.ofFinite _
  let f : ℕ → ZMod q := fun u =>
    if h : 3 ∣ u then 0 else
      (((ZMod.unitOfCoprime u (by dsimp [q]; exact Nat.prime_three.coprime_pow_of_not_dvd h))⁻¹ : (ZMod q)ˣ) : ZMod q)^2
  have hfull0 : (3 : ZMod q) * (∑ i ∈ (Finset.range q).filter (fun i => ¬ 3 ∣ i+1), f (i+1)) = 0 := by
    have hunit := unit_sum_inv_sq_zmod_three_power_mul_three r
    have htransfer := unit_sum_eq_range_filter_prime_power 3 r Nat.prime_three hr (fun x : (ZMod (3^r))ˣ => (((x⁻¹ : (ZMod (3^r))ˣ) : ZMod (3^r))^2))
    change (3 : ZMod q) * (∑ i ∈ (Finset.range q).filter (fun i => ¬ 3 ∣ i+1), f (i+1)) = 0
    rw [← htransfer]
    simpa [q] using hunit
  have hpq : 3 ∣ q := by dsimp [q]; exact dvd_pow_self 3 (by omega)
  have hqodd : q % 2 = 1 := by
    dsimp [q]
    rw [Nat.pow_mod]
    norm_num
  have hpair := sum_units_pair (M:=ZMod q) 3 q hpq hqodd f
  have hupper_eq : ∀ i ∈ (Finset.range (q/2)).filter (fun i => ¬ 3 ∣ i+1), f (q-(i+1)) = f (i+1) := by
    intro i hi
    simp only [f]
    simp only [mem_filter, mem_range] at hi
    have hiq : i + 1 < q := by omega
    have hnoti : ¬ 3 ∣ i+1 := hi.2
    have hnotq : ¬ 3 ∣ q - (i+1) := by
      intro hd
      apply hnoti
      have hsub : q - (q - (i+1)) = i+1 := by omega
      simpa [hsub] using Nat.dvd_sub hpq hd
    rw [dif_neg hnotq, dif_neg hnoti]
    have hcast : ((q - (i+1) : ℕ) : ZMod q) = - ((i+1 : ℕ) : ZMod q) := by
      apply eq_neg_of_add_eq_zero_left
      rw [← Nat.cast_add]
      have hadd : q - (i+1) + (i+1) = q := by omega
      rw [hadd]
      exact CharP.cast_eq_zero (ZMod q) q
    let u : (ZMod q)ˣ := ZMod.unitOfCoprime (i+1) (Nat.prime_three.coprime_pow_of_not_dvd hnoti)
    let negUnit : (ZMod q)ˣ :=
      ⟨-(u : ZMod q), -((u⁻¹ : (ZMod q)ˣ) : ZMod q), by simp, by simp⟩
    have hunitneg : ZMod.unitOfCoprime (q - (i+1)) (Nat.prime_three.coprime_pow_of_not_dvd hnotq) = negUnit := by
      apply Units.ext
      dsimp [negUnit, u]
      simpa [ZMod.coe_unitOfCoprime] using hcast
    rw [hunitneg]
    dsimp [negUnit]
    simp
    ring
  have hfull_pair0 : (3 : ZMod q) * (∑ i ∈ (Finset.range (q/2)).filter (fun i => ¬ 3 ∣ i+1), (f (i+1) + f (q-(i+1)))) = 0 := by
    rw [← hpair]
    exact hfull0
  have hlower2 : (3 : ZMod q) * (2 * ∑ i ∈ (Finset.range (q/2)).filter (fun i => ¬ 3 ∣ i+1), f (i+1)) = 0 := by
    have hsum2 : (2 : ZMod q) * (∑ i ∈ (Finset.range (q/2)).filter (fun i => ¬ 3 ∣ i+1), f (i+1)) =
        ∑ i ∈ (Finset.range (q/2)).filter (fun i => ¬ 3 ∣ i+1), (f (i+1) + f (q-(i+1))) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      rw [hupper_eq i hi]
      ring
    rw [hsum2]
    exact hfull_pair0
  have hunit2 : IsUnit (2 : ZMod q) := by
    change IsUnit ((2:ℕ) : ZMod q)
    rw [ZMod.isUnit_iff_coprime]
    dsimp [q]
    exact (Nat.coprime_of_lt_prime (by decide : (2:ℕ) ≠ 0) (by decide : 2 < 3) Nat.prime_three).symm.pow_right r
  have hcomm : (3 : ZMod q) * (2 * ∑ i ∈ (Finset.range (q/2)).filter (fun i => ¬ 3 ∣ i+1), f (i+1)) =
      (2 : ZMod q) * ((3 : ZMod q) * ∑ i ∈ (Finset.range (q/2)).filter (fun i => ¬ 3 ∣ i+1), f (i+1)) := by ring
  rw [hcomm] at hlower2
  have hlower0 := hunit2.mul_right_eq_zero.mp hlower2
  simpa [q, f] using hlower0

lemma U_offset_dvd_three (r t : ℕ) (hr : 1 ≤ r) :
    ((3:ℤ)^(3*r - 1)) ∣
      (∏ i ∈ (Finset.range (3^r)).filter (fun i => ¬ 3 ∣ i+1), ((i+1:ℤ) + (t:ℤ)*(3^r:ℤ)))
      - (∏ i ∈ (Finset.range (3^r)).filter (fun i => ¬ 3 ∣ i+1), ((i+1:ℤ))) := by
  classical
  let q := 3^r
  have hqpos : 0 < q := by dsimp [q]; exact pow_pos (by decide : 0 < 3) r
  have hpq : 3 ∣ q := by dsimp [q]; exact dvd_pow_self 3 (by omega)
  have hqodd : q % 2 = 1 := by dsimp [q]; rw [Nat.pow_mod]; norm_num
  let S := (Finset.range (q/2)).filter (fun i => ¬ 3 ∣ i+1)
  let A : ℕ → ℤ := fun i => (i+1:ℤ) * (q - (i+1) : ℤ)
  let B : ℕ → ℤ := fun i =>
    if h : 3 ∣ i+1 then 0 else
      - (((((ZMod.unitOfCoprime (i+1) (by dsimp [q]; exact Nat.prime_three.coprime_pow_of_not_dvd h))⁻¹ : (ZMod q)ˣ) : ZMod q)^2).valMinAbs)
  have hAB : ∀ i ∈ S, (q:ℤ) ∣ A i * B i - 1 := by
    intro i hi
    simp only [S, mem_filter, mem_range] at hi
    have hnot : ¬ 3 ∣ i+1 := hi.2
    have hiq : i+1 < q := by omega
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    change ((A i * B i - 1 : ℤ) : ZMod q) = 0
    simp [A, B, dif_neg hnot]
    have hcastq : ((q - (i+1) : ℕ) : ZMod q) = - ((i+1 : ℕ) : ZMod q) := by
      apply eq_neg_of_add_eq_zero_left
      rw [← Nat.cast_add]
      have hadd : q - (i+1) + (i+1) = q := by omega
      rw [hadd]
      exact CharP.cast_eq_zero (ZMod q) q
    let u : (ZMod q)ˣ := ZMod.unitOfCoprime (i+1) (Nat.prime_three.coprime_pow_of_not_dvd hnot)
    have hu : (u : ZMod q) = ((i+1:ℕ):ZMod q) := by simp [u, ZMod.coe_unitOfCoprime]
    have hu' : (u : ZMod q) = (i : ZMod q) + 1 := by simpa using hu
    change (-(((i : ZMod q) + 1) * (-1 + -(i : ZMod q)) * (((u⁻¹ : (ZMod q)ˣ) : ZMod q)^2)) - 1) = 0
    have hneg : (-1 + -(i : ZMod q)) = -(u : ZMod q) := by
      rw [hu']
      ring
    rw [← hu', hneg]
    ring_nf
    rw [add_comm]
    rw [← mul_pow]
    simp
  have hSumWeak : ((3:ℤ)^(r-1)) ∣ ∑ i ∈ S, B i := by
    have hdiv3 : (q:ℤ) ∣ (3:ℤ) * (∑ i ∈ S, B i) := by
      rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
      change ((((3:ℤ) * (∑ i ∈ S, B i) : ℤ) : ZMod q) = 0)
      rw [Int.cast_mul, Int.cast_sum]
      have hlower := lower_inv_sq_sum_zmod_three_mul_three r hr
      have hcastsum : (∑ i ∈ S, ((B i : ℤ) : ZMod q)) =
          -(∑ i ∈ S, (if h : 3 ∣ i+1 then 0 else (((ZMod.unitOfCoprime (i+1) (by dsimp [q]; exact Nat.prime_three.coprime_pow_of_not_dvd h))⁻¹ : (ZMod q)ˣ) : ZMod q)^2)) := by
        rw [← Finset.sum_neg_distrib]
        apply Finset.sum_congr rfl
        intro i hi
        by_cases h : 3 ∣ i+1
        · simp [B, h]
        · simp [B, h, ZMod.coe_valMinAbs]
      rw [hcastsum, mul_neg]
      have hlow : (3 : ZMod q) * (∑ i ∈ S, (if h : 3 ∣ i+1 then 0 else (((ZMod.unitOfCoprime (i+1) (by dsimp [q]; exact Nat.prime_three.coprime_pow_of_not_dvd h))⁻¹ : (ZMod q)ˣ) : ZMod q)^2)) = 0 := by
        simpa [q,S] using hlower
      simpa [hlow]
    obtain ⟨k, hk⟩ := hdiv3
    refine ⟨k, ?_⟩
    have hqcast : (q:ℤ) = 3 * (3:ℤ)^(r-1) := by
      have hnat : 3 * 3^(r-1) = 3^r := pow_mul_pow_sub_one 3 r hr
      dsimp [q]
      norm_cast
      exact hnat.symm
    have hk' : (3:ℤ) * (∑ i ∈ S, B i) = (3:ℤ) * (((3:ℤ)^(r-1)) * k) := by
      rw [hk, hqcast]
      ring
    exact mul_left_cancel₀ (by norm_num : (3:ℤ) ≠ 0) hk'
  have hcore := prod_linear_first_refined' S A B (q:ℤ) ((t:ℤ)*((t:ℤ)+1)) hAB
  obtain ⟨k, hk⟩ := hcore
  obtain ⟨l, hl⟩ := hSumWeak
  have hPt := paired_product_identity 3 q t hpq hqodd
  have hP0 := paired_product_identity 3 q 0 hpq hqodd
  let M : ℤ := (3:ℤ)^(3*r-1)
  have hM_q3 : M ∣ (q:ℤ)^3 := by
    dsimp [M,q]
    change (3:ℤ)^(3*r-1) ∣ ((3:ℤ)^r)^3
    rw [← pow_mul]
    exact pow_dvd_pow (3:ℤ) (by omega)
  have hq2sum : M ∣ (q:ℤ)^2 * (∑ i ∈ S, B i) := by
    rw [hl]
    dsimp [M,q]
    use l
    have hq2 : (((3^r : ℕ) : ℤ))^2 = (3:ℤ)^(2*r) := by
      norm_cast
      rw [← pow_mul]
      ring_nf
    calc
      (((3^r : ℕ) : ℤ))^2 * ((3:ℤ)^(r-1) * l)
          = ((3:ℤ)^(2*r) * (3:ℤ)^(r-1)) * l := by rw [hq2]; ring
      _ = (3:ℤ)^(3*r-1) * l := by
          have hpow : (3:ℤ) ^ (2 * r) * (3:ℤ) ^ (r - 1) = (3:ℤ) ^ (3*r - 1) := by
            rw [← pow_add]
            congr 1
            omega
          rw [hpow]
  have hdiff_pair : M ∣ (∏ i ∈ S, (A i + ((t:ℤ)*((t:ℤ)+1)) * (q:ℤ)^2)) - (∏ i ∈ S, A i) := by
    have hrewrite : (∏ i ∈ S, (A i + ((t:ℤ)*((t:ℤ)+1)) * (q:ℤ)^2)) - (∏ i ∈ S, A i) =
        ((∏ i ∈ S, (A i + ((t:ℤ)*((t:ℤ)+1)) * (q:ℤ)^2)) - (∏ i ∈ S, A i) * (1 + ((t:ℤ)*((t:ℤ)+1)) * (q:ℤ)^2 * ∑ i ∈ S, B i))
        + (∏ i ∈ S, A i) * (((t:ℤ)*((t:ℤ)+1)) * ((q:ℤ)^2 * ∑ i ∈ S, B i)) := by ring
    rw [hrewrite]
    apply dvd_add
    · rw [hk]
      exact hM_q3.mul_right k
    · simpa [mul_assoc] using (hq2sum.mul_left ((∏ i ∈ S, A i) * ((t:ℤ)*((t:ℤ)+1))))
  have htarget : M ∣
      (∏ i ∈ (Finset.range q).filter (fun i => ¬ 3 ∣ i+1), ((i+1:ℤ) + (t:ℤ)*(q:ℤ)))
      - (∏ i ∈ (Finset.range q).filter (fun i => ¬ 3 ∣ i+1), ((i+1:ℤ))) := by
    rw [hPt]
    have hP0' : (∏ i ∈ (Finset.range q).filter (fun i => ¬ 3 ∣ i+1), ((i+1:ℤ))) = ∏ i ∈ S, A i := by
      simpa [S,A] using hP0
    rw [hP0']
    simpa [S,A, M, mul_assoc, add_comm, add_left_comm, add_assoc] using hdiff_pair
  simpa [q, M] using htarget

lemma choose_mul_threepow_stable_mod81 (s m t : ℕ)
    (hm : 1 ≤ m) (hmt : t = m - 1) (hs : 2 ≤ s) :
    (Int.ofNat ((m * 3^s).choose (3^s))) ≡ (Int.ofNat ((m * 3^(s-1)).choose (3^(s-1)))) [ZMOD ((3:ℤ)^4)] := by
  classical
  let q0 := 3^(s-1)
  let q := 3^s
  let P0n : ℕ := ∏ i ∈ (Finset.range q).filter (fun i => ¬ 3 ∣ i+1), (i+1)
  let Ptn : ℕ := ∏ i ∈ (Finset.range q).filter (fun i => ¬ 3 ∣ i+1), ((m-1)*q + (i+1))
  let B : ℤ := Int.ofNat ((m*q).choose q)
  let B0 : ℤ := Int.ofNat ((m*q0).choose q0)
  let P0 : ℤ := Int.ofNat P0n
  let Pt : ℤ := Int.ofNat Ptn
  have hs1 : 1 ≤ s := by omega
  have hqeq : 3 * q0 = q := by
    dsimp [q0,q]
    exact pow_mul_pow_sub_one 3 s hs1
  have hquot_nat := quotient_identity m 3 q0 hm (by decide : 0 < 3)
  have hquot : B * P0 = B0 * Pt := by
    dsimp [B,B0,P0,Pt,P0n,Ptn]
    norm_cast
    simpa [q0, q, hqeq, mul_assoc] using hquot_nat
  have hU0 : ((3:ℤ)^4) ∣ Pt - P0 := by
    have hoff := U_offset_dvd_three s t hs1
    have hpow : (3:ℤ)^4 ∣ (3:ℤ)^(3*s - 1) := pow_dvd_pow (3:ℤ) (by omega)
    have hdiv := dvd_trans hpow hoff
    rw [hmt] at hdiv
    dsimp [Pt,P0,Ptn,P0n,q]
    simpa [mul_assoc, add_comm, add_left_comm, add_assoc, Nat.cast_add, Nat.cast_mul] using hdiv
  have hmain : ((3:ℤ)^4) ∣ (B - B0) * P0 := by
    have hcalc : (B - B0) * P0 = B0 * (Pt - P0) := by
      calc
        (B - B0) * P0 = B * P0 - B0 * P0 := by ring
        _ = B0 * Pt - B0 * P0 := by rw [hquot]
        _ = B0 * (Pt - P0) := by ring
    rw [hcalc]
    exact hU0.mul_left B0
  rw [Int.modEq_iff_dvd]
  change ((3:ℤ)^4) ∣ Int.ofNat ((m * 3 ^ (s - 1)).choose (3 ^ (s - 1))) - Int.ofNat ((m * 3 ^ s).choose (3 ^ s))
  have hcop : IsCoprime ((3:ℤ)^4) P0 := by
    dsimp [P0,P0n,q]
    exact unit_prod_isCoprime_int_pow 3 (3^s) 4 Nat.prime_three
  have hcancel : ((3:ℤ)^4) ∣ B - B0 := by
    exact hcop.dvd_of_dvd_mul_right hmain
  dsimp [B,B0,q,q0] at hcancel
  exact dvd_neg.mp (by simpa [sub_eq_add_neg, add_comm] using hcancel)

lemma choose_mul_threepow_mod81_base (s m t : ℕ)
    (hm : 1 ≤ m) (hmt : t = m - 1) (hs : 1 ≤ s) :
    (Int.ofNat ((m * 3^s).choose (3^s))) ≡ (Int.ofNat ((m * 3).choose 3)) [ZMOD ((3:ℤ)^4)] := by
  revert hs
  induction s with
  | zero => intro hs; omega
  | succ s ih =>
      intro hs
      by_cases hsz : s = 0
      · subst s
        simp
      · have hspos : 1 ≤ s := by omega
        have hstab := choose_mul_threepow_stable_mod81 (s+1) m t hm hmt (by omega)
        exact hstab.trans (ih hspos)

lemma coeff_cancel_three (s : ℕ) (hs : 1 ≤ s) :
    ((3:ℤ)^4) ∣
      2 * (Int.ofNat ((3 * 3^s).choose (3^s)))^2 - 9 * (Int.ofNat ((2 * 3^s).choose (3^s))) := by
  have hB := choose_mul_threepow_mod81_base s 3 2 (by omega) (by rfl) hs
  have hD := choose_mul_threepow_mod81_base s 2 1 (by omega) (by rfl) hs
  rw [Int.modEq_iff_dvd] at hB hD
  have hB' : (3:ℤ)^4 ∣ Int.ofNat ((3 * 3 ^ s).choose (3 ^ s)) - Int.ofNat ((3*3).choose 3) := dvd_neg.mp (by simpa using hB)
  have hD' : (3:ℤ)^4 ∣ Int.ofNat ((2 * 3 ^ s).choose (3 ^ s)) - Int.ofNat ((2*3).choose 3) := dvd_neg.mp (by simpa using hD)
  norm_num at hB' hD' ⊢
  obtain ⟨u, hu⟩ := hB'
  obtain ⟨v, hv⟩ := hD'
  use (172 + 336*u + 2*((3:ℤ)^4)*u^2 - 9*v)
  have h93 : (((Nat.choose 9 3) : ℕ) : ℤ) = 84 := by norm_num [Nat.choose]
  have h63 : (((Nat.choose 6 3) : ℕ) : ℤ) = 20 := by norm_num [Nat.choose]
  have hBexpr : (((3 * 3 ^ s).choose (3 ^ s) : ℕ) : ℤ) = 84 + 81*u := by
    linarith
  have hDexpr : (((2 * 3 ^ s).choose (3 ^ s) : ℕ) : ℤ) = 20 + 81*v := by
    linarith
  rw [hBexpr, hDexpr]
  norm_num
  ring

lemma dvd_mul_right_of_dvd_int {m x y : ℤ} (h : m ∣ x) : m*y ∣ y*x := by
  rcases h with ⟨k, hk⟩
  use k
  rw [hk]
  ring

lemma prod_diff_first_mod_my (s : Finset ℕ) (A B : ℕ → ℤ) (m y : ℤ)
    (hy : m ∣ y) (hAB : ∀ i ∈ s, m ∣ A i * B i - 1) :
    m*y ∣
      ((∏ i ∈ s, (A i + 6*y)) - (∏ i ∈ s, (A i + 2*y)))
        - 4*y*(∏ i ∈ s, A i)*(∑ i ∈ s, B i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s has ih =>
      rw [Finset.prod_insert has, Finset.prod_insert has, Finset.prod_insert has, Finset.sum_insert has]
      set F6 := ∏ i ∈ s, (A i + 6*y)
      set F2 := ∏ i ∈ s, (A i + 2*y)
      set P := ∏ i ∈ s, A i
      set S := ∑ i ∈ s, B i
      have hABs : ∀ i ∈ s, m ∣ A i * B i - 1 := by intro i hi; exact hAB i (by simp [hi])
      have hABa : m ∣ A a * B a - 1 := hAB a (by simp)
      have ih' := ih hABs
      have hF6P : m ∣ F6 - P := by
        dsimp [F6,P]
        apply prod_congr_dvd s A (fun _ => 6*y) m
        intro i hi
        exact (hy.mul_left 6)
      have hPAB : m ∣ P - A a * B a * P := by
        rcases hABa with ⟨k,hk⟩
        use -P*k
        calc
          P - A a * B a * P = -P*(A a * B a - 1) := by ring
          _ = -P*(m*k) := by rw [hk]
          _ = m*(-P*k) := by ring
      have hF6AB : m ∣ F6 - A a * B a * P := by
        have := dvd_add hF6P hPAB
        simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using this
      have hterm1 : m*y ∣ A a * (((F6 - F2) - 4*y*P*S)) := ih'.mul_left (A a)
      have hF6F2' : m ∣ F6 - F2 := by
        dsimp [F6,F2]
        have hd : m ∣ (∏ i ∈ s, (A i + 6*y)) - (∏ i ∈ s, (A i + 2*y)) := by
          have h0 := prod_linear_diff_dvd s A y 6 2
          exact dvd_trans hy h0
        simpa using hd
      have hterm2 : m*y ∣ 4*y*(F6 - A a * B a * P) := by
        rcases hF6AB with ⟨k,hk⟩
        use 4*k
        rw [hk]
        ring
      have hterm3 : m*y ∣ 2*y*(F6 - F2) := by
        rcases hF6F2' with ⟨k,hk⟩
        use 2*k
        rw [hk]
        ring
      have hdecomp :
        ((A a + 6*y) * F6 - (A a + 2*y) * F2) - 4*y*(A a * P)*(B a + S)
        = A a * ((F6 - F2) - 4*y*P*S) + 4*y*(F6 - A a*B a*P) + 2*y*(F6-F2) := by ring
      rw [hdecomp]
      exact dvd_add (dvd_add hterm1 hterm2) hterm3

lemma prod_second_difference_mod_my2 (s : Finset ℕ) (A B : ℕ → ℤ) (m y : ℤ)
    (hy : m ∣ y) (hAB : ∀ i ∈ s, m ∣ A i * B i - 1) :
    m*y^2 ∣
      ((∏ i ∈ s, (A i + 6*y)) - 3*(∏ i ∈ s, (A i + 2*y)) + 2*(∏ i ∈ s, A i))
        - 12*(∏ i ∈ s, A i)*y^2*((∑ i ∈ s, B i)^2 - ∑ i ∈ s, (B i)^2) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s has ih =>
      rw [Finset.prod_insert has, Finset.prod_insert has, Finset.prod_insert has, Finset.sum_insert has, Finset.sum_insert has]
      set F6 := ∏ i ∈ s, (A i + 6*y)
      set F2 := ∏ i ∈ s, (A i + 2*y)
      set P := ∏ i ∈ s, A i
      set S := ∑ i ∈ s, B i
      set Q := ∑ i ∈ s, (B i)^2
      have hABs : ∀ i ∈ s, m ∣ A i * B i - 1 := by intro i hi; exact hAB i (by simp [hi])
      have hABa : m ∣ A a * B a - 1 := hAB a (by simp)
      have ih' := ih hABs
      have hfirst := prod_diff_first_mod_my s A B m y hy hABs
      -- promote first-difference congruence by multiplying with 6*y
      have hterm_first : m*y^2 ∣ 6*y*(((F6 - F2) - 4*y*P*S)) := by
        rcases hfirst with ⟨k,hk⟩
        use 6*k
        rw [hk]
        ring
      have hone : m ∣ A a * B a - 1 := hABa
      have hcorr : m*y^2 ∣ 24*P*y^2*S*(1 - A a*B a) := by
        rcases hone with ⟨k,hk⟩
        use -24*P*S*k
        have h1 : 1 - A a*B a = -(A a*B a - 1) := by ring
        rw [h1, hk]
        ring
      have hterm_ind : m*y^2 ∣ A a * (((F6 - 3*F2 + 2*P) - 12*P*y^2*(S^2 - Q))) := by
        dsimp [F6,F2,P,S,Q] at ih'
        exact ih'.mul_left (A a)
      have hdecomp :
        (((A a + 6*y)*F6) - 3*((A a + 2*y)*F2) + 2*(A a*P))
          - 12*(A a*P)*y^2*((B a + S)^2 - ((B a)^2 + Q))
        = A a*((F6 - 3*F2 + 2*P) - 12*P*y^2*(S^2 - Q))
          + 6*y*((F6 - F2) - 4*y*P*S)
          + 24*P*y^2*S*(1 - A a*B a) := by ring
      rw [hdecomp]
      exact dvd_add (dvd_add hterm_ind hterm_first) hcorr

lemma unit_sum_fourth_zmod_prime_power (p r : ℕ) (hp : Nat.Prime p) (hp7 : 7 ≤ p) :
    (letI : Fintype (ZMod (p^r))ˣ := Fintype.ofFinite _
     ∑ x : (ZMod (p^r))ˣ, ((x : (ZMod (p^r))ˣ) : ZMod (p^r)) ^ 4) = 0 := by
  classical
  let n := p^r
  letI : Fintype (ZMod n)ˣ := Fintype.ofFinite _
  have hcop2 : Nat.Coprime 2 n := by
    dsimp [n]
    exact (Nat.coprime_of_lt_prime (by decide : (2:ℕ) ≠ 0) (by omega) hp).symm.pow_right r
  let u : (ZMod n)ˣ := ZMod.unitOfCoprime 2 hcop2
  let S : ZMod n := ∑ x : (ZMod n)ˣ, (x : ZMod n)^4
  have hSperm : S = ∑ x : (ZMod n)ˣ, ((u * x : (ZMod n)ˣ) : ZMod n)^4 := by
    dsimp [S]
    symm
    exact Fintype.sum_equiv (Equiv.mulLeft u) (fun x : (ZMod n)ˣ => ((u * x : (ZMod n)ˣ) : ZMod n)^4)
      (fun y : (ZMod n)ˣ => (y : ZMod n)^4) (by intro x; rfl)
  have hS : S = (u : ZMod n)^4 * S := by
    calc
      S = ∑ x : (ZMod n)ˣ, ((u * x : (ZMod n)ˣ) : ZMod n)^4 := hSperm
      _ = ∑ x : (ZMod n)ˣ, ((u : ZMod n) * (x : ZMod n))^4 := by rfl
      _ = ∑ x : (ZMod n)ˣ, (u : ZMod n)^4 * (x : ZMod n)^4 := by
        apply Finset.sum_congr rfl; intro x hx; ring
      _ = (u : ZMod n)^4 * S := by simp [S, Finset.mul_sum]
  have hzero : (((u : ZMod n)^4 - 1) * S) = 0 := by
    rw [sub_mul, one_mul, ← hS, sub_self]
  have hunit15 : IsUnit (((u : ZMod n)^4 - 1) : ZMod n) := by
    have hu : (u : ZMod n) = (2 : ZMod n) := by simp [u, ZMod.coe_unitOfCoprime]
    rw [hu]; norm_num
    have hcop15 : Nat.Coprime 15 n := by
      dsimp [n]
      have hpnot3 : ¬ p ∣ 3 := by
        intro h; have := Nat.le_of_dvd (by decide : 0 < 3) h; omega
      have hpnot5 : ¬ p ∣ 5 := by
        intro h; have := Nat.le_of_dvd (by decide : 0 < 5) h; omega
      have hcop3 : Nat.Coprime 3 (p^r) := hp.coprime_pow_of_not_dvd hpnot3
      have hcop5 : Nat.Coprime 5 (p^r) := hp.coprime_pow_of_not_dvd hpnot5
      simpa [show (15:ℕ)=3*5 by norm_num] using hcop3.mul_left hcop5
    simpa [ZMod.coe_unitOfCoprime] using (ZMod.unitOfCoprime 15 hcop15).isUnit
  exact hunit15.mul_right_eq_zero.mp hzero

lemma unit_sum_inv_fourth_zmod_prime_power (p r : ℕ) (hp : Nat.Prime p) (hp7 : 7 ≤ p) :
    (letI : Fintype (ZMod (p^r))ˣ := Fintype.ofFinite _
     ∑ x : (ZMod (p^r))ˣ, (((x⁻¹ : (ZMod (p^r))ˣ) : ZMod (p^r)) ^ 4)) = 0 := by
  classical
  let n := p^r
  letI : Fintype (ZMod n)ˣ := Fintype.ofFinite _
  have h := unit_sum_fourth_zmod_prime_power p r hp hp7
  change (∑ x : (ZMod n)ˣ, ((x⁻¹ : (ZMod n)ˣ) : ZMod n)^4) = 0
  calc
    (∑ x : (ZMod n)ˣ, ((x⁻¹ : (ZMod n)ˣ) : ZMod n)^4)
        = ∑ x : (ZMod n)ˣ, ((x : (ZMod n)ˣ) : ZMod n)^4 := by
          exact Fintype.sum_equiv (Equiv.inv (ZMod n)ˣ) (fun x : (ZMod n)ˣ => ((x⁻¹ : (ZMod n)ˣ) : ZMod n)^4)
            (fun y : (ZMod n)ˣ => ((y : (ZMod n)ˣ) : ZMod n)^4) (by intro x; rfl)
    _ = 0 := by simpa [n] using h

lemma lower_inv_fourth_sum_zmod_zero (p r : ℕ) (hp : Nat.Prime p) (hp7 : 7 ≤ p) (hr : 1 ≤ r) :
    (let q := p^r
     ∑ i ∈ (Finset.range (q/2)).filter (fun i => ¬ p ∣ i+1),
       (if h : p ∣ i+1 then 0 else (((ZMod.unitOfCoprime (i+1) (by dsimp [q]; exact hp.coprime_pow_of_not_dvd h))⁻¹ : (ZMod q)ˣ) : ZMod q)^4)) = 0 := by
  classical
  let q := p^r
  have hqpos : 0 < q := by dsimp [q]; exact pow_pos hp.pos r
  have hq_ne0 : q ≠ 0 := Nat.ne_of_gt hqpos
  have hq_gt1 : 1 < q := by
    dsimp [q]
    cases r with
    | zero => omega
    | succ r => exact one_lt_pow₀ (by omega) (Nat.succ_ne_zero r)
  haveI : NeZero q := ⟨hq_ne0⟩
  haveI : Fact (1 < q) := ⟨hq_gt1⟩
  haveI : Nontrivial (ZMod q) := ZMod.nontrivial q
  letI : Fintype (ZMod q)ˣ := Fintype.ofFinite _
  let f : ℕ → ZMod q := fun u =>
    if h : p ∣ u then 0 else
      (((ZMod.unitOfCoprime u (by dsimp [q]; exact hp.coprime_pow_of_not_dvd h))⁻¹ : (ZMod q)ˣ) : ZMod q)^4
  have hfull0 : (∑ i ∈ (Finset.range q).filter (fun i => ¬ p ∣ i+1), f (i+1)) = 0 := by
    have hunit := unit_sum_inv_fourth_zmod_prime_power p r hp hp7
    have htransfer := unit_sum_eq_range_filter_prime_power p r hp hr (fun x : (ZMod (p^r))ˣ => (((x⁻¹ : (ZMod (p^r))ˣ) : ZMod (p^r))^4))
    change (∑ i ∈ (Finset.range q).filter (fun i => ¬ p ∣ i+1), f (i+1)) = 0
    rw [← htransfer]
    simpa [q] using hunit
  have hpq : p ∣ q := by dsimp [q]; exact dvd_pow_self p (by omega)
  have hqodd : q % 2 = 1 := by
    have hpodd : p % 2 = 1 := by rw [hp.mod_two_eq_one_iff_ne_two]; omega
    dsimp [q]; rw [Nat.pow_mod]; simp [hpodd]
  have hpair := sum_units_pair (M:=ZMod q) p q hpq hqodd f
  have hupper_eq : ∀ i ∈ (Finset.range (q/2)).filter (fun i => ¬ p ∣ i+1), f (q-(i+1)) = f (i+1) := by
    intro i hi
    simp only [f]
    simp only [mem_filter, mem_range] at hi
    have hiq : i + 1 < q := by omega
    have hnoti : ¬ p ∣ i+1 := hi.2
    have hnotq : ¬ p ∣ q - (i+1) := by
      intro hd; apply hnoti
      have hsub : q - (q - (i+1)) = i+1 := by omega
      simpa [hsub] using Nat.dvd_sub hpq hd
    rw [dif_neg hnotq, dif_neg hnoti]
    have hcast : ((q - (i+1) : ℕ) : ZMod q) = - ((i+1 : ℕ) : ZMod q) := by
      apply eq_neg_of_add_eq_zero_left
      rw [← Nat.cast_add]
      have hadd : q - (i+1) + (i+1) = q := by omega
      rw [hadd]
      exact CharP.cast_eq_zero (ZMod q) q
    let u : (ZMod q)ˣ := ZMod.unitOfCoprime (i+1) (hp.coprime_pow_of_not_dvd hnoti)
    let negUnit : (ZMod q)ˣ :=
      ⟨-(u : ZMod q), -((u⁻¹ : (ZMod q)ˣ) : ZMod q), by simp, by simp⟩
    have hunitneg : ZMod.unitOfCoprime (q - (i+1)) (hp.coprime_pow_of_not_dvd hnotq) = negUnit := by
      apply Units.ext
      dsimp [negUnit, u]
      simpa [ZMod.coe_unitOfCoprime] using hcast
    rw [hunitneg]
    dsimp [negUnit]
    ring
  have hfull_pair0 : (∑ i ∈ (Finset.range (q/2)).filter (fun i => ¬ p ∣ i+1), (f (i+1) + f (q-(i+1)))) = 0 := by
    rw [← hpair, hfull0]
  have hlower2 : (2 : ZMod q) * (∑ i ∈ (Finset.range (q/2)).filter (fun i => ¬ p ∣ i+1), f (i+1)) = 0 := by
    rw [← hfull_pair0]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [hupper_eq i hi]
    ring
  have hunit2 : IsUnit (2 : ZMod q) := by
    change IsUnit ((2:ℕ) : ZMod q)
    rw [ZMod.isUnit_iff_coprime]
    dsimp [q]
    exact (Nat.coprime_of_lt_prime (by decide : (2:ℕ) ≠ 0) (by omega) hp).symm.pow_right r
  exact hunit2.mul_right_eq_zero.mp hlower2

lemma U_second_dvd_r2_pge7 (p : ℕ) (hp : Nat.Prime p) (hp7 : 7 ≤ p) :
    ((p:ℤ)^9) ∣
      (∏ i ∈ (Finset.range (p^2)).filter (fun i => ¬ p ∣ i+1), ((i+1:ℤ) + 2*(p^2:ℤ)))
      - 3 * (∏ i ∈ (Finset.range (p^2)).filter (fun i => ¬ p ∣ i+1), ((i+1:ℤ) + 1*(p^2:ℤ)))
      + 2 * (∏ i ∈ (Finset.range (p^2)).filter (fun i => ¬ p ∣ i+1), ((i+1:ℤ))) := by
  classical
  let q := p^2
  have hp5 : 5 ≤ p := by omega
  have hpq : p ∣ q := by dsimp [q]; exact dvd_pow_self p (by omega)
  have hqodd : q % 2 = 1 := by
    have hpodd : p % 2 = 1 := by rw [hp.mod_two_eq_one_iff_ne_two]; omega
    dsimp [q]; rw [Nat.pow_mod]; simp [hpodd]
  let S := (Finset.range (q/2)).filter (fun i => ¬ p ∣ i+1)
  let A : ℕ → ℤ := fun i => (i+1:ℤ) * (q - (i+1) : ℤ)
  let B : ℕ → ℤ := fun i =>
    if h : p ∣ i+1 then 0 else
      - (((((ZMod.unitOfCoprime (i+1) (by dsimp [q]; exact hp.coprime_pow_of_not_dvd h))⁻¹ : (ZMod q)ˣ) : ZMod q)^2).valMinAbs)
  have hABq : ∀ i ∈ S, (q:ℤ) ∣ A i * B i - 1 := by
    intro i hi
    simp only [S, mem_filter, mem_range] at hi
    have hnot : ¬ p ∣ i+1 := hi.2
    have hiq : i+1 < q := by omega
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    change ((A i * B i - 1 : ℤ) : ZMod q) = 0
    simp [A, B, dif_neg hnot]
    have hcastq : ((q - (i+1) : ℕ) : ZMod q) = - ((i+1 : ℕ) : ZMod q) := by
      apply eq_neg_of_add_eq_zero_left
      rw [← Nat.cast_add]
      have hadd : q - (i+1) + (i+1) = q := by omega
      rw [hadd]
      exact CharP.cast_eq_zero (ZMod q) q
    let u : (ZMod q)ˣ := ZMod.unitOfCoprime (i+1) (hp.coprime_pow_of_not_dvd hnot)
    have hu : (u : ZMod q) = ((i+1:ℕ):ZMod q) := by simp [u, ZMod.coe_unitOfCoprime]
    have hu' : (u : ZMod q) = (i : ZMod q) + 1 := by simpa using hu
    change (-(((i : ZMod q) + 1) * (-1 + -(i : ZMod q)) * (((u⁻¹ : (ZMod q)ˣ) : ZMod q)^2)) - 1) = 0
    have hneg : (-1 + -(i : ZMod q)) = -(u : ZMod q) := by
      rw [hu']
      ring
    rw [← hu', hneg]
    ring_nf
    rw [add_comm]
    rw [← mul_pow]
    simp
  have hABp : ∀ i ∈ S, (p:ℤ) ∣ A i * B i - 1 := by
    intro i hi
    exact dvd_trans (by exact_mod_cast hpq) (hABq i hi)
  have hSumQ : (q:ℤ) ∣ ∑ i ∈ S, B i := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    change (((∑ i ∈ S, B i : ℤ) : ZMod q) = 0)
    rw [Int.cast_sum]
    simp only [B]
    have hlower := lower_inv_sq_sum_zmod_zero p 2 hp hp5 (by omega)
    trans - (∑ i ∈ S, (if h : p ∣ i+1 then 0 else (((ZMod.unitOfCoprime (i+1) (by dsimp [q]; exact hp.coprime_pow_of_not_dvd h))⁻¹ : (ZMod q)ˣ) : ZMod q)^2))
    · rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro i hi
      by_cases h : p ∣ i+1
      · simp [h]
      · simp [h, ZMod.coe_valMinAbs]
    · rw [show (∑ i ∈ S, (if h : p ∣ i+1 then 0 else (((ZMod.unitOfCoprime (i+1) (by dsimp [q]; exact hp.coprime_pow_of_not_dvd h))⁻¹ : (ZMod q)ˣ) : ZMod q)^2)) = 0 by simpa [q,S] using hlower]
      simp
  have hSumP : (p:ℤ) ∣ ∑ i ∈ S, B i := dvd_trans (by exact_mod_cast hpq) hSumQ
  have hSqQ : (q:ℤ) ∣ ∑ i ∈ S, (B i)^2 := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    change (((∑ i ∈ S, (B i)^2 : ℤ) : ZMod q) = 0)
    rw [Int.cast_sum]
    simp only [B]
    have hlower4 := lower_inv_fourth_sum_zmod_zero p 2 hp hp7 (by omega)
    trans (∑ i ∈ S, (if h : p ∣ i+1 then 0 else (((ZMod.unitOfCoprime (i+1) (by dsimp [q]; exact hp.coprime_pow_of_not_dvd h))⁻¹ : (ZMod q)ˣ) : ZMod q)^4))
    · apply Finset.sum_congr rfl
      intro i hi
      by_cases h : p ∣ i+1
      · simp [h]
      · simp [h, ZMod.coe_valMinAbs]
        ring
    · simpa [q,S] using hlower4
  have hSqP : (p:ℤ) ∣ ∑ i ∈ S, (B i)^2 := dvd_trans (by exact_mod_cast hpq) hSqQ
  have hT : (p:ℤ) ∣ (∑ i ∈ S, B i)^2 - ∑ i ∈ S, (B i)^2 := by
    rcases hSumP with ⟨u, hu⟩
    rcases hSqP with ⟨v, hv⟩
    use u*(∑ i ∈ S, B i) - v
    rw [hu, hv]
    ring
  let y : ℤ := (q:ℤ)^2
  have hy : (p:ℤ) ∣ y := by
    dsimp [y,q]
    use (p:ℤ)^3
    norm_num
    ring
  have hcore := prod_second_difference_mod_my2 S A B (p:ℤ) y hy hABp
  have hcorr : (p:ℤ)*y^2 ∣ 12*(∏ i ∈ S, A i)*y^2*((∑ i ∈ S, B i)^2 - ∑ i ∈ S, (B i)^2) := by
    rcases hT with ⟨k,hk⟩
    use 12*(∏ i ∈ S, A i)*k
    rw [hk]
    ring
  have hpaired : (p:ℤ)*y^2 ∣
      ((∏ i ∈ S, (A i + 6*y)) - 3*(∏ i ∈ S, (A i + 2*y)) + 2*(∏ i ∈ S, A i)) := by
    let E := ((∏ i ∈ S, (A i + 6*y)) - 3*(∏ i ∈ S, (A i + 2*y)) + 2*(∏ i ∈ S, A i))
    let C := 12*(∏ i ∈ S, A i)*y^2*((∑ i ∈ S, B i)^2 - ∑ i ∈ S, (B i)^2)
    change (p:ℤ)*y^2 ∣ E
    change (p:ℤ)*y^2 ∣ E - C at hcore
    change (p:ℤ)*y^2 ∣ C at hcorr
    rcases hcore with ⟨u, hu⟩
    rcases hcorr with ⟨v, hv⟩
    use u+v
    have : E = (E - C) + C := by ring
    rw [this, hu, hv]
    ring
  have hP2 := paired_product_identity p q 2 hpq hqodd
  have hP1 := paired_product_identity p q 1 hpq hqodd
  have hP0 := paired_product_identity p q 0 hpq hqodd
  have hrewrite :
      ((∏ i ∈ S, (A i + 6*y)) - 3*(∏ i ∈ S, (A i + 2*y)) + 2*(∏ i ∈ S, A i)) =
      (∏ i ∈ (Finset.range q).filter (fun i => ¬ p ∣ i+1), ((i+1:ℤ) + 2*(q:ℤ)))
      - 3 * (∏ i ∈ (Finset.range q).filter (fun i => ¬ p ∣ i+1), ((i+1:ℤ) + 1*(q:ℤ)))
      + 2 * (∏ i ∈ (Finset.range q).filter (fun i => ¬ p ∣ i+1), ((i+1:ℤ))) := by
    have hP2' : (∏ i ∈ (Finset.range q).filter (fun i => ¬ p ∣ i+1), ((i+1:ℤ) + 2*(q:ℤ))) = ∏ i ∈ S, (A i + 6*y) := by
      simpa [S,A,y] using hP2
    have hP1' : (∏ i ∈ (Finset.range q).filter (fun i => ¬ p ∣ i+1), ((i+1:ℤ) + 1*(q:ℤ))) = ∏ i ∈ S, (A i + 2*y) := by
      simpa [S,A,y] using hP1
    have hP0' : (∏ i ∈ (Finset.range q).filter (fun i => ¬ p ∣ i+1), ((i+1:ℤ))) = ∏ i ∈ S, A i := by
      simpa [S,A] using hP0
    rw [← hP2', ← hP1', ← hP0']
  have hmod : (p:ℤ)*y^2 = (p:ℤ)^9 := by
    dsimp [y,q]
    norm_num
    rw [← pow_mul]
    ring
  rw [← hmod]
  rw [hrewrite] at hpaired
  simpa [q] using hpaired

lemma assemble_core_three (r : ℕ) (B0 D0 P0 P1 P2 : ℤ) (hr : 2 ≤ r)
    (hD1 : (3 : ℤ) ^ (3*r-1) ∣ P1 - P0)
    (hD2 : (3 : ℤ) ^ (3*r+3) ∣ P2 - 3*P1 + 2*P0)
    (hC : (3 : ℤ)^4 ∣ 2*B0^2 - 9*D0)
    (hP20 : (3 : ℤ)^(3*r-1) ∣ P2 - P0) :
    (3 : ℤ) ^ (3*r+3) ∣
      (B0^2 * (P2^2 - P0^2) - 27 * D0 * P0 * (P1 - P0)) := by
  let pp : ℤ := (3 : ℤ)
  let D1 := P1 - P0
  let D2 := P2 - 3*P1 + 2*P0
  have hP2 : P2 - P0 = 3*D1 + D2 := by dsimp [D1,D2]; ring
  have hexp : B0^2 * (P2^2 - P0^2) - 27 * D0 * P0 * (P1 - P0)
      = D1 * (3*B0^2*(P2+P0) - 27*D0*P0) + D2 * (B0^2*(P2+P0)) := by
    dsimp [D1,D2]
    ring
  rw [hexp]
  apply dvd_add
  · have hcoef : pp^4 ∣ (3*B0^2*(P2+P0) - 27*D0*P0) := by
      have hrewrite : 3*B0^2*(P2+P0) - 27*D0*P0 =
          3*P0*(2*B0^2 - 9*D0) + 3*B0^2*(P2-P0) := by ring
      rw [hrewrite]
      apply dvd_add
      · exact hC.mul_left (3*P0)
      · have hp20small : pp^4 ∣ P2-P0 := by
          exact dvd_trans (pow_dvd_pow pp (by omega : 4 ≤ 3*r-1)) hP20
        exact hp20small.mul_left (3*B0^2)
    have hpowmul : (3:ℤ)^(3*r+3) ∣ (3:ℤ)^(3*r-1) * (3:ℤ)^4 := by
      rw [← pow_add]
      have he : 3*r - 1 + 4 = 3*r + 3 := by omega
      rw [he]
    exact dvd_trans hpowmul (mul_dvd_mul hD1 hcoef)
  · exact hD2.mul_right (B0^2*(P2+P0))

lemma final_from_core (p r : ℕ) (hp : Nat.Prime p) (hr : 1 ≤ r)
    (hcore : (p:ℤ)^(3*r+3) ∣
      ((Int.ofNat ((3 * p^(r-1)).choose (p^(r-1))))^2 *
        (((∏ i ∈ (Finset.range (p^r)).filter (fun i => ¬ p ∣ i+1), ((i+1:ℤ) + 2*(p^r:ℤ)))^2) -
         ((∏ i ∈ (Finset.range (p^r)).filter (fun i => ¬ p ∣ i+1), ((i+1:ℤ)))^2))
        - 27 * (Int.ofNat ((2 * p^(r-1)).choose (p^(r-1)))) *
          (∏ i ∈ (Finset.range (p^r)).filter (fun i => ¬ p ∣ i+1), ((i+1:ℤ))) *
          ((∏ i ∈ (Finset.range (p^r)).filter (fun i => ¬ p ∣ i+1), ((i+1:ℤ) + 1*(p^r:ℤ))) -
           (∏ i ∈ (Finset.range (p^r)).filter (fun i => ¬ p ∣ i+1), ((i+1:ℤ)))))) :
    a (p^r) ≡ a (p^(r-1)) [ZMOD ((p:ℤ)^(3*r+3))] := by
  classical
  let q := p^r
  let q0 := p^(r-1)
  let B : ℤ := Int.ofNat ((3*q).choose q)
  let B0 : ℤ := Int.ofNat ((3*q0).choose q0)
  let D : ℤ := Int.ofNat ((2*q).choose q)
  let D0 : ℤ := Int.ofNat ((2*q0).choose q0)
  let P0 : ℤ := ∏ i ∈ (Finset.range q).filter (fun i => ¬ p ∣ i+1), ((i+1:ℤ))
  let P1 : ℤ := ∏ i ∈ (Finset.range q).filter (fun i => ¬ p ∣ i+1), ((i+1:ℤ) + 1*(q:ℤ))
  let P2 : ℤ := ∏ i ∈ (Finset.range q).filter (fun i => ¬ p ∣ i+1), ((i+1:ℤ) + 2*(q:ℤ))
  have hqeq : p*q0 = q := by dsimp [q,q0]; exact pow_mul_pow_sub_one p r hr
  have hquot3_nat := quotient_identity 3 p q0 (by omega) hp.pos
  have hquot2_nat := quotient_identity 2 p q0 (by omega) hp.pos
  have hquotB : B * P0 = B0 * P2 := by
    dsimp [B,B0,P0,P2]
    norm_cast
    simpa [q,q0,hqeq, Nat.cast_add, Nat.cast_mul, add_comm, add_left_comm, add_assoc, mul_assoc] using hquot3_nat
  have hquotD : D * P0 = D0 * P1 := by
    dsimp [D,D0,P0,P1]
    norm_cast
    simpa [q,q0,hqeq, Nat.cast_add, Nat.cast_mul, add_comm, add_left_comm, add_assoc, mul_assoc] using hquot2_nat
  let N : ℤ := (p:ℤ)^(3*r+3)
  have hmul : N ∣ ((B^2 - 27*D) - (B0^2 - 27*D0)) * P0^2 := by
    have hEq : ((B^2 - 27*D) - (B0^2 - 27*D0)) * P0^2 =
        (B0^2 * (P2^2 - P0^2) - 27 * D0 * P0 * (P1 - P0)) := by
      calc
        ((B^2 - 27*D) - (B0^2 - 27*D0)) * P0^2
            = (B*P0)^2 - 27*(D*P0)*P0 - B0^2*P0^2 + 27*D0*P0^2 := by ring
        _ = (B0*P2)^2 - 27*(D0*P1)*P0 - B0^2*P0^2 + 27*D0*P0^2 := by rw [hquotB, hquotD]
        _ = B0^2 * (P2^2 - P0^2) - 27 * D0 * P0 * (P1 - P0) := by ring
    rw [hEq]
    simpa [N,B0,D0,P0,P1,P2,q,q0] using hcore
  have hcopP : IsCoprime N P0 := by
    have h := unit_prod_isCoprime_int_pow p (p^r) (3*r+3) hp
    dsimp [N,P0,q] at h ⊢
    convert h using 1
    norm_cast
  have hcopP2 : IsCoprime N (P0^2) := by simpa [pow_two] using hcopP.mul_right hcopP
  have hdiff : N ∣ ((B^2 - 27*D) - (B0^2 - 27*D0)) := by
    exact hcopP2.dvd_of_dvd_mul_left (by simpa [pow_two, mul_comm, mul_left_comm, mul_assoc] using hmul)
  rw [Int.modEq_iff_dvd]
  have hneg := dvd_neg.mpr hdiff
  dsimp [a]
  dsimp [B,B0,D,D0,q,q0] at hneg
  simpa [N, sub_eq_add_neg, add_comm, add_left_comm, add_assoc, mul_assoc] using hneg

lemma core_from_units (p r : ℕ)
    (hD1 : (p : ℤ) ^ (3*r) ∣
      (∏ i ∈ (Finset.range (p^r)).filter (fun i => ¬ p ∣ i+1), ((i+1:ℤ) + 1*(p^r:ℤ)))
      - (∏ i ∈ (Finset.range (p^r)).filter (fun i => ¬ p ∣ i+1), ((i+1:ℤ))))
    (hD2 : (p : ℤ) ^ (3*r+3) ∣
      (∏ i ∈ (Finset.range (p^r)).filter (fun i => ¬ p ∣ i+1), ((i+1:ℤ) + 2*(p^r:ℤ)))
      - 3 * (∏ i ∈ (Finset.range (p^r)).filter (fun i => ¬ p ∣ i+1), ((i+1:ℤ) + 1*(p^r:ℤ)))
      + 2 * (∏ i ∈ (Finset.range (p^r)).filter (fun i => ¬ p ∣ i+1), ((i+1:ℤ))))
    (hC : (p : ℤ)^3 ∣ 2 * (Int.ofNat ((3 * p^(r-1)).choose (p^(r-1))))^2 - 9 * (Int.ofNat ((2 * p^(r-1)).choose (p^(r-1)))))
    (hP20 : (p : ℤ)^3 ∣
      (∏ i ∈ (Finset.range (p^r)).filter (fun i => ¬ p ∣ i+1), ((i+1:ℤ) + 2*(p^r:ℤ)))
      - (∏ i ∈ (Finset.range (p^r)).filter (fun i => ¬ p ∣ i+1), ((i+1:ℤ)))) :
    (p:ℤ)^(3*r+3) ∣
      ((Int.ofNat ((3 * p^(r-1)).choose (p^(r-1))))^2 *
        (((∏ i ∈ (Finset.range (p^r)).filter (fun i => ¬ p ∣ i+1), ((i+1:ℤ) + 2*(p^r:ℤ)))^2) -
         ((∏ i ∈ (Finset.range (p^r)).filter (fun i => ¬ p ∣ i+1), ((i+1:ℤ)))^2))
        - 27 * (Int.ofNat ((2 * p^(r-1)).choose (p^(r-1)))) *
          (∏ i ∈ (Finset.range (p^r)).filter (fun i => ¬ p ∣ i+1), ((i+1:ℤ))) *
          ((∏ i ∈ (Finset.range (p^r)).filter (fun i => ¬ p ∣ i+1), ((i+1:ℤ) + 1*(p^r:ℤ))) -
           (∏ i ∈ (Finset.range (p^r)).filter (fun i => ¬ p ∣ i+1), ((i+1:ℤ))))) := by
  let P0 : ℤ := ∏ i ∈ (Finset.range (p^r)).filter (fun i => ¬ p ∣ i+1), ((i+1:ℤ))
  let P1 : ℤ := ∏ i ∈ (Finset.range (p^r)).filter (fun i => ¬ p ∣ i+1), ((i+1:ℤ) + 1*(p^r:ℤ))
  let P2 : ℤ := ∏ i ∈ (Finset.range (p^r)).filter (fun i => ¬ p ∣ i+1), ((i+1:ℤ) + 2*(p^r:ℤ))
  let B0 : ℤ := Int.ofNat ((3 * p^(r-1)).choose (p^(r-1)))
  let D0 : ℤ := Int.ofNat ((2 * p^(r-1)).choose (p^(r-1)))
  have hc := assemble_core p r B0 D0 P0 P1 P2 (by simpa [P1,P0] using hD1) (by simpa [P2,P1,P0] using hD2) (by simpa [B0,D0] using hC) (by simpa [P2,P0] using hP20)
  simpa [B0,D0,P0,P1,P2, mul_assoc] using hc

theorem oeis_357569_conjecture_0 (p r : ℕ) (hp : Nat.Prime p) (hp3 : p ≥ 3) (hr : r ≥ 2) :
  a (p ^ r) ≡ a (p ^ (r - 1)) [ZMOD ((p : ℤ) ^ (3 * r + 3))] := by
  classical
  by_cases hp_eq3 : p = 3
  · subst p
    by_cases hr_eq2 : r = 2
    · subst r
      apply final_from_core 3 2 Nat.prime_three (by omega)
      let P0 : ℤ := ∏ i ∈ (Finset.range (3^2)).filter (fun i => ¬ 3 ∣ i+1), ((i+1:ℤ))
      let P1 : ℤ := ∏ i ∈ (Finset.range (3^2)).filter (fun i => ¬ 3 ∣ i+1), ((i+1:ℤ) + 1*(3^2:ℤ))
      let P2 : ℤ := ∏ i ∈ (Finset.range (3^2)).filter (fun i => ¬ 3 ∣ i+1), ((i+1:ℤ) + 2*(3^2:ℤ))
      let B0 : ℤ := Int.ofNat ((3 * 3^(2-1)).choose (3^(2-1)))
      let D0 : ℤ := Int.ofNat ((2 * 3^(2-1)).choose (3^(2-1)))
      have hD1 : (3 : ℤ) ^ (3*2-1) ∣ P1 - P0 := by
        dsimp [P1,P0]
        simpa using U_offset_dvd_three 2 1 (by omega)
      have hD2 : (3 : ℤ) ^ (3*2+3) ∣ P2 - 3*P1 + 2*P0 := by
        dsimp [P2,P1,P0]
        decide
      have hC : (3 : ℤ)^4 ∣ 2*B0^2 - 9*D0 := by
        dsimp [B0,D0]
        simpa using coeff_cancel_three (2-1) (by omega)
      have hP20 : (3 : ℤ) ^ (3*2-1) ∣ P2 - P0 := by
        dsimp [P2,P0]
        simpa using U_offset_dvd_three 2 2 (by omega)
      have hc := assemble_core_three 2 B0 D0 P0 P1 P2 (by omega) hD1 hD2 hC hP20
      simpa [B0,D0,P0,P1,P2] using hc
    · have hr3 : 3 ≤ r := by omega
      apply final_from_core 3 r Nat.prime_three (by omega)
      let P0 : ℤ := ∏ i ∈ (Finset.range (3^r)).filter (fun i => ¬ 3 ∣ i+1), ((i+1:ℤ))
      let P1 : ℤ := ∏ i ∈ (Finset.range (3^r)).filter (fun i => ¬ 3 ∣ i+1), ((i+1:ℤ) + 1*(3^r:ℤ))
      let P2 : ℤ := ∏ i ∈ (Finset.range (3^r)).filter (fun i => ¬ 3 ∣ i+1), ((i+1:ℤ) + 2*(3^r:ℤ))
      let B0 : ℤ := Int.ofNat ((3 * 3^(r-1)).choose (3^(r-1)))
      let D0 : ℤ := Int.ofNat ((2 * 3^(r-1)).choose (3^(r-1)))
      have hD1 : (3 : ℤ) ^ (3*r-1) ∣ P1 - P0 := by
        dsimp [P1,P0]
        simpa using U_offset_dvd_three r 1 (by omega)
      have hD2 : (3 : ℤ) ^ (3*r+3) ∣ P2 - 3*P1 + 2*P0 := by
        dsimp [P2,P1,P0]
        simpa using U_second_dvd_rge3 3 r Nat.prime_three (by omega) hr3
      have hC : (3 : ℤ)^4 ∣ 2*B0^2 - 9*D0 := by
        dsimp [B0,D0]
        simpa using coeff_cancel_three (r-1) (by omega)
      have hP20 : (3 : ℤ) ^ (3*r-1) ∣ P2 - P0 := by
        dsimp [P2,P0]
        simpa using U_offset_dvd_three r 2 (by omega)
      have hc := assemble_core_three r B0 D0 P0 P1 P2 hr hD1 hD2 hC hP20
      simpa [B0,D0,P0,P1,P2] using hc
  · have hp5 : 5 ≤ p := by
      have hpne4 : p ≠ 4 := by intro h; subst p; norm_num at hp
      omega
    by_cases hr_eq2 : r = 2
    · subst r
      by_cases hp_eq5 : p = 5
      · subst p
        apply final_from_core 5 2 Nat.prime_five (by omega)
        apply core_from_units 5 2
        · simpa using U_offset_dvd_pge5 5 2 1 Nat.prime_five (by omega) (by omega)
        · decide
        · simpa using coeff_cancel_pge5 5 1 Nat.prime_five (by omega)
        · have hoff := U_offset_dvd_pge5 5 2 2 Nat.prime_five (by omega) (by omega)
          exact dvd_trans (pow_dvd_pow (5:ℤ) (by omega : 3 ≤ 3*2)) hoff
      · have hpne6 : p ≠ 6 := by intro h; subst p; norm_num at hp
        have hp7 : 7 ≤ p := by omega
        apply final_from_core p 2 hp (by omega)
        apply core_from_units p 2
        · simpa using U_offset_dvd_pge5 p 2 1 hp hp5 (by omega)
        · simpa using U_second_dvd_r2_pge7 p hp hp7
        · simpa using coeff_cancel_pge5 p 1 hp hp5
        · have hoff := U_offset_dvd_pge5 p 2 2 hp hp5 (by omega)
          exact dvd_trans (pow_dvd_pow (p:ℤ) (by omega : 3 ≤ 3*2)) hoff
    · have hr3 : 3 ≤ r := by omega
      apply final_from_core p r hp (by omega)
      apply core_from_units p r
      · simpa using U_offset_dvd_pge5 p r 1 hp hp5 (by omega)
      · simpa using U_second_dvd_rge3 p r hp (by omega) hr3
      · simpa using coeff_cancel_pge5 p (r-1) hp hp5
      · have hoff := U_offset_dvd_pge5 p r 2 hp hp5 (by omega)
        exact dvd_trans (pow_dvd_pow (p:ℤ) (by omega : 3 ≤ 3*r)) hoff
