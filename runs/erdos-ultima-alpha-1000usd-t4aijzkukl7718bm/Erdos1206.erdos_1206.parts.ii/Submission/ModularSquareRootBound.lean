import FormalConjecturesUtil

/-! An elementary divisor-function bound for square roots modulo a positive
integer. No primality, squarefreeness, or factorization assumptions are used. -/
namespace Erdos1206.ModularSquareRootBound
open Finset
open scoped Classical

noncomputable def roots (m D : ℕ) : Finset ℕ :=
  (range m).filter (fun r => Nat.ModEq m (r^2) D)

private lemma gcd_root_dvd {m D r : ℕ} (hr : Nat.ModEq m (r^2) D) :
    Nat.gcd m r ∣ Nat.gcd m D := by
  have hd : Nat.gcd m r ∣ r^2 := dvd_pow (Nat.gcd_dvd_right m r) (by decide : 2≠0)
  exact Nat.dvd_gcd (Nat.gcd_dvd_left m r)
    ((hr.dvd_iff (Nat.gcd_dvd_left m r)).mp hd)

private lemma gcd_twice_root_bound {m D r : ℕ} (hm : 0 < m)
    (hr : Nat.ModEq m (r^2) D) :
    Nat.gcd m (2*r) ≤ 2*Nat.gcd m D := by
  have hh : Nat.gcd m (2*r) ∣ Nat.gcd m 2 * Nat.gcd m r := by
    simpa only [gcd_eq_nat_gcd] using gcd_mul_dvd_mul_gcd m 2 r
  have hg : Nat.gcd m 2 * Nat.gcd m r ∣ 2*Nat.gcd m D :=
    Nat.mul_dvd_mul (Nat.gcd_dvd_right m 2) (gcd_root_dvd hr)
  exact Nat.le_of_dvd (by positivity) (hh.trans hg)

private lemma root_complement_divisor {m D r t : ℕ}
    (hm : 0 < m) (hrt : r≤t)
    (hr : Nat.ModEq m (r^2) D) (ht : Nat.ModEq m (t^2) D) :
    m / Nat.gcd m (t-r) ∣ t+r := by
  let g := Nat.gcd m (t-r)
  have hg : 0 < g := Nat.gcd_pos_of_pos_left _ hm
  have hgm : g ∣ m := Nat.gcd_dvd_left _ _
  have hgt : g ∣ t-r := Nat.gcd_dvd_right _ _
  have hsq : m ∣ t^2-r^2 :=
    (Nat.modEq_iff_dvd' (Nat.pow_le_pow_left hrt 2)).mp (hr.trans ht.symm)
  have he : t^2-r^2=(t-r)*(t+r) := by
    have ha : t-r+r=t := Nat.sub_add_cancel hrt
    nlinarith [Nat.sub_add_cancel (Nat.pow_le_pow_left hrt 2)]
  rw [he] at hsq
  have hc := Nat.coprime_div_gcd_div_gcd (Nat.gcd_pos_of_pos_left (t-r) hm)
  have hd : m/g ∣ ((t-r)/g)*(t+r) := by
    apply Nat.dvd_of_mul_dvd_mul_left hg
    calc
      g*(m/g) = m := Nat.mul_div_cancel' hgm
      _ ∣ (t-r)*(t+r) := hsq
      _ = g*(((t-r)/g)*(t+r)) := by rw [←mul_assoc,Nat.mul_div_cancel' hgt]
  exact hc.dvd_of_dvd_mul_left hd

/-- The number of square roots of D modulo m is bounded in terms of the
ordinary divisor count and gcd(m,D). -/
theorem roots_card_le {m D : ℕ} (hm : 0 < m) :
    (roots m D).card ≤ 2*Nat.gcd m D*m.divisors.card := by
  classical
  by_cases hn : (roots m D).Nonempty
  · let r := (roots m D).min' hn
    have hrmem : r ∈ roots m D := min'_mem _ hn
    have hr : Nat.ModEq m (r^2) D := (mem_filter.mp hrmem).2
    let G := 2*Nat.gcd m D
    let f (t : ℕ) := (Nat.gcd m (t-r), t/Nat.lcm (Nat.gcd m (t-r))
      (m/Nat.gcd m (t-r)))
    have hrt (t : ℕ) (ht : t ∈ roots m D) : r≤t := min'_le _ _ ht
    have hprops (t : ℕ) (ht : t ∈ roots m D) :
        let g := Nat.gcd m (t-r)
        0 < g ∧ g∣m ∧ 0 < m/g ∧
        Nat.gcd g (m/g) ≤ G ∧
        g∣t-r ∧ m/g∣t+r := by
      let g := Nat.gcd m (t-r)
      have hg : 0 < g := Nat.gcd_pos_of_pos_left _ hm
      have hgm : g∣m := Nat.gcd_dvd_left _ _
      have hgt : g∣t-r := Nat.gcd_dvd_right _ _
      have hcomp : m/g∣t+r := root_complement_divisor hm (hrt t ht) hr (mem_filter.mp ht).2
      have hhpos : 0 < m/g := Nat.div_pos (Nat.le_of_dvd hm hgm) hg
      have hkm : Nat.gcd g (m/g) ∣ m := (Nat.gcd_dvd_left _ _).trans hgm
      have hkr : Nat.gcd g (m/g) ∣ 2*r := by
        have h1 := (Nat.gcd_dvd_left g (m/g)).trans hgt
        have h2 := (Nat.gcd_dvd_right g (m/g)).trans hcomp
        have he : (t+r)-(t-r)=2*r := by have := hrt t ht; omega
        rw [←he]
        exact Nat.dvd_sub h2 h1
      have hk : Nat.gcd g (m/g) ≤ G := by
        exact (Nat.le_of_dvd (Nat.gcd_pos_of_pos_left _ hm) (Nat.dvd_gcd hkm hkr)).trans
          (gcd_twice_root_bound hm hr)
      exact ⟨hg,hgm,hhpos,hk,hgt,hcomp⟩
    have hmap : Set.MapsTo f (roots m D) ((m.divisors ×ˢ range G : Finset (ℕ × ℕ)) : Set (ℕ × ℕ)) := by
      intro t ht
      obtain ⟨hg,hgm,hhpos,hk,_,_⟩ := hprops t ht
      have htlt : t < m := mem_range.mp (mem_filter.mp ht).1
      let g := Nat.gcd m (t-r)
      have hlpos : 0 < Nat.lcm g (m/g) := Nat.lcm_pos hg hhpos
      have he : Nat.gcd g (m/g)*Nat.lcm g (m/g)=m := by
        rw [Nat.gcd_mul_lcm,Nat.mul_div_cancel' hgm]
      have hquot : t/Nat.lcm g (m/g)  <  Nat.gcd g (m/g) := by
        apply (Nat.div_lt_iff_lt_mul hlpos).mpr
        rwa [he]
      change (g,t/Nat.lcm g (m/g)) ∈ (m.divisors ×ˢ range G : Finset (ℕ × ℕ))
      exact mem_product.mpr ⟨Nat.mem_divisors.mpr ⟨hgm,hm.ne'⟩,
        mem_range.mpr (hquot.trans_le hk)⟩
    have hinj : Set.InjOn f (roots m D) := by
      intro t ht t' ht' heq
      have hgEq := congrArg Prod.fst heq
      have hqEq := congrArg Prod.snd heq
      dsimp [f] at hgEq hqEq
      obtain ⟨hg,hgm,hhpos,_,hgt,hht⟩ := hprops t ht
      obtain ⟨_,_,_,_,hgt',hht'⟩ := hprops t' ht'
      rw [←hgEq] at hgt' hht' hqEq
      let g := Nat.gcd m (t-r)
      have hmodg : Nat.ModEq g t t' := by
        exact ((Nat.modEq_iff_dvd' (hrt t ht)).mpr hgt).symm.trans
          ((Nat.modEq_iff_dvd' (hrt t' ht')).mpr hgt')
      have hmodh : Nat.ModEq (m/g) t t' := by
        have h1 := Nat.modEq_zero_iff_dvd.mpr hht
        have h2 := Nat.modEq_zero_iff_dvd.mpr hht'
        exact Nat.ModEq.add_right_cancel (Nat.ModEq.refl r) (h1.trans h2.symm)
      have hmod : Nat.ModEq (Nat.lcm g (m/g)) t t' := by
        exact Nat.mod_lcm hmodg hmodh
      have h₁ := Nat.mod_add_div t (Nat.lcm g (m/g))
      have h₂ := Nat.mod_add_div t' (Nat.lcm g (m/g))
      change t%Nat.lcm g (m/g)=t'%Nat.lcm g (m/g) at hmod
      change t/Nat.lcm g (m/g)=t'/Nat.lcm g (m/g) at hqEq
      rw [hqEq,hmod] at h₁
      omega
    have hh := card_le_card_of_injOn f hmap hinj
    simpa only [card_product,card_range,G,Nat.mul_comm m.divisors.card] using hh
  · simp only [Finset.not_nonempty_iff_eq_empty.mp hn,card_empty,Nat.zero_le]

#print axioms roots_card_le
end Erdos1206.ModularSquareRootBound
