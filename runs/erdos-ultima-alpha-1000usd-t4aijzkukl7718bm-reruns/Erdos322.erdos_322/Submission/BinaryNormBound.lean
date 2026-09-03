import Submission.DivisorBound

/-! Bounds for binary positive definite norm equations. -/
namespace Erdos322Research

private lemma square_roots_same_gcd {n a r s : ℕ} (hn : 0 < n)
    (hr : r ^ 2 ≡ a ^ 2 [MOD n]) (hs : s ^ 2 ≡ a ^ 2 [MOD n])
    (hg : n.gcd (r + a) = n.gcd (s + a)) :
    r ≡ s [MOD n / n.gcd (2 * a)] := by
  let g := n.gcd (r + a)
  have hqr : r ≡ a [MOD n / g] := by
    apply Nat.ModEq.cancel_left_div_gcd hn
    convert hr.add_right (r * a) using 1 <;> ring
  have hqs : s ≡ a [MOD n / g] := by
    rw [show g = n.gcd (s + a) from hg]
    apply Nat.ModEq.cancel_left_div_gcd hn
    convert hs.add_right (s * a) using 1 <;> ring
  have hqrsub : ((n / g : ℕ) : ℤ) ∣ (r : ℤ) - a := by
    exact Nat.modEq_iff_dvd.mp hqr.symm
  have hqsub : ((n / g : ℕ) : ℤ) ∣ (s : ℤ) - r := by
    exact Nat.modEq_iff_dvd.mp (hqr.trans hqs.symm)
  have hgr : (g : ℤ) ∣ (r : ℤ) + a := by
    exact_mod_cast Nat.gcd_dvd_right n (r + a)
  have hgs : (g : ℤ) ∣ (s : ℤ) + a := by
    have : g ∣ s + a := by rw [show g = n.gcd (s + a) from hg]; exact Nat.gcd_dvd_right _ _
    exact_mod_cast this
  have hgsub : (g : ℤ) ∣ (s : ℤ) - r := by
    convert dvd_sub hgs hgr using 1 <;> ring
  have hprod : (g : ℤ) * (n / g : ℕ) = n := by
    exact_mod_cast Nat.mul_div_cancel' (Nat.gcd_dvd_left n (r + a))
  have h1 : (n : ℤ) ∣ ((r : ℤ) + a) * (s - r) := by
    rw [← hprod]
    exact mul_dvd_mul hgr hqsub
  have h2 : (n : ℤ) ∣ ((r : ℤ) - a) * (s - r) := by
    rw [← hprod, mul_comm]
    exact mul_dvd_mul hqrsub hgsub
  have hmul : 2 * a * r ≡ 2 * a * s [MOD n] := by
    apply Nat.modEq_iff_dvd.mpr
    convert dvd_sub h1 h2 using 1 <;> push_cast <;> ring
  exact hmul.cancel_left_div_gcd hn

/-- A root of a quadratic congruence with small derivative controls the total
number of roots, by an elementary divisor injection. -/
theorem square_congruence_count {n a K : ℕ} (hn : 0 < n)
    (hK : n.gcd (2 * a) ≤ K) :
    ((Finset.range n).filter fun r ↦ r ^ 2 ≡ a ^ 2 [MOD n]).card ≤
      n.divisors.card * K := by
  classical
  let G := n.gcd (2 * a)
  let q := n / G
  have hG : 0 < G := Nat.gcd_pos_of_pos_left _ hn
  have hdG : G ∣ n := Nat.gcd_dvd_left _ _
  have hq : 0 < q := Nat.div_pos (Nat.le_of_dvd hn hdG) hG
  have hnq : G * q = n := Nat.mul_div_cancel' hdG
  have h := Finset.card_le_card_of_injOn
    (fun r : ℕ ↦ (n.gcd (r + a), r / q))
    (s := (Finset.range n).filter fun r ↦ r ^ 2 ≡ a ^ 2 [MOD n])
    (t := n.divisors ×ˢ Finset.range K) (by
      intro r hr
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_range] at hr
      obtain ⟨hrn, hroot⟩ := hr
      refine Finset.mem_product.mpr ⟨Nat.mem_divisors.mpr ⟨Nat.gcd_dvd_left _ _, hn.ne'⟩, ?_⟩
      apply Finset.mem_range.mpr
      have hdiv : r / q < G := (Nat.div_lt_iff_lt_mul hq).mpr (by rwa [hnq])
      exact hdiv.trans_le hK)
    (by
      intro r hr s hs heq
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_range] at hr hs
      have hg := congrArg Prod.fst heq
      have hdiv := congrArg Prod.snd heq
      have hmod : r % q = s % q := square_roots_same_gcd hn
        hr.2 hs.2 hg
      have h1 := Nat.div_add_mod r q
      have h2 := Nat.div_add_mod s q
      change r / q = s / q at hdiv
      rw [hdiv] at h1
      omega)
  simpa using h


def binaryNormSolutions (d n : ℕ) : Finset (ℕ × ℕ) :=
  ((Finset.range (n + 1)) ×ˢ (Finset.range (n + 1))).filter
    (fun p ↦ p.1 ^ 2 + d * p.2 ^ 2 = n)

def primitiveBinaryNormSolutions (d n : ℕ) : Finset (ℕ × ℕ) :=
  (binaryNormSolutions d n).filter (fun p ↦ p.1.Coprime p.2)

private def normRoot (n : ℕ) (p : ℕ × ℕ) : ℕ :=
  ((p.1 : ZMod n) * (p.2 : ZMod n)⁻¹).val

private lemma norm_coprime_right {d n x y : ℕ}
    (h : x ^ 2 + d * y ^ 2 = n) (hc : x.Coprime y) : y.Coprime n := by
  rw [← h, show d * y ^ 2 = (d * y) * y by ring,
    Nat.coprime_add_mul_right_right]
  exact hc.symm.pow_right 2

private lemma normRoot_mul {d n x y : ℕ} (hn : 0 < n)
    (h : x ^ 2 + d * y ^ 2 = n) (hc : x.Coprime y) :
    normRoot n (x, y) * y ≡ x [MOD n] := by
  letI : NeZero n := ⟨hn.ne'⟩
  apply (ZMod.natCast_eq_natCast_iff _ _ _).mp
  have hi := ZMod.mul_inv_of_unit (y : ZMod n)
    ((ZMod.isUnit_iff_coprime _ _).mpr (norm_coprime_right h hc))
  simp only [Nat.cast_mul, normRoot, ZMod.natCast_zmod_val]
  calc
    (x : ZMod n) * (y : ZMod n)⁻¹ * y = x * (y * (y : ZMod n)⁻¹) := by ring
    _ = x := by rw [hi, mul_one]

private lemma normRoot_square {d n x y : ℕ} (hn : 0 < n)
    (h : x ^ 2 + d * y ^ 2 = n) (hc : x.Coprime y) :
    normRoot n (x, y) ^ 2 + d ≡ 0 [MOD n] := by
  have hr := normRoot_mul hn h hc
  have heq : (normRoot n (x, y) ^ 2 + d) * y ^ 2 ≡ 0 * y ^ 2 [MOD n] := by
    have hh : x ^ 2 + d * y ^ 2 ≡ 0 [MOD n] :=
      Nat.modEq_zero_iff_dvd.mpr (h ▸ dvd_refl n)
    convert ((hr.pow 2).add_right (d * y ^ 2)).trans hh using 1 <;> ring
  have hc' : n.Coprime (y ^ 2) := (norm_coprime_right h hc).symm.pow_right 2
  exact heq.cancel_right_of_coprime hc'

private lemma normRoot_derivative_bound {d n x y : ℕ} (hd : 0 < d) (hn : 0 < n)
    (h : x ^ 2 + d * y ^ 2 = n) (hc : x.Coprime y) :
    n.gcd (2 * normRoot n (x, y)) ≤ 2 * d := by
  let r := normRoot n (x, y)
  let g := n.gcd r
  have hgx : g ∣ x := by
    have hmod := (normRoot_mul hn h hc).of_dvd (Nat.gcd_dvd_left n r)
    have hzero : r * y ≡ 0 [MOD g] :=
      Nat.modEq_zero_iff_dvd.mpr (dvd_mul_of_dvd_left (Nat.gcd_dvd_right _ _) _)
    exact Nat.modEq_zero_iff_dvd.mp (hmod.symm.trans hzero)
  have hgd : g ∣ d := by
    have hdyy : g ∣ d * y ^ 2 := by
      have hsum : g ∣ x ^ 2 + d * y ^ 2 := h ▸ Nat.gcd_dvd_left n r
      exact (Nat.dvd_add_iff_right (dvd_pow hgx (by decide : 2 ≠ 0))).mpr hsum
    exact ((hc.of_dvd_left hgx).pow_right 2).dvd_of_dvd_mul_right hdyy
  have hbound : n.gcd (2 * r) ∣ 2 * d := by
    exact (Nat.gcd_mul_right_dvd_mul_gcd n 2 r).trans
      (mul_dvd_mul (Nat.gcd_dvd_right n 2) hgd)
  exact Nat.le_of_dvd (by positivity) hbound

private lemma cross_product_lt {d n x y u v : ℕ} (hd : 2 ≤ d) (hn : 0 < n)
    (h : x ^ 2 + d * y ^ 2 = n) (h' : u ^ 2 + d * v ^ 2 = n) :
    x * v < n := by
  have hx : x ^ 2 ≤ n := by omega
  have hv : 2 * v ^ 2 ≤ n := by nlinarith
  have hm : 2 * (x * v) ^ 2 ≤ n ^ 2 := by
    calc
      2 * (x * v) ^ 2 = x ^ 2 * (2 * v ^ 2) := by ring
      _ ≤ n * n := Nat.mul_le_mul hx hv
      _ = n ^ 2 := by ring
  by_contra hnot
  have hh := Nat.pow_le_pow_left (Nat.le_of_not_lt hnot) 2
  nlinarith [sq_pos_of_pos hn]

private lemma normRoot_injective {d n : ℕ} (hd : 2 ≤ d) (hn : 0 < n) :
    Set.InjOn (normRoot n) (primitiveBinaryNormSolutions d n : Set (ℕ × ℕ)) := by
  intro p hp q hq heq
  obtain ⟨⟨hpbd, hp⟩, hpc⟩ := by
    simpa only [primitiveBinaryNormSolutions, binaryNormSolutions,
      Finset.mem_coe, Finset.mem_filter] using hp
  obtain ⟨⟨hqbd, hq⟩, hqc⟩ := by
    simpa only [primitiveBinaryNormSolutions, binaryNormSolutions,
      Finset.mem_coe, Finset.mem_filter] using hq
  have hr := (normRoot_mul hn hp hpc).mul_right q.2
  have hs := (normRoot_mul hn hq hqc).mul_right p.2
  have he : p.1 * q.2 ≡ q.1 * p.2 [MOD n] := by
    apply hr.symm.trans
    convert hs using 1
    rw [heq]
    ring
  have hc : p.1 * q.2 = q.1 * p.2 := he.eq_of_lt_of_lt
    (cross_product_lt hd hn hp hq) (cross_product_lt hd hn hq hp)
  have hsq : p.1 ^ 2 = q.1 ^ 2 := by
    apply Nat.mul_left_cancel hn
    calc
      n * p.1 ^ 2 = p.1 ^ 2 * q.1 ^ 2 + d * (p.1 * q.2) ^ 2 := by rw [← hq]; ring
      _ = p.1 ^ 2 * q.1 ^ 2 + d * (q.1 * p.2) ^ 2 := by rw [hc]
      _ = n * q.1 ^ 2 := by rw [← hp]; ring
  have hx : p.1 = q.1 := by nlinarith
  have hy : p.2 = q.2 := by
    rw [hx] at hp
    have hmul : d * p.2 ^ 2 = d * q.2 ^ 2 := by omega
    exact Nat.pow_left_injective (by decide : 2 ≠ 0)
      (Nat.mul_left_cancel (by omega : 0 < d) hmul)
  exact Prod.ext hx hy


lemma mem_binaryNormSolutions {d n : ℕ} (hd : 0 < d) (p : ℕ × ℕ) :
    p ∈ binaryNormSolutions d n ↔ p.1 ^ 2 + d * p.2 ^ 2 = n := by
  simp only [binaryNormSolutions, Finset.mem_filter, Finset.mem_product,
    Finset.mem_range]
  constructor
  · exact And.right
  · intro h
    have hx := Nat.le_pow (by decide : 0 < 2) (a := p.1)
    have hy := Nat.le_pow (by decide : 0 < 2) (a := p.2)
    have hdy : p.2 ^ 2 ≤ d * p.2 ^ 2 := Nat.le_mul_of_pos_left _ hd
    exact ⟨⟨by omega, by omega⟩, h⟩

theorem primitive_binary_norm_count {d n : ℕ} (hd : 2 ≤ d) (hn : 0 < n) :
    (primitiveBinaryNormSolutions d n).card ≤ n.divisors.card * (2 * d) := by
  classical
  by_cases hempty : (primitiveBinaryNormSolutions d n) = ∅
  · simp [hempty]
  obtain ⟨p,hp⟩ := Finset.nonempty_iff_ne_empty.mpr hempty
  have hp' := Finset.mem_filter.mp hp
  have hpNorm := (mem_binaryNormSolutions (by omega : 0 < d) p).mp hp'.1
  let a := normRoot n p
  have hroots := square_congruence_count (a := a) hn
    (normRoot_derivative_bound (by omega : 0 < d) hn hpNorm hp'.2)
  apply le_trans _ hroots
  apply Finset.card_le_card_of_injOn (normRoot n)
  · intro q hq
    simp only [Finset.mem_coe, primitiveBinaryNormSolutions, Finset.mem_filter] at hq
    have hqNorm := (mem_binaryNormSolutions (by omega : 0 < d) q).mp hq.1
    change normRoot n q ∈ (Finset.range n).filter (fun r ↦ r ^ 2 ≡ a ^ 2 [MOD n])
    refine Finset.mem_filter.mpr ⟨?_, ?_⟩
    · letI : NeZero n := ⟨hn.ne'⟩
      exact Finset.mem_range.mpr (ZMod.val_lt _)
    · have hr := normRoot_square hn hqNorm hq.2
      have hs := normRoot_square hn hpNorm hp'.2
      exact Nat.ModEq.add_right_cancel (Nat.ModEq.refl d) (hr.trans hs.symm)
  · exact normRoot_injective hd hn

private lemma norm_gcd_pos {d n : ℕ} (hn : 0 < n) (p : ℕ × ℕ)
    (hp : p.1 ^ 2 + d * p.2 ^ 2 = n) : 0 < p.1.gcd p.2 := by
  by_contra hnot
  have hg : p.1.gcd p.2 = 0 := by omega
  obtain ⟨hx,hy⟩ := Nat.gcd_eq_zero_iff.mp hg
  simp [hx, hy] at hp
  omega

private lemma norm_quotient_mul {d n : ℕ} (p : ℕ × ℕ)
    (hp : p.1 ^ 2 + d * p.2 ^ 2 = n) :
    p.1.gcd p.2 ^ 2 * ((p.1 / p.1.gcd p.2) ^ 2 +
      d * (p.2 / p.1.gcd p.2) ^ 2) = n := by
  calc
    _ = (p.1.gcd p.2 * (p.1 / p.1.gcd p.2)) ^ 2 +
        d * (p.1.gcd p.2 * (p.2 / p.1.gcd p.2)) ^ 2 := by ring
    _ = p.1 ^ 2 + d * p.2 ^ 2 := by
      rw [Nat.mul_div_cancel' (Nat.gcd_dvd_left _ _),
        Nat.mul_div_cancel' (Nat.gcd_dvd_right _ _)]
    _ = n := hp

private lemma norm_quotient_primitive {d n : ℕ} (hd : 0 < d) (hn : 0 < n)
    (p : ℕ × ℕ) (hp : p.1 ^ 2 + d * p.2 ^ 2 = n) :
    (p.1 / p.1.gcd p.2, p.2 / p.1.gcd p.2) ∈
      primitiveBinaryNormSolutions d (n / p.1.gcd p.2 ^ 2) := by
  have hg := norm_gcd_pos hn p hp
  have hmul := norm_quotient_mul p hp
  refine Finset.mem_filter.mpr ⟨?_, ?_⟩
  · apply (mem_binaryNormSolutions hd _).mpr
    change (p.1 / p.1.gcd p.2) ^ 2 + d * (p.2 / p.1.gcd p.2) ^ 2 = _
    rw [← hmul, Nat.mul_div_cancel_left _ (pow_pos hg 2)]
  · change (p.1 / p.1.gcd p.2).gcd (p.2 / p.1.gcd p.2) = 1
    rw [Nat.gcd_div (Nat.gcd_dvd_left _ _) (Nat.gcd_dvd_right _ _), Nat.div_self hg]

theorem binary_norm_count {d n : ℕ} (hd : 2 ≤ d) (hn : 0 < n) :
    (binaryNormSolutions d n).card ≤ (2 * d) * n.divisors.card ^ 2 := by
  classical
  let S := binaryNormSolutions d n
  let gs := S.image (fun p ↦ p.1.gcd p.2)
  have hgs : gs ⊆ n.divisors := by
    intro g hg
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hg
    have hpNorm := (mem_binaryNormSolutions (by omega : 0 < d) p).mp hp
    have hmul := norm_quotient_mul p hpNorm
    have hsq : p.1.gcd p.2 ^ 2 ∣ n := ⟨_, hmul.symm⟩
    exact Nat.mem_divisors.mpr ⟨(dvd_pow_self _ (by decide : 2 ≠ 0)).trans hsq, hn.ne'⟩
  have hfiber (g : ℕ) (hg : g ∈ gs) :
      (S.filter (fun p ↦ p.1.gcd p.2 = g)).card ≤ n.divisors.card * (2 * d) := by
    obtain ⟨p,hp,hpg⟩ := Finset.mem_image.mp hg
    have hpNorm := (mem_binaryNormSolutions (by omega : 0 < d) p).mp hp
    have hgpos : 0 < g := hpg ▸ norm_gcd_pos hn p hpNorm
    have hmul := norm_quotient_mul p hpNorm
    rw [hpg] at hmul
    have hsq : g ^ 2 ∣ n := ⟨_, hmul.symm⟩
    have hmpos : 0 < n / g ^ 2 :=
      Nat.div_pos (Nat.le_of_dvd hn hsq) (pow_pos hgpos 2)
    have hdiv : (n / g ^ 2).divisors.card ≤ n.divisors.card :=
      Finset.card_le_card (Nat.divisors_subset_of_dvd hn.ne' (Nat.div_dvd_of_dvd hsq))
    apply le_trans _ ((primitive_binary_norm_count hd hmpos).trans
      (Nat.mul_le_mul_right (2 * d) hdiv))
    apply Finset.card_le_card_of_injOn (fun q : ℕ × ℕ ↦ (q.1 / g, q.2 / g))
    · intro q hq
      simp only [Finset.mem_coe, Finset.mem_filter] at hq
      have hqNorm := (mem_binaryNormSolutions (by omega : 0 < d) q).mp hq.1
      have hh := norm_quotient_primitive (by omega : 0 < d) hn q hqNorm
      rwa [hq.2] at hh
    · intro q hq r hr heq
      simp only [Finset.mem_coe, Finset.mem_filter] at hq hr
      have h1 : q.1 / g = r.1 / g := congrArg Prod.fst heq
      have h2 : q.2 / g = r.2 / g := congrArg Prod.snd heq
      have hq1 : g * (q.1 / g) = q.1 := by
        rw [← hq.2]; exact Nat.mul_div_cancel' (Nat.gcd_dvd_left _ _)
      have hq2 : g * (q.2 / g) = q.2 := by
        rw [← hq.2]; exact Nat.mul_div_cancel' (Nat.gcd_dvd_right _ _)
      have hr1 : g * (r.1 / g) = r.1 := by
        rw [← hr.2]; exact Nat.mul_div_cancel' (Nat.gcd_dvd_left _ _)
      have hr2 : g * (r.2 / g) = r.2 := by
        rw [← hr.2]; exact Nat.mul_div_cancel' (Nat.gcd_dvd_right _ _)
      apply Prod.ext
      · rw [← hq1, ← hr1, h1]
      · rw [← hq2, ← hr2, h2]
  calc
    S.card = ∑ g ∈ gs, (S.filter (fun p ↦ p.1.gcd p.2 = g)).card :=
      Finset.card_eq_sum_card_image _ _
    _ ≤ ∑ g ∈ gs, n.divisors.card * (2 * d) := Finset.sum_le_sum hfiber
    _ = gs.card * (n.divisors.card * (2 * d)) := by simp
    _ ≤ n.divisors.card * (n.divisors.card * (2 * d)) :=
      Nat.mul_le_mul_right _ (Finset.card_le_card hgs)
    _ = (2 * d) * n.divisors.card ^ 2 := by ring


lemma binary_norm_zero {d : ℕ} (hd : 0 < d) : binaryNormSolutions d 0 = {(0,0)} := by
  ext p
  rw [mem_binaryNormSolutions hd, Finset.mem_singleton]
  constructor
  · intro h
    have hx : p.1 = 0 := by nlinarith
    have hy : p.2 = 0 := by
      have : d * p.2 ^ 2 = 0 := by omega
      have : p.2 ^ 2 = 0 := (mul_eq_zero.mp this).resolve_left hd.ne'
      nlinarith
    exact Prod.ext hx hy
  · rintro rfl
    simp

theorem binary_norm_subpolynomial {d : ℕ} (hd : 2 ≤ d) (ε : ℝ) (hε : 0 < ε) :
    ∃ C > (0 : ℝ), ∀ n : ℕ, 0 < n →
      ((binaryNormSolutions d n).card : ℝ) ≤ C * (n : ℝ) ^ ε := by
  obtain ⟨C,hC,hdiv⟩ := Erdos322Research.divisor_count_subpolynomial (ε / 2) (by linarith)
  refine ⟨(2 * d : ℝ) * C ^ 2, by positivity, ?_⟩
  intro n hn
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  have hp : ((n : ℝ) ^ (ε / 2)) ^ 2 = (n : ℝ) ^ ε := by
    rw [pow_two, ← Real.rpow_add hnr]
    congr 1
    ring
  calc
    ((binaryNormSolutions d n).card : ℝ) ≤ (2 * d : ℝ) * (n.divisors.card : ℝ) ^ 2 := by
      exact_mod_cast binary_norm_count hd hn
    _ ≤ (2 * d : ℝ) * (C * (n : ℝ) ^ (ε / 2)) ^ 2 := by gcongr; exact hdiv n hn
    _ = ((2 * d : ℝ) * C ^ 2) * (n : ℝ) ^ ε := by rw [mul_pow, hp]; ring

/-- A convenient uniform variant including target zero and all smaller targets. -/
theorem binary_norm_subpolynomial_up_to {d : ℕ} (hd : 2 ≤ d) (ε : ℝ) (hε : 0 < ε) :
    ∃ C > (0 : ℝ), ∀ N n : ℕ, n ≤ N →
      ((binaryNormSolutions d n).card : ℝ) ≤ C * (N + 1 : ℝ) ^ ε := by
  obtain ⟨C,hC,hbound⟩ := binary_norm_subpolynomial hd ε hε
  refine ⟨max 1 C, lt_of_lt_of_le zero_lt_one (le_max_left _ _), fun N n hn ↦ ?_⟩
  by_cases hz : n = 0
  · subst n
    rw [binary_norm_zero (by omega : 0 < d), Finset.card_singleton, Nat.cast_one]
    have hpow : 1 ≤ (N + 1 : ℝ) ^ ε := Real.one_le_rpow (by have := Nat.cast_nonneg (α := ℝ) N; linarith) hε.le
    nlinarith [le_max_left (1 : ℝ) C]
  · calc
      ((binaryNormSolutions d n).card : ℝ) ≤ C * (n : ℝ) ^ ε := hbound n (by omega)
      _ ≤ max 1 C * (N + 1 : ℝ) ^ ε := by
        apply mul_le_mul (le_max_right _ _) _ (by positivity) (by positivity)
        exact Real.rpow_le_rpow (by positivity) (by exact_mod_cast (by omega : n ≤ N + 1)) hε.le


private lemma cross_product_lt_of_first_pos {d n x y u v : ℕ} (hd : 0 < d) (hn : 0 < n)
    (hu : 0 < u) (h : x ^ 2 + d * y ^ 2 = n) (h' : u ^ 2 + d * v ^ 2 = n) :
    x * v < n := by
  by_cases hx : x = 0
  · simpa [hx] using hn
  have hxp : 0 < x ^ 2 := pow_pos (by omega) 2
  have hv : v ^ 2 < n := by
    have hh : v ^ 2 ≤ d * v ^ 2 := Nat.le_mul_of_pos_left _ hd
    have hh' : 0 < u ^ 2 := pow_pos hu 2
    omega
  have hm : (x * v) ^ 2 < n ^ 2 := by
    calc
      (x * v) ^ 2 = x ^ 2 * v ^ 2 := by ring
      _ < x ^ 2 * n := Nat.mul_lt_mul_of_pos_left hv hxp
      _ ≤ n * n := Nat.mul_le_mul_right n (by omega)
      _ = n ^ 2 := by ring
  by_contra hnot
  have hh := Nat.pow_le_pow_left (Nat.le_of_not_lt hnot) 2
  omega

private lemma normRoot_tag_injective {d n : ℕ} (hd : 0 < d) (hn : 0 < n) :
    Set.InjOn (fun p : ℕ × ℕ ↦ (normRoot n p, decide (p.1 = 0)))
      (primitiveBinaryNormSolutions d n : Set (ℕ × ℕ)) := by
  intro p hp q hq heq
  obtain ⟨⟨hpbd, hp⟩, hpc⟩ := by
    simpa only [primitiveBinaryNormSolutions, binaryNormSolutions,
      Finset.mem_coe, Finset.mem_filter] using hp
  obtain ⟨⟨hqbd, hq⟩, hqc⟩ := by
    simpa only [primitiveBinaryNormSolutions, binaryNormSolutions,
      Finset.mem_coe, Finset.mem_filter] using hq
  have hroot : normRoot n p = normRoot n q := congrArg Prod.fst heq
  have htag : decide (p.1 = 0) = decide (q.1 = 0) := congrArg Prod.snd heq
  have hz := decide_eq_decide.mp htag
  have hx : p.1 = q.1 := by
    by_cases hp0 : p.1 = 0
    · exact hp0.trans (hz.mp hp0).symm
    have hq0 : q.1 ≠ 0 := fun h ↦ hp0 (hz.mpr h)
    have hr := (normRoot_mul hn hp hpc).mul_right q.2
    have hs := (normRoot_mul hn hq hqc).mul_right p.2
    have he : p.1 * q.2 ≡ q.1 * p.2 [MOD n] := by
      apply hr.symm.trans
      convert hs using 1
      rw [hroot]
      ring
    have hc : p.1 * q.2 = q.1 * p.2 := he.eq_of_lt_of_lt
      (cross_product_lt_of_first_pos hd hn (by omega) hp hq)
      (cross_product_lt_of_first_pos hd hn (by omega) hq hp)
    have hsq : p.1 ^ 2 = q.1 ^ 2 := by
      apply Nat.mul_left_cancel hn
      calc
        n * p.1 ^ 2 = p.1 ^ 2 * q.1 ^ 2 + d * (p.1 * q.2) ^ 2 := by rw [← hq]; ring
        _ = p.1 ^ 2 * q.1 ^ 2 + d * (q.1 * p.2) ^ 2 := by rw [hc]
        _ = n * q.1 ^ 2 := by rw [← hp]; ring
    exact Nat.pow_left_injective (by decide : 2 ≠ 0) hsq
  have hy : p.2 = q.2 := by
    rw [hx] at hp
    have hmul : d * p.2 ^ 2 = d * q.2 ^ 2 := by omega
    exact Nat.pow_left_injective (by decide : 2 ≠ 0) (Nat.mul_left_cancel hd hmul)
  exact Prod.ext hx hy

/-- A slightly weaker bound that also includes the Gaussian norm. -/
theorem primitive_binary_norm_count_general {d n : ℕ} (hd : 0 < d) (hn : 0 < n) :
    (primitiveBinaryNormSolutions d n).card ≤ n.divisors.card * (4 * d) := by
  classical
  by_cases hempty : (primitiveBinaryNormSolutions d n) = ∅
  · simp [hempty]
  obtain ⟨p,hp⟩ := Finset.nonempty_iff_ne_empty.mpr hempty
  have hp' := Finset.mem_filter.mp hp
  have hpNorm := (mem_binaryNormSolutions hd p).mp hp'.1
  let a := normRoot n p
  let R := (Finset.range n).filter (fun r ↦ r ^ 2 ≡ a ^ 2 [MOD n])
  have hroots := square_congruence_count (a := a) hn
    (normRoot_derivative_bound hd hn hpNorm hp'.2)
  have hcard : (primitiveBinaryNormSolutions d n).card ≤ (R ×ˢ (Finset.univ : Finset Bool)).card := by
    apply Finset.card_le_card_of_injOn (fun p : ℕ × ℕ ↦ (normRoot n p, decide (p.1 = 0)))
    · intro q hq
      simp only [Finset.mem_coe, primitiveBinaryNormSolutions, Finset.mem_filter] at hq
      have hqNorm := (mem_binaryNormSolutions hd q).mp hq.1
      change (normRoot n q, decide (q.1 = 0)) ∈ R ×ˢ (Finset.univ : Finset Bool)
      apply Finset.mem_product.mpr
      refine ⟨Finset.mem_filter.mpr ⟨?_, ?_⟩, Finset.mem_univ _⟩
      · letI : NeZero n := ⟨hn.ne'⟩
        exact Finset.mem_range.mpr (ZMod.val_lt _)
      · have hr := normRoot_square hn hqNorm hq.2
        have hs := normRoot_square hn hpNorm hp'.2
        exact Nat.ModEq.add_right_cancel (Nat.ModEq.refl d) (hr.trans hs.symm)
    · exact normRoot_tag_injective hd hn
  have hcard' : (primitiveBinaryNormSolutions d n).card ≤ R.card * 2 := by simpa using hcard
  calc
    (primitiveBinaryNormSolutions d n).card ≤ R.card * 2 := hcard'
    _ ≤ (n.divisors.card * (2 * d)) * 2 := Nat.mul_le_mul_right 2 hroots
    _ = n.divisors.card * (4 * d) := by ring

theorem binary_norm_count_general {d n : ℕ} (hd : 0 < d) (hn : 0 < n) :
    (binaryNormSolutions d n).card ≤ (4 * d) * n.divisors.card ^ 2 := by
  classical
  let S := binaryNormSolutions d n
  let gs := S.image (fun p ↦ p.1.gcd p.2)
  have hgs : gs ⊆ n.divisors := by
    intro g hg
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hg
    have hpNorm := (mem_binaryNormSolutions (by omega : 0 < d) p).mp hp
    have hmul := norm_quotient_mul p hpNorm
    have hsq : p.1.gcd p.2 ^ 2 ∣ n := ⟨_, hmul.symm⟩
    exact Nat.mem_divisors.mpr ⟨(dvd_pow_self _ (by decide : 2 ≠ 0)).trans hsq, hn.ne'⟩
  have hfiber (g : ℕ) (hg : g ∈ gs) :
      (S.filter (fun p ↦ p.1.gcd p.2 = g)).card ≤ n.divisors.card * (4 * d) := by
    obtain ⟨p,hp,hpg⟩ := Finset.mem_image.mp hg
    have hpNorm := (mem_binaryNormSolutions (by omega : 0 < d) p).mp hp
    have hgpos : 0 < g := hpg ▸ norm_gcd_pos hn p hpNorm
    have hmul := norm_quotient_mul p hpNorm
    rw [hpg] at hmul
    have hsq : g ^ 2 ∣ n := ⟨_, hmul.symm⟩
    have hmpos : 0 < n / g ^ 2 :=
      Nat.div_pos (Nat.le_of_dvd hn hsq) (pow_pos hgpos 2)
    have hdiv : (n / g ^ 2).divisors.card ≤ n.divisors.card :=
      Finset.card_le_card (Nat.divisors_subset_of_dvd hn.ne' (Nat.div_dvd_of_dvd hsq))
    apply le_trans _ ((primitive_binary_norm_count_general hd hmpos).trans
      (Nat.mul_le_mul_right (4 * d) hdiv))
    apply Finset.card_le_card_of_injOn (fun q : ℕ × ℕ ↦ (q.1 / g, q.2 / g))
    · intro q hq
      simp only [Finset.mem_coe, Finset.mem_filter] at hq
      have hqNorm := (mem_binaryNormSolutions (by omega : 0 < d) q).mp hq.1
      have hh := norm_quotient_primitive (by omega : 0 < d) hn q hqNorm
      rwa [hq.2] at hh
    · intro q hq r hr heq
      simp only [Finset.mem_coe, Finset.mem_filter] at hq hr
      have h1 : q.1 / g = r.1 / g := congrArg Prod.fst heq
      have h2 : q.2 / g = r.2 / g := congrArg Prod.snd heq
      have hq1 : g * (q.1 / g) = q.1 := by
        rw [← hq.2]; exact Nat.mul_div_cancel' (Nat.gcd_dvd_left _ _)
      have hq2 : g * (q.2 / g) = q.2 := by
        rw [← hq.2]; exact Nat.mul_div_cancel' (Nat.gcd_dvd_right _ _)
      have hr1 : g * (r.1 / g) = r.1 := by
        rw [← hr.2]; exact Nat.mul_div_cancel' (Nat.gcd_dvd_left _ _)
      have hr2 : g * (r.2 / g) = r.2 := by
        rw [← hr.2]; exact Nat.mul_div_cancel' (Nat.gcd_dvd_right _ _)
      apply Prod.ext
      · rw [← hq1, ← hr1, h1]
      · rw [← hq2, ← hr2, h2]
  calc
    S.card = ∑ g ∈ gs, (S.filter (fun p ↦ p.1.gcd p.2 = g)).card :=
      Finset.card_eq_sum_card_image _ _
    _ ≤ ∑ g ∈ gs, n.divisors.card * (4 * d) := Finset.sum_le_sum hfiber
    _ = gs.card * (n.divisors.card * (4 * d)) := by simp
    _ ≤ n.divisors.card * (n.divisors.card * (4 * d)) :=
      Nat.mul_le_mul_right _ (Finset.card_le_card hgs)
    _ = (4 * d) * n.divisors.card ^ 2 := by ring

theorem binary_norm_subpolynomial_general {d : ℕ} (hd : 0 < d) (ε : ℝ) (hε : 0 < ε) :
    ∃ C > (0 : ℝ), ∀ n : ℕ, 0 < n →
      ((binaryNormSolutions d n).card : ℝ) ≤ C * (n : ℝ) ^ ε := by
  obtain ⟨C,hC,hdiv⟩ := Erdos322Research.divisor_count_subpolynomial (ε / 2) (by linarith)
  refine ⟨(4 * d : ℝ) * C ^ 2, by positivity, ?_⟩
  intro n hn
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  have hp : ((n : ℝ) ^ (ε / 2)) ^ 2 = (n : ℝ) ^ ε := by
    rw [pow_two, ← Real.rpow_add hnr]
    congr 1
    ring
  calc
    ((binaryNormSolutions d n).card : ℝ) ≤ (4 * d : ℝ) * (n.divisors.card : ℝ) ^ 2 := by
      exact_mod_cast binary_norm_count_general hd hn
    _ ≤ (4 * d : ℝ) * (C * (n : ℝ) ^ (ε / 2)) ^ 2 := by gcongr; exact hdiv n hn
    _ = ((4 * d : ℝ) * C ^ 2) * (n : ℝ) ^ ε := by rw [mul_pow, hp]; ring

/-- A convenient uniform variant including target zero and all smaller targets. -/
theorem binary_norm_subpolynomial_general_up_to {d : ℕ} (hd : 0 < d) (ε : ℝ) (hε : 0 < ε) :
    ∃ C > (0 : ℝ), ∀ N n : ℕ, n ≤ N →
      ((binaryNormSolutions d n).card : ℝ) ≤ C * (N + 1 : ℝ) ^ ε := by
  obtain ⟨C,hC,hbound⟩ := binary_norm_subpolynomial_general hd ε hε
  refine ⟨max 1 C, lt_of_lt_of_le zero_lt_one (le_max_left _ _), fun N n hn ↦ ?_⟩
  by_cases hz : n = 0
  · subst n
    rw [binary_norm_zero (by omega : 0 < d), Finset.card_singleton, Nat.cast_one]
    have hpow : 1 ≤ (N + 1 : ℝ) ^ ε := Real.one_le_rpow (by have := Nat.cast_nonneg (α := ℝ) N; linarith) hε.le
    nlinarith [le_max_left (1 : ℝ) C]
  · calc
      ((binaryNormSolutions d n).card : ℝ) ≤ C * (n : ℝ) ^ ε := hbound n (by omega)
      _ ≤ max 1 C * (N + 1 : ℝ) ^ ε := by
        apply mul_le_mul (le_max_right _ _) _ (by positivity) (by positivity)
        exact Real.rpow_le_rpow (by positivity) (by exact_mod_cast (by omega : n ≤ N + 1)) hε.le

end Erdos322Research
