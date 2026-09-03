import Submission.BinaryNormBound

/-! Bounds on positive binary quadratic norms, uniform in their coefficient. -/
namespace Erdos322Research.UniformBinaryNorm

open Erdos322Research

private lemma coprime_right {d n x y : ℕ}
    (h : x^2+d*y^2=n) (hc : x.Coprime y) : y.Coprime n := by
  rw [← h, show d*y^2 = (d*y)*y by ring, Nat.coprime_add_mul_right_right]
  exact hc.symm.pow_right 2

/-- Ramified primes in a primitive representation of a squarefree-coefficient
norm occur to exponent one in the target. -/
private lemma reduced_coprime {d n x y : ℕ} (hs : Squarefree d)
    (h : x^2+d*y^2=n) (hc : x.Coprime y) : (n / n.gcd d).Coprime x := by
  apply Nat.coprime_of_dvd
  intro p hp hpm hpx
  have hpn : p ∣ n := hpm.trans (Nat.div_dvd_of_dvd (Nat.gcd_dvd_left n d))
  have hpdy : p ∣ d*y^2 := (Nat.dvd_add_iff_right (dvd_pow hpx (by decide : 2 ≠ 0))).mpr (h ▸ hpn)
  have hpy : p.Coprime y := hc.of_dvd_left hpx
  have hpd : p ∣ d := (hpy.pow_right 2).dvd_of_dvd_mul_right hpdy
  have hpg : p ∣ n.gcd d := Nat.dvd_gcd hpn hpd
  have hppn : p^2 ∣ n := by
    have hm := mul_dvd_mul hpg hpm
    rw [Nat.mul_div_cancel' (Nat.gcd_dvd_left n d)] at hm
    simpa only [pow_two] using hm
  have hppx : p^2 ∣ x^2 := pow_dvd_pow_of_dvd hpx 2
  have hppdy : p^2 ∣ d*y^2 := (Nat.dvd_add_iff_right hppx).mpr (h ▸ hppn)
  have hppd : p^2 ∣ d := (hpy.pow 2 2).dvd_of_dvd_mul_right hppdy
  exact hp.not_isUnit (hs p (by simpa only [pow_two] using hppd))

private lemma common_factor_dvd_first {d n x y : ℕ} (hs : Squarefree d)
    (h : x^2+d*y^2=n) : n.gcd d ∣ x := by
  have hgs : Squarefree (n.gcd d) := hs.squarefree_of_dvd (Nat.gcd_dvd_right n d)
  apply (hgs.dvd_pow_iff_dvd (by decide : 2 ≠ 0)).mp
  have hgd : n.gcd d ∣ d*y^2 := dvd_mul_of_dvd_left (Nat.gcd_dvd_right n d) _
  apply (Nat.dvd_add_iff_left hgd).mpr
  rw [h]
  exact Nat.gcd_dvd_left n d

private def root (m : ℕ) (p : ℕ × ℕ) : ℕ :=
  ((p.1 : ZMod m)*(p.2 : ZMod m)⁻¹).val

private lemma root_mul {d n m x y : ℕ} (hm : 0 < m) (hmn : m ∣ n)
    (h : x^2+d*y^2=n) (hc : x.Coprime y) : root m (x,y)*y ≡ x [MOD m] := by
  letI : NeZero m := ⟨hm.ne'⟩
  apply (ZMod.natCast_eq_natCast_iff _ _ _).mp
  have hi := ZMod.mul_inv_of_unit (y : ZMod m)
    ((ZMod.isUnit_iff_coprime _ _).mpr ((coprime_right h hc).of_dvd_right hmn))
  simp only [Nat.cast_mul, root, ZMod.natCast_zmod_val]
  calc
    (x : ZMod m)*(y : ZMod m)⁻¹*y = x*(y*(y : ZMod m)⁻¹) := by ring
    _ = x := by rw [hi, mul_one]

private lemma root_square {d n m x y : ℕ} (hm : 0 < m) (hmn : m ∣ n)
    (h : x^2+d*y^2=n) (hc : x.Coprime y) : root m (x,y)^2+d ≡ 0 [MOD m] := by
  have hr := root_mul hm hmn h hc
  have he : (root m (x,y)^2+d)*y^2 ≡ 0*y^2 [MOD m] := by
    have hh : x^2+d*y^2 ≡ 0 [MOD m] := Nat.modEq_zero_iff_dvd.mpr (h ▸ hmn)
    convert ((hr.pow 2).add_right (d*y^2)).trans hh using 1 <;> ring
  exact he.cancel_right_of_coprime (((coprime_right h hc).of_dvd_right hmn).symm.pow_right 2)

private lemma root_derivative {d n m x y : ℕ} (hm : 0 < m) (hmn : m ∣ n)
    (h : x^2+d*y^2=n) (hc : x.Coprime y) (hmx : m.Coprime x) :
    m.gcd (2*root m (x,y)) ≤ 2 := by
  have hr := root_mul hm hmn h hc
  have hrc : (root m (x,y)*y).Coprime m := by
    change (root m (x,y)*y).gcd m = 1
    rw [hr.gcd_eq]
    exact hmx.symm
  have hrc' : m.gcd (root m (x,y)) = 1 := (Nat.coprime_mul_iff_left.mp hrc).1.symm
  have hdiv := Nat.gcd_mul_right_dvd_mul_gcd m 2 (root m (x,y))
  rw [hrc', mul_one] at hdiv
  exact Nat.le_of_dvd (by decide : 0 < 2) (hdiv.trans (Nat.gcd_dvd_right m 2))

private lemma cross_lt {d n x y u v : ℕ} (hd : 0 < d) (hn : 0 < n)
    (hu : 0 < u) (h : x^2+d*y^2=n) (h' : u^2+d*v^2=n) : x*v < n := by
  by_cases hx : x = 0
  · simpa [hx] using hn
  have hxp : 0 < x^2 := pow_pos (by omega) 2
  have hv : v^2 < n := by
    have hh : v^2 ≤ d*v^2 := Nat.le_mul_of_pos_left _ hd
    have hh' : 0 < u^2 := pow_pos hu 2
    omega
  have hm : (x*v)^2 < n^2 := by
    calc
      (x*v)^2 = x^2*v^2 := by ring
      _ < x^2*n := Nat.mul_lt_mul_of_pos_left hv hxp
      _ ≤ n*n := Nat.mul_le_mul_right n (by omega)
      _ = n^2 := by ring
  by_contra hnot
  have hh := Nat.pow_le_pow_left (Nat.le_of_not_lt hnot) 2
  omega

private lemma root_tag_injective {d n : ℕ} (hd : 0 < d) (hs : Squarefree d) (hn : 0 < n) :
    Set.InjOn (fun p : ℕ × ℕ ↦ (root (n / n.gcd d) p, decide (p.1=0)))
      (primitiveBinaryNormSolutions d n : Set (ℕ × ℕ)) := by
  intro p hp q hq he
  obtain ⟨hp, hpc⟩ := Finset.mem_filter.mp hp
  obtain ⟨hq, hqc⟩ := Finset.mem_filter.mp hq
  have hp' := (mem_binaryNormSolutions hd p).mp hp
  have hq' := (mem_binaryNormSolutions hd q).mp hq
  let g := n.gcd d
  let m := n/g
  have hg : 0 < g := Nat.gcd_pos_of_pos_left d hn
  have hgn : g ∣ n := Nat.gcd_dvd_left n d
  have hm : 0 < m := Nat.div_pos (Nat.le_of_dvd hn hgn) hg
  have hmn : m ∣ n := Nat.div_dvd_of_dvd hgn
  have hgm : g*m=n := Nat.mul_div_cancel' hgn
  have hgp : g ∣ p.1 := common_factor_dvd_first hs hp'
  have hgq : g ∣ q.1 := common_factor_dvd_first hs hq'
  have hcop : g.Coprime m := ((reduced_coprime hs hp' hpc).of_dvd_right hgp).symm
  have hr : root m p = root m q := congrArg Prod.fst he
  have hz : p.1=0 ↔ q.1=0 := decide_eq_decide.mp (congrArg Prod.snd he)
  have hx : p.1=q.1 := by
    by_cases hp0 : p.1=0
    · exact hp0.trans (hz.mp hp0).symm
    have hq0 : q.1 ≠ 0 := fun h ↦ hp0 (hz.mpr h)
    have h₁ := (root_mul hm hmn hp' hpc).mul_right q.2
    have h₂ := (root_mul hm hmn hq' hqc).mul_right p.2
    have hem : p.1*q.2 ≡ q.1*p.2 [MOD m] := by
      apply h₁.symm.trans
      convert h₂ using 1
      rw [hr]
      ring
    have heg : p.1*q.2 ≡ q.1*p.2 [MOD g] :=
      (Nat.modEq_zero_iff_dvd.mpr (dvd_mul_of_dvd_left hgp _)).trans
        (Nat.modEq_zero_iff_dvd.mpr (dvd_mul_of_dvd_left hgq _)).symm
    have hen : p.1*q.2 ≡ q.1*p.2 [MOD n] := by
      rw [← hgm]
      exact (Nat.modEq_and_modEq_iff_modEq_mul hcop).mp ⟨heg, hem⟩
    have hc : p.1*q.2=q.1*p.2 := hen.eq_of_lt_of_lt
      (cross_lt hd hn (by omega) hp' hq') (cross_lt hd hn (by omega) hq' hp')
    have hsq : p.1^2=q.1^2 := by
      apply Nat.mul_left_cancel hn
      calc
        n*p.1^2 = p.1^2*q.1^2+d*(p.1*q.2)^2 := by rw [← hq']; ring
        _ = p.1^2*q.1^2+d*(q.1*p.2)^2 := by rw [hc]
        _ = n*q.1^2 := by rw [← hp']; ring
    exact Nat.pow_left_injective (by decide : 2 ≠ 0) hsq
  have hy : p.2=q.2 := by
    rw [hx] at hp'
    have hmul : d*p.2^2=d*q.2^2 := by omega
    exact Nat.pow_left_injective (by decide : 2 ≠ 0) (Nat.mul_left_cancel hd hmul)
  exact Prod.ext hx hy

/-- The primitive bound is independent of a squarefree norm coefficient. -/
theorem primitive_norm_count_squarefree {d n : ℕ} (hd : 0 < d)
    (hs : Squarefree d) (hn : 0 < n) :
    (primitiveBinaryNormSolutions d n).card ≤ 4*n.divisors.card := by
  classical
  by_cases he : primitiveBinaryNormSolutions d n = ∅
  · simp [he]
  obtain ⟨p, hp⟩ := Finset.nonempty_iff_ne_empty.mpr he
  obtain ⟨hp, hpc⟩ := Finset.mem_filter.mp hp
  have hp' := (mem_binaryNormSolutions hd p).mp hp
  let m := n/n.gcd d
  have hm : 0 < m := Nat.div_pos
    (Nat.le_of_dvd hn (Nat.gcd_dvd_left n d)) (Nat.gcd_pos_of_pos_left d hn)
  have hmn : m ∣ n := Nat.div_dvd_of_dvd (Nat.gcd_dvd_left n d)
  let a := root m p
  let R := (Finset.range m).filter (fun r ↦ r^2 ≡ a^2 [MOD m])
  have hroots : R.card ≤ m.divisors.card*2 := square_congruence_count hm
    (root_derivative hm hmn hp' hpc (reduced_coprime hs hp' hpc))
  have hb : (primitiveBinaryNormSolutions d n).card ≤ (R ×ˢ (Finset.univ : Finset Bool)).card := by
    apply Finset.card_le_card_of_injOn (fun q : ℕ × ℕ ↦ (root m q, decide (q.1=0)))
    · intro q hq
      obtain ⟨hq, hqc⟩ := Finset.mem_filter.mp hq
      have hq' := (mem_binaryNormSolutions hd q).mp hq
      apply Finset.mem_product.mpr
      refine ⟨Finset.mem_filter.mpr ⟨?_, ?_⟩, Finset.mem_univ _⟩
      · letI : NeZero m := ⟨hm.ne'⟩
        exact Finset.mem_range.mpr (ZMod.val_lt _)
      · exact Nat.ModEq.add_right_cancel (Nat.ModEq.refl d)
          ((root_square hm hmn hq' hqc).trans (root_square hm hmn hp' hpc).symm)
    · exact root_tag_injective hd hs hn
  have hdiv : m.divisors.card ≤ n.divisors.card :=
    Finset.card_le_card (Nat.divisors_subset_of_dvd hn.ne' hmn)
  have hb' : (primitiveBinaryNormSolutions d n).card ≤ R.card*2 := by simpa using hb
  nlinarith


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

theorem norm_count_squarefree {d n : ℕ} (hd : 0 < d) (hs : Squarefree d) (hn : 0 < n) :
    (binaryNormSolutions d n).card ≤ 4 * n.divisors.card ^ 2 := by
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
      (S.filter (fun p ↦ p.1.gcd p.2 = g)).card ≤ n.divisors.card * 4 := by
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
    have hb := (primitive_norm_count_squarefree hd hs hmpos).trans
      (Nat.mul_le_mul_left 4 hdiv)
    rw [mul_comm 4] at hb
    apply le_trans _ hb
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
    _ ≤ ∑ g ∈ gs, n.divisors.card * 4 := Finset.sum_le_sum hfiber
    _ = gs.card * (n.divisors.card * 4) := by simp
    _ ≤ n.divisors.card * (n.divisors.card * 4) :=
      Nat.mul_le_mul_right _ (Finset.card_le_card hgs)
    _ = 4 * n.divisors.card ^ 2 := by ring

/-- A coefficient-uniform divisor bound, with no squarefreeness assumption. -/
theorem binary_norm_count_uniform {d n : ℕ} (hd : 0 < d) (hn : 0 < n) :
    (binaryNormSolutions d n).card ≤ 4*n.divisors.card^2 := by
  obtain ⟨a, b, hba, has⟩ := Nat.sq_mul_squarefree d
  have ha : 0 < a := Nat.pos_of_ne_zero has.ne_zero
  have hb : 0 < b := by
    by_contra hnot
    have hb0 : b=0 := by omega
    simp [hb0] at hba
    omega
  apply le_trans _ (norm_count_squarefree ha has hn)
  apply Finset.card_le_card_of_injOn (fun p : ℕ × ℕ ↦ (p.1, b*p.2))
  · intro p hp
    apply (mem_binaryNormSolutions ha _).mpr
    have hp' := (mem_binaryNormSolutions hd p).mp hp
    change p.1^2+a*(b*p.2)^2=n
    calc
      p.1^2+a*(b*p.2)^2 = p.1^2+(b^2*a)*p.2^2 := by ring
      _ = n := by rw [hba]; exact hp'
  · intro p hp q hq he
    have h₁ := congrArg Prod.fst he
    change p.1=q.1 at h₁
    have h₂ : b*p.2=b*q.2 := congrArg Prod.snd he
    exact Prod.ext h₁ (Nat.mul_left_cancel hb h₂)

/-- The same subpolynomial constant works for every positive norm coefficient,
including a coefficient chosen as a function of the target. -/
theorem binary_norm_subpolynomial_uniform (ε : ℝ) (hε : 0 < ε) :
    ∃ C > (0 : ℝ), ∀ d n : ℕ, 0 < d → 0 < n →
      ((binaryNormSolutions d n).card : ℝ) ≤ C*(n : ℝ)^ε := by
  obtain ⟨C, hC, hdiv⟩ := Erdos322Research.divisor_count_subpolynomial (ε/2) (by linarith)
  refine ⟨4*C^2, by positivity, fun d n hd hn ↦ ?_⟩
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  have hp : ((n : ℝ)^(ε/2))^2 = (n : ℝ)^ε := by
    rw [pow_two, ← Real.rpow_add hnr]
    congr 1
    ring
  calc
    ((binaryNormSolutions d n).card : ℝ) ≤ 4*(n.divisors.card : ℝ)^2 := by
      exact_mod_cast binary_norm_count_uniform hd hn
    _ ≤ 4*(C*(n : ℝ)^(ε/2))^2 := by gcongr; exact hdiv n hn
    _ = (4*C^2)*(n : ℝ)^ε := by rw [mul_pow, hp]; ring

/-- A uniform bound for any finite collection of solutions of a positive
binary diagonal quadratic equation, even when both coefficients vary. -/
theorem diagonal_binary_subpolynomial_uniform (ε : ℝ) (hε : 0 < ε) :
    ∃ C > (0 : ℝ), ∀ a d n : ℕ, 0 < a → 0 < d → 0 < n →
      ∀ S : Finset (ℕ × ℕ), (∀ p ∈ S, a*p.1^2+d*p.2^2=n) →
        (S.card : ℝ) ≤ C*(n : ℝ)^ε := by
  classical
  obtain ⟨C, hC, hb⟩ := binary_norm_subpolynomial_uniform (ε/2) (by linarith)
  refine ⟨max 1 C, lt_of_lt_of_le zero_lt_one (le_max_left _ _),
    fun a d n ha hd hn S hS ↦ ?_⟩
  by_cases hzero : ∀ p ∈ S, p.1=0
  · have hcard : S.card ≤ 1 := by
      apply Finset.card_le_one.mpr
      intro p hp q hq
      have hp' := hS p hp
      have hq' := hS q hq
      rw [hzero p hp] at hp'
      rw [hzero q hq] at hq'
      simp only [zero_pow (by decide : 2 ≠ 0), mul_zero, zero_add] at hp' hq'
      apply Prod.ext ((hzero p hp).trans (hzero q hq).symm)
      exact Nat.pow_left_injective (by decide : 2 ≠ 0)
        (Nat.mul_left_cancel hd (hp'.trans hq'.symm))
    have hp : 1 ≤ (n : ℝ)^ε := Real.one_le_rpow (by exact_mod_cast hn) hε.le
    have hc : (S.card : ℝ) ≤ 1 := by exact_mod_cast hcard
    apply hc.trans
    calc
      (1 : ℝ) = 1*1 := by norm_num
      _ ≤ max 1 C*(n : ℝ)^ε := mul_le_mul (le_max_left _ _) hp (by norm_num) (by positivity)
  · push_neg at hzero
    obtain ⟨p, hp, hpx⟩ := hzero
    have han : a ≤ n := by
      have hp' := hS p hp
      have hx : 1 ≤ p.1^2 := one_le_pow₀ (by omega)
      have hh := Nat.mul_le_mul_left a hx
      nlinarith
    have hcard : S.card ≤ (binaryNormSolutions (a*d) (a*n)).card := by
      apply Finset.card_le_card_of_injOn (fun p : ℕ × ℕ ↦ (a*p.1, p.2))
      · intro p hp
        apply (mem_binaryNormSolutions (Nat.mul_pos ha hd) _).mpr
        change (a*p.1)^2+(a*d)*p.2^2=a*n
        calc
          (a*p.1)^2+(a*d)*p.2^2 = a*(a*p.1^2+d*p.2^2) := by ring
          _ = a*n := by rw [hS p hp]
      · intro p hp q hq he
        have h₁ : a*p.1=a*q.1 := congrArg Prod.fst he
        have h₂ := congrArg Prod.snd he
        change p.2=q.2 at h₂
        exact Prod.ext (Nat.mul_left_cancel ha h₁) h₂
    have hnr : (0 : ℝ) < n := by exact_mod_cast hn
    have hh : ((a*n : ℕ) : ℝ)^(ε/2) ≤ (n : ℝ)^ε := by
      calc
        ((a*n : ℕ) : ℝ)^(ε/2) ≤ ((n : ℝ)*(n : ℝ))^(ε/2) := by
          apply Real.rpow_le_rpow (by positivity) _ (by linarith)
          exact_mod_cast Nat.mul_le_mul_right n han
        _ = (n : ℝ)^ε := by
          rw [Real.mul_rpow hnr.le hnr.le, ← Real.rpow_add hnr]
          congr 1
          ring
    calc
      (S.card : ℝ) ≤ (binaryNormSolutions (a*d) (a*n)).card := by exact_mod_cast hcard
      _ ≤ C*((a*n : ℕ) : ℝ)^(ε/2) := hb (a*d) (a*n) (Nat.mul_pos ha hd) (Nat.mul_pos ha hn)
      _ ≤ max 1 C*(n : ℝ)^ε := mul_le_mul (le_max_right _ _) hh (by positivity) (by positivity)

end Erdos322Research.UniformBinaryNorm
