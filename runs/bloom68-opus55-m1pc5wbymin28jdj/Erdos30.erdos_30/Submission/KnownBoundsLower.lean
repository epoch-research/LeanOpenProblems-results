import Submission.KnownBounds

/-!
# Erdős Problem 30 — known lower bounds (variants)

This file does **not** settle `Erdos30.erdos_30` (an open problem). It formalizes the classical
lower-bound side of the known results:

* `Erdos30.singer_le_h`: **Singer's construction** (1938): for every prime `p`,
  `p + 1 ≤ h (p^2 + p + 1)`. The Sidon set is `{i < p^2+p+1 : f(g^i) = 0}` where `g` generates
  `𝔽_{p^3}ˣ` and `f : 𝔽_{p^3} → 𝔽_p` is a nonzero linear functional (a perfect difference set).
* `Erdos30.frequently_sqrt_le_h`: `√N ≤ h N` for infinitely many `N`.
* `Erdos30.sqrt_sub_one_div_two_le_h`: `(√N - 1)/2 ≤ h N` for all `N` (Singer + Bertrand).
-/

open Finset

namespace SingerConstr

variable (p : ℕ) [hp : Fact p.Prime]

/-- The field with `p^3` elements. -/
abbrev K := GaloisField p 3

noncomputable instance instFintypeK : Fintype (K p) := Fintype.ofFinite _

noncomputable instance instDecEqK : DecidableEq (K p) := Classical.decEq _

lemma card_K : Fintype.card (K p) = p ^ 3 := by
  rw [Fintype.card_eq_nat_card]; exact GaloisField.card p 3 (by norm_num)

lemma finrank_K : Module.finrank (ZMod p) (K p) = 3 := GaloisField.finrank p (by norm_num)

/-- A nonzero linear functional `K → ZMod p`. -/
noncomputable def f : K p →ₗ[ZMod p] ZMod p :=
  (Module.finBasisOfFinrankEq (ZMod p) (K p) (finrank_K p)).coord 0

lemma f_surj : Function.Surjective (f p) := by
  intro c
  refine ⟨c • (Module.finBasisOfFinrankEq (ZMod p) (K p) (finrank_K p)) 0, ?_⟩
  simp [f]

lemma finrank_ker_f : Module.finrank (ZMod p) (LinearMap.ker (f p)) = 2 := by
  have h1 := LinearMap.finrank_range_add_finrank_ker (f p)
  rw [LinearMap.range_eq_top.mpr (f_surj p), finrank_top, Module.finrank_self, finrank_K] at h1
  omega

lemma card_ker_f : (univ.filter (fun x : K p => f p x = 0)).card = p ^ 2 := by
  classical
  have h := Module.card_eq_pow_finrank (K := ZMod p) (V := LinearMap.ker (f p))
  rw [finrank_ker_f, ZMod.card] at h
  rw [← h, ← Fintype.card_subtype]
  exact Fintype.card_congr (Equiv.subtypeEquivRight (fun x => by simp [LinearMap.mem_ker]))

lemma card_ker_f_ne_zero : (univ.filter (fun x : K p => x ≠ 0 ∧ f p x = 0)).card = p ^ 2 - 1 := by
  classical
  have : univ.filter (fun x : K p => x ≠ 0 ∧ f p x = 0) = (univ.filter (fun x : K p => f p x = 0)).erase 0 := by
    ext x; simp
  rw [this, card_erase_of_mem (by simp), card_ker_f]

/-- `m = p^2 + p + 1`. -/
abbrev m : ℕ := p ^ 2 + p + 1

lemma pm1_mul_m : (p - 1) * m p = p ^ 3 - 1 := by
  have h2 := hp.out.two_le
  obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
  simp only [Nat.add_sub_cancel, m]
  refine (Nat.sub_eq_of_eq_add ?_).symm
  ring

variable {p}

section gen

variable (g : (K p)ˣ) (hg : ∀ x, x ∈ Subgroup.zpowers g)
include hg

lemma orderOf_g : orderOf g = p ^ 3 - 1 := by
  classical
  rw [orderOf_eq_card_of_forall_mem_zpowers hg, Nat.card_eq_fintype_card, Fintype.card_units, card_K]

lemma exists_pow_eq (w : K p) (hw : w ≠ 0) : ∃ n : ℕ, n < p ^ 3 - 1 ∧ (g : K p) ^ n = w := by
  have hmem : Units.mk0 w hw ∈ Submonoid.powers g := (mem_powers_iff_mem_zpowers).mpr (hg _)
  obtain ⟨n, hn⟩ := hmem
  refine ⟨n % orderOf g, ?_, ?_⟩
  · rw [← orderOf_g g hg]
    exact Nat.mod_lt _ (orderOf_pos g)
  · have h1 : g ^ (n % orderOf g) = Units.mk0 w hw := by rw [pow_mod_orderOf]; exact hn
    rw [← Units.val_pow_eq_pow_val, h1]
    rfl

lemma gm_mem : ∃ c : ZMod p, c ≠ 0 ∧ (g : K p) ^ m p = algebraMap (ZMod p) (K p) c := by
  classical
  set y : (K p)ˣ := g ^ m p with hy_def
  have hy : y ^ (p - 1) = 1 := by
    rw [hy_def, ← pow_mul, mul_comm, pm1_mul_m, ← orderOf_g g hg, pow_orderOf_eq_one]
  let φ : (ZMod p)ˣ →* (K p)ˣ := Units.map (algebraMap (ZMod p) (K p)).toMonoidHom
  have hφ : Function.Injective φ := by
    intro a b hab
    ext
    have := congrArg (fun u : (K p)ˣ => (u : K p)) hab
    simp only [φ, Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe] at this
    exact (algebraMap (ZMod p) (K p)).injective this
  have hT : (univ.image φ) ⊆ univ.filter (fun a : (K p)ˣ => a ^ (p - 1) = 1) := by
    intro a ha
    simp only [mem_image, mem_univ, true_and] at ha
    obtain ⟨u, rfl⟩ := ha
    simp only [mem_filter, mem_univ, true_and]
    rw [← map_pow, ZMod.units_pow_card_sub_one_eq_one, map_one]
  have hcardT : (univ.image φ).card = p - 1 := by
    rw [card_image_of_injective _ hφ, card_univ, ZMod.card_units]
  have hcardS := IsCyclic.card_pow_eq_one_le (α := (K p)ˣ) (n := p - 1)
    (by have := hp.out.two_le; omega)
  have heq : univ.image φ = univ.filter (fun a : (K p)ˣ => a ^ (p - 1) = 1) :=
    eq_of_subset_of_card_le hT (by rw [hcardT]; exact hcardS)
  have hmem : y ∈ univ.image φ := by rw [heq]; simp [hy]
  obtain ⟨u, -, hu⟩ := mem_image.mp hmem
  refine ⟨(u : ZMod p), u.ne_zero, ?_⟩
  have := congrArg (fun u : (K p)ˣ => (u : K p)) hu
  simp only [φ, Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe, hy_def,
    Units.val_pow_eq_pow_val] at this
  exact this.symm

lemma f_pow_mod (n : ℕ) : f p ((g : K p) ^ n) = 0 ↔ f p ((g : K p) ^ (n % m p)) = 0 := by
  obtain ⟨c, hc, hgm⟩ := gm_mem g hg
  have : (g : K p) ^ n = c ^ (n / m p) • (g : K p) ^ (n % m p) := by
    conv_lhs => rw [← Nat.mod_add_div n (m p)]
    rw [pow_add, pow_mul, hgm, ← map_pow, Algebra.smul_def, mul_comm]
  rw [this, map_smul, smul_eq_mul, mul_eq_zero, or_iff_right (pow_ne_zero _ hc)]

end gen

lemma mod_helper {m i j : ℕ} (hi : i < m) (hj : j < m) (h : (i + m - j) % m = 0) : i = j := by
  rcases lt_trichotomy i j with hlt | heq | hgt
  · have : i + m - j < m := by omega
    rw [Nat.mod_eq_of_lt this] at h
    omega
  · exact heq
  · have : i + m - j = (i - j) + m := by omega
    rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)] at h
    omega

lemma mod_helper2 {m i j e : ℕ} (hj : j < m) (he : e < m) (h : (j + e) % m = i) :
    (i + m - j) % m = e ∧ (0 < e → i ≠ j) := by
  rcases Nat.lt_or_ge (j + e) m with h1 | h1
  · rw [Nat.mod_eq_of_lt h1] at h
    subst h
    constructor
    · rw [show j + e + m - j = e + m by omega, Nat.add_mod_right, Nat.mod_eq_of_lt he]
    · omega
  · have : (j + e) % m = j + e - m := by
      rw [Nat.mod_eq_sub_mod h1, Nat.mod_eq_of_lt (by omega)]
    rw [this] at h
    subst h
    constructor
    · rw [show j + e - m + m - j = e by omega, Nat.mod_eq_of_lt he]
    · omega

section gen2

variable (g : (K p)ˣ)

/-- The Singer difference set `{i < m : f(g^i) = 0}`. -/
noncomputable def D : Finset ℕ := (range (m p)).filter (fun i => f p ((g : K p) ^ i) = 0)

variable (hg : ∀ x, x ∈ Subgroup.zpowers g)
include hg

lemma count_range_mul (k : ℕ) :
    ((range (k * m p)).filter (fun n => f p ((g : K p) ^ n) = 0)).card = k * (D g).card := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [card_filter] at ih ⊢
    rw [Nat.succ_mul, sum_range_add, ih, Nat.succ_mul]
    congr 1
    rw [D, card_filter]
    apply sum_congr rfl
    intro j hj
    have hj' : j < m p := mem_range.mp hj
    have hmod : (k * m p + j) % m p = j := by
      rw [add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hj']
    have key : (f p ((g : K p) ^ (k * m p + j)) = 0) ↔ (f p ((g : K p) ^ j) = 0) := by
      rw [f_pow_mod g hg, hmod]
    simp only [key]

lemma card_D : (D g).card = p + 1 := by
  have h1 := count_range_mul g hg (p - 1)
  rw [pm1_mul_m] at h1
  have h2 : ((range (p ^ 3 - 1)).filter (fun n => f p ((g : K p) ^ n) = 0)).card = p ^ 2 - 1 := by
    rw [← card_ker_f_ne_zero p]
    apply card_bij (fun n _ => (g : K p) ^ n)
    · intro n hn
      simp only [mem_filter, mem_range, mem_univ, true_and] at hn ⊢
      exact ⟨pow_ne_zero _ g.ne_zero, hn.2⟩
    · intro a ha b hb hab
      simp only [mem_filter, mem_range] at ha hb
      have ha' : a ∈ Set.Iio (orderOf g) := by rw [orderOf_g g hg]; exact ha.1
      have hb' : b ∈ Set.Iio (orderOf g) := by rw [orderOf_g g hg]; exact hb.1
      exact pow_injOn_Iio_orderOf ha' hb'
        (Units.ext (by rw [Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val]; exact hab))
    · intro w hw
      simp only [mem_filter, mem_univ, true_and] at hw
      obtain ⟨n, hn, rfl⟩ := exists_pow_eq g hg w hw.1
      exact ⟨n, by simp [hn, hw.2], rfl⟩
  rw [h2] at h1
  have h3 : p ^ 2 - 1 = (p - 1) * (p + 1) := by
    have h2 := hp.out.two_le
    obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
    simp only [Nat.add_sub_cancel]
    refine Nat.sub_eq_of_eq_add ?_
    ring
  have hp1 : 0 < p - 1 := by have := hp.out.two_le; omega
  exact Nat.eq_of_mul_eq_mul_left hp1 (h1.symm.trans h3)

lemma diff_cover (e : ℕ) :
    ∃ i ∈ D g, ∃ j ∈ D g, (j + e) % m p = i := by
  let φ : K p →ₗ[ZMod p] ZMod p × ZMod p :=
    (f p).prod ((f p).comp (LinearMap.mulLeft (ZMod p) ((g : K p) ^ e)))
  have hker : LinearMap.ker φ ≠ ⊥ := LinearMap.ker_ne_bot_of_finrank_lt (by
    rw [Module.finrank_prod, Module.finrank_self, finrank_K]; norm_num)
  obtain ⟨w, hw, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker
  rw [LinearMap.mem_ker] at hw
  have hw1 : f p w = 0 := by
    have := congrArg Prod.fst hw; simpa [φ] using this
  have hw2 : f p ((g : K p) ^ e * w) = 0 := by
    have := congrArg Prod.snd hw; simpa [φ] using this
  obtain ⟨n, -, rfl⟩ := exists_pow_eq g hg w hw0
  have h1 : f p ((g : K p) ^ n) = 0 := hw1
  have h2 : f p ((g : K p) ^ (n + e)) = 0 := by rw [pow_add, mul_comm]; exact hw2
  have hm0 : 0 < m p := by positivity
  refine ⟨(n + e) % m p, ?_, n % m p, ?_, ?_⟩
  · simp only [D, mem_filter, mem_range]
    exact ⟨Nat.mod_lt _ hm0, (f_pow_mod g hg _).mp h2⟩
  · simp only [D, mem_filter, mem_range]
    exact ⟨Nat.mod_lt _ hm0, (f_pow_mod g hg _).mp h1⟩
  · exact Nat.mod_add_mod n (m p) e

omit hg in
lemma D_lt (i : ℕ) (hi : i ∈ D g) : i < m p := by
  simp only [D, mem_filter, mem_range] at hi; exact hi.1

lemma D_sidon : IsSidon ((D g : Finset ℕ) : Set ℕ) := by
  have hm0 : 0 < m p := by positivity
  have hinj : ∀ a₁ ∈ (D g).offDiag, ∀ a₂ ∈ (D g).offDiag,
      (a₁.1 + m p - a₁.2) % m p = (a₂.1 + m p - a₂.2) % m p → a₁ = a₂ := by
    intro a₁ ha₁ a₂ ha₂ heq
    refine Finset.inj_on_of_surj_on_of_card_le (s := (D g).offDiag) (t := (range (m p)).erase 0)
      (fun a _ => (a.1 + m p - a.2) % m p) ?_ ?_ ?_ ha₁ ha₂ heq
    · rintro ⟨i, j⟩ hij
      simp only [mem_offDiag] at hij
      simp only [mem_erase, mem_range]
      exact ⟨fun h0 => hij.2.2 (mod_helper (D_lt g i hij.1) (D_lt g j hij.2.1) h0),
        Nat.mod_lt _ hm0⟩
    · intro e he
      simp only [mem_erase, mem_range] at he
      obtain ⟨i, hi, j, hj, hij⟩ := diff_cover g hg e
      obtain ⟨h1, h2⟩ := mod_helper2 (D_lt g j hj) he.2 hij
      exact ⟨(i, j), mem_offDiag.mpr ⟨hi, hj, h2 (Nat.pos_of_ne_zero he.1)⟩, h1⟩
    · rw [offDiag_card, card_D g hg, card_erase_of_mem (by simp [hm0]), card_range]
      have : (p + 1) * (p + 1) = p ^ 2 + 2 * p + 1 := by ring
      rw [this]
      simp only [m]
      omega
  intro i₁ hi₁ j₁ hj₁ i₂ hi₂ j₂ hj₂ h
  simp only [Finset.mem_coe] at hi₁ hj₁ hi₂ hj₂
  by_cases hij : i₁ = j₁
  · left; exact ⟨hij, by omega⟩
  · right
    have hl1 := D_lt g j₁ hj₁
    have hl2 := D_lt g i₂ hi₂
    have hne : j₂ ≠ i₂ := by omega
    have := hinj (i₁, j₁) (mem_offDiag.mpr ⟨hi₁, hj₁, hij⟩) (j₂, i₂)
      (mem_offDiag.mpr ⟨hj₂, hi₂, hne⟩) (by simp only; congr 1; omega)
    simp only [Prod.mk.injEq] at this
    exact ⟨this.1, this.2.symm⟩

end gen2

end SingerConstr

namespace Erdos30

open KnownBounds

/-- `h` is monotone. -/
theorem h_mono {N N' : ℕ} (hNN : N ≤ N') : h N ≤ h N' := by
  obtain ⟨B, hB, hS, hc⟩ := exists_sidon_card_eq_h N
  rw [← hc]
  exact card_le_h (hB.trans (Finset.Icc_subset_Icc le_rfl hNN)) hS

/-- **Singer's theorem** (1938): for every prime `p`, `h (p^2 + p + 1) ≥ p + 1`. -/
theorem singer_le_h (p : ℕ) [Fact p.Prime] : p + 1 ≤ h (p ^ 2 + p + 1) := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := (SingerConstr.K p)ˣ)
  let A := (SingerConstr.D g).image (· + 1)
  have hA : A ⊆ Finset.Icc 1 (p ^ 2 + p + 1) := by
    intro x hx
    simp only [A, Finset.mem_image] at hx
    obtain ⟨i, hi, rfl⟩ := hx
    have := SingerConstr.D_lt g i hi
    simp only [SingerConstr.m] at this
    simp only [Finset.mem_Icc]
    omega
  have hS : IsSidon (A : Set ℕ) := by
    intro a ha b hb c hc d hd habcd
    simp only [A, Finset.coe_image, Set.mem_image, Finset.mem_coe] at ha hb hc hd
    obtain ⟨a', ha', rfl⟩ := ha
    obtain ⟨b', hb', rfl⟩ := hb
    obtain ⟨c', hc', rfl⟩ := hc
    obtain ⟨d', hd', rfl⟩ := hd
    have := SingerConstr.D_sidon g hg a' ha' b' hb' c' hc' d' hd' (by omega)
    omega
  have hcard : A.card = p + 1 := by
    rw [Finset.card_image_of_injective _ (add_left_injective 1), SingerConstr.card_D g hg]
  calc p + 1 = A.card := hcard.symm
    _ ≤ h (p ^ 2 + p + 1) := card_le_h hA hS

/-- `√N ≤ h N` for infinitely many `N` (so `h N - √N` is not eventually negative). -/
theorem frequently_sqrt_le_h : ∃ᶠ N : ℕ in Filter.atTop, Real.sqrt (N : ℝ) ≤ h N := by
  rw [Filter.frequently_atTop]
  intro N₀
  obtain ⟨p, hpN, hp⟩ := Nat.exists_infinite_primes N₀
  haveI := Fact.mk hp
  refine ⟨p ^ 2 + p + 1, by nlinarith, ?_⟩
  have h1 := singer_le_h p
  have h2 : Real.sqrt ((p ^ 2 + p + 1 : ℕ) : ℝ) ≤ p + 1 :=
    Real.sqrt_le_iff.mpr ⟨by positivity, by push_cast; nlinarith⟩
  calc Real.sqrt ((p ^ 2 + p + 1 : ℕ) : ℝ) ≤ p + 1 := h2
    _ ≤ h (p ^ 2 + p + 1) := by exact_mod_cast h1

/-- A lower bound valid for all `N`: `(√N - 1)/2 ≤ h N` (Singer's construction + Bertrand). -/
theorem sqrt_sub_one_div_two_le_h (N : ℕ) : (Real.sqrt N - 1) / 2 ≤ h N := by
  set s := Nat.sqrt N with hs
  have hNs : N < (s + 1) ^ 2 := Nat.lt_succ_sqrt' N
  have hsqrt : Real.sqrt N < s + 1 := by
    rw [Real.sqrt_lt' (by positivity)]
    exact_mod_cast hNs
  by_cases hs3 : s < 3
  · rcases Nat.eq_zero_or_pos N with hN0 | hN
    · subst hN0
      norm_num
    · have h1 : 1 ≤ h N := by
        have := card_le_h (N := N) (B := {1}) (by simp; omega) (by
          intro a ha b hb c hc d hd _
          simp only [Finset.coe_singleton, Set.mem_singleton_iff] at ha hb hc hd
          subst ha hb hc hd
          left; exact ⟨rfl, rfl⟩)
        simpa using this
      have h2 : (s : ℝ) + 1 ≤ 3 := by exact_mod_cast (by omega : s + 1 ≤ 3)
      have h3 : (1 : ℝ) ≤ h N := by exact_mod_cast h1
      linarith
  · push_neg at hs3
    set n := (s - 1) / 2 with hn
    have hn1 : n ≠ 0 := by omega
    obtain ⟨q, hq, hnq, hq2n⟩ := Nat.exists_prime_lt_and_le_two_mul n hn1
    haveI := Fact.mk hq
    have hqs : q + 1 ≤ s := by omega
    have hsN : s ^ 2 ≤ N := Nat.sqrt_le' N
    have hqN : q ^ 2 + q + 1 ≤ N := by nlinarith
    have h1 : q + 1 ≤ h N := (singer_le_h q).trans (h_mono hqN)
    have h3 : (s : ℝ) ≤ 2 * q := by exact_mod_cast (by omega : s ≤ 2 * q)
    have h4 : ((q : ℝ) + 1) ≤ h N := by exact_mod_cast h1
    linarith

end Erdos30
