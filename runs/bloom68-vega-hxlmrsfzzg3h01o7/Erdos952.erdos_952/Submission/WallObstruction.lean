import FormalConjecturesUtil
import Submission.DiscreteStream

/-!
# A finite-quotient current obstruction to infinite white king walks

The hypotheses concern currents, not a construction of a black path. A
surjective finite additive quotient of the Gaussian integers has kernel
spanned over `ℤ` by `p` and `I * p`. A divergence-free quotient current,
vanishing at all four edges incident to white vertices and having nonzero
total flux, supplies two invariants of white king walks. They are a stream
function `H` and `H ∘ Rinv`, where `Rinv (x,y) = (y-1,-x)`.

The two period increments cannot both vanish: otherwise `H` descends to the
finite quotient, where the sums of its forward differences vanish. The two
invariants and a residue then determine a vertex. Thus an injective infinite
white king sequence is impossible, by finite-residue pigeonhole.

No path-current construction, Jordan curve theorem, or homology is used.
This is a generic finite-wall theorem, not the Gaussian moat conjecture.
-/

namespace Erdos952.WallObstruction

open scoped BigOperators

abbrev G := GaussianInt

/-- The northward unit Gaussian integer. -/
def I : G := ⟨0, 1⟩

@[simp] theorem I_re : I.re = 0 := rfl
@[simp] theorem I_im : I.im = 1 := rfl

/-- The affine quarter turn preserving the intended black wall. -/
def R (u : G) : G := ⟨-u.im, u.re + 1⟩

/-- Its inverse. We only require that this map preserve white vertices. -/
def Rinv (u : G) : G := ⟨u.im - 1, -u.re⟩

@[simp] theorem R_Rinv (u : G) : R (Rinv u) = u := by
  ext <;> simp [R, Rinv]

@[simp] theorem Rinv_R (u : G) : Rinv (R u) = u := by
  ext <;> simp [R, Rinv]

/-- Black preservation by `R` implies the white preservation actually used. -/
theorem white_Rinv_of_black_R {B : G → Prop}
    (hR : ∀ u, B u → B (R u)) {u : G} (hu : ¬ B u) : ¬ B (Rinv u) := by
  intro h
  exact hu (by simpa using hR (Rinv u) h)

/-- King adjacency, allowing a stationary step. Injective sequences of course
have no stationary steps. Both coordinate differences have absolute value at
most one. -/
def KingAdjacent (u v : G) : Prop :=
  |v.re - u.re| ≤ 1 ∧ |v.im - u.im| ≤ 1

theorem KingAdjacent.symm {u v : G} (h : KingAdjacent u v) : KingAdjacent v u := by
  simpa only [KingAdjacent, abs_sub_comm] using h

/-- The inverse affine quarter turn preserves king adjacency. -/
theorem KingAdjacent.Rinv {u v : G} (h : KingAdjacent u v) :
    KingAdjacent (Rinv u) (Rinv v) := by
  rcases h with ⟨hx, hy⟩
  constructor
  · simpa [Erdos952.WallObstruction.Rinv] using hy
  · change |-v.re - -u.re| ≤ 1
    rw [neg_sub_neg, abs_sub_comm]
    exact hx

section Currents

variable {α : Type*} [AddCommGroup α]

/-- Pull back a quotient current to the integer grid. -/
def liftCurrent (r : G →+ α) (C : α → ℤ) : DiscreteStream.GridFunction :=
  fun x y => C (r ⟨x, y⟩)

/-- Stream gradients with exactly the indexing of `DiscreteStream`. -/
abbrev IsStream (r : G →+ α) (Cx Cy : α → ℤ) (H : G → ℤ) : Prop :=
  DiscreteStream.IsStreamFunction (liftCurrent r Cx) (liftCurrent r Cy)
    (fun x y => H ⟨x, y⟩)

/-- Backward divergence of the current vanishes at every lattice vertex. -/
def DivergenceFree (r : G →+ α) (Cx Cy : α → ℤ) : Prop :=
  ∀ u : G, Cx (r u) - Cx (r (u - 1)) + Cy (r u) - Cy (r (u - I)) = 0

/-- The Gaussian and coordinate divergence conventions agree. -/
theorem DivergenceFree.grid {r : G →+ α} {Cx Cy : α → ℤ}
    (hd : DivergenceFree r Cx Cy) :
    DiscreteStream.DivergenceFree (liftCurrent r Cx) (liftCurrent r Cy) := by
  intro x y
  have hx : (⟨x, y⟩ : G) - 1 = ⟨x - 1, y⟩ := by ext <;> simp
  have hy : (⟨x, y⟩ : G) - I = ⟨x, y - 1⟩ := by ext <;> simp
  simpa only [liftCurrent, hx, hy] using hd ⟨x, y⟩

/-- All four currents incident to a white vertex vanish. -/
def WhiteZero (r : G →+ α) (B : G → Prop) (Cx Cy : α → ℤ) : Prop :=
  ∀ u : G, ¬ B u →
    Cx (r u) = 0 ∧ Cx (r (u - 1)) = 0 ∧
      Cy (r u) = 0 ∧ Cy (r (u - I)) = 0

/-- Coordinate form of the white support condition. -/
theorem WhiteZero.grid {r : G →+ α} {B : G → Prop} {Cx Cy : α → ℤ}
    (hw : WhiteZero r B Cx Cy) (x y : ℤ) (hu : ¬ B ⟨x, y⟩) :
    liftCurrent r Cx x y = 0 ∧ liftCurrent r Cx (x - 1) y = 0 ∧
      liftCurrent r Cy x y = 0 ∧ liftCurrent r Cy x (y - 1) = 0 := by
  have h := hw ⟨x, y⟩ hu
  have hx : (⟨x, y⟩ : G) - 1 = ⟨x - 1, y⟩ := by ext <;> simp
  have hy : (⟨x, y⟩ : G) - I = ⟨x, y - 1⟩ := by ext <;> simp
  simpa only [liftCurrent, hx, hy] using h

/-- The discrete Poincaré lemma, expressed on Gaussian integer vertices. -/
theorem exists_stream (r : G →+ α) (Cx Cy : α → ℤ)
    (hdiv : DivergenceFree r Cx Cy) :
    ∃ H : G → ℤ, H 0 = 0 ∧ IsStream r Cx Cy H := by
  obtain ⟨H, h0, hx, hy⟩ :=
    DiscreteStream.discrete_poincare (liftCurrent r Cx) (liftCurrent r Cy) hdiv.grid
  exact ⟨fun u => H u.re u.im, h0, hx, hy⟩

variable {r : G →+ α} {Cx Cy : α → ℤ} {H : G → ℤ}

/-- Eastward stream difference. -/
theorem IsStream.east (hH : IsStream r Cx Cy H) (u : G) :
    H (u + 1) - H u = Cy (r (u + 1)) := by
  have he : u + 1 = (⟨u.re + 1, u.im⟩ : G) := by ext <;> simp
  simpa only [he, liftCurrent] using hH.dx u.re u.im

/-- Northward stream difference. -/
theorem IsStream.north (hH : IsStream r Cx Cy H) (u : G) :
    H (u + I) - H u = -Cx (r (u + I)) := by
  have he : u + I = (⟨u.re, u.im + 1⟩ : G) := by ext <;> simp
  simpa only [he, liftCurrent] using hH.dy u.re u.im

/-- Northeast difference: both terms are incident to the northeast endpoint. -/
theorem IsStream.northeast (hH : IsStream r Cx Cy H) (u : G) :
    H (u + 1 + I) - H u = Cy (r (u + 1)) - Cx (r (u + 1 + I)) := by
  have hx := hH.east u
  have hy := hH.north (u + 1)
  omega

/-- Southeast difference: one term is incident to each endpoint. -/
theorem IsStream.southeast (hH : IsStream r Cx Cy H) (u : G) :
    H (u + 1 - I) - H u = Cx (r u) + Cy (r (u + 1 - I)) := by
  have hy := hH.north (u - I)
  have hx := hH.east (u - I)
  have he : u - I + 1 = u + 1 - I := by abel
  simp only [sub_add_cancel, he] at hx hy
  omega

variable {B : G → Prop}

/-- White king edges do not change the stream value. The four forward
cases use the displayed stream differences; the other four are reversals. -/
theorem IsStream.eq_of_white_king (hH : IsStream r Cx Cy H)
    (hw : WhiteZero r B Cx Cy) {u v : G}
    (hu : ¬ B u) (hv : ¬ B v) (huv : KingAdjacent u v) : H u = H v := by
  have east (a : G) (ha : ¬ B (a + 1)) : H a = H (a + 1) := by
    have hz := (hw (a + 1) ha).2.2.1
    have hd := hH.east a
    omega
  have north (a : G) (ha : ¬ B (a + I)) : H a = H (a + I) := by
    have hz := (hw (a + I) ha).1
    have hd := hH.north a
    omega
  have northeast (a : G) (ha : ¬ B (a + 1 + I)) : H a = H (a + 1 + I) := by
    have hz := hw (a + 1 + I) ha
    have hd := hH.northeast a
    simp only [add_sub_cancel_right] at hz
    omega
  have southeast (a : G) (ha : ¬ B a) (hb : ¬ B (a + 1 - I)) :
      H a = H (a + 1 - I) := by
    have hz := (hw a ha).1
    have hz' := (hw (a + 1 - I) hb).2.2.1
    have hd := hH.southeast a
    omega
  obtain ⟨hx, hy⟩ := huv
  rw [abs_le] at hx hy
  have hxs : v.re = u.re - 1 ∨ v.re = u.re ∨ v.re = u.re + 1 := by omega
  have hys : v.im = u.im - 1 ∨ v.im = u.im ∨ v.im = u.im + 1 := by omega
  rcases hxs with hx | hx | hx <;> rcases hys with hy | hy | hy
  · have he : u = v + 1 + I := by ext <;> simp_all
    simpa only [← he] using (northeast v (by simpa only [← he] using hu)).symm
  · have he : u = v + 1 := by ext <;> simp_all
    simpa only [← he] using (east v (by simpa only [← he] using hu)).symm
  · have he : u = v + 1 - I := by ext <;> simp_all
    simpa only [← he] using (southeast v hv (by simpa only [← he] using hu)).symm
  · have he : u = v + I := by ext <;> simp_all
    simpa only [← he] using (north v (by simpa only [← he] using hu)).symm
  · have he : u = v := by ext <;> omega
    exact congrArg H he
  · have he : v = u + I := by ext <;> simp_all
    simpa only [← he] using north u (by simpa only [← he] using hv)
  · have he : v = u + 1 - I := by ext <;> simp_all
    simpa only [← he] using southeast u hu (by simpa only [← he] using hv)
  · have he : v = u + 1 := by ext <;> simp_all
    simpa only [← he] using east u (by simpa only [← he] using hv)
  · have he : v = u + 1 + I := by ext <;> simp_all
    simpa only [← he] using northeast u (by simpa only [← he] using hv)

/-- `H ∘ Rinv` is a white-king invariant. It is not asserted to be the
stream function of a naively rotated current (the face offsets differ). -/
theorem IsStream.rotated_eq_of_white_king (hH : IsStream r Cx Cy H)
    (hw : WhiteZero r B Cx Cy) (hR : ∀ u, ¬ B u → ¬ B (Rinv u))
    {u v : G} (hu : ¬ B u) (hv : ¬ B v) (huv : KingAdjacent u v) :
    H (Rinv u) = H (Rinv v) :=
  hH.eq_of_white_king hw (hR u hu) (hR v hv) huv.Rinv

end Currents

/- ## The additive period homomorphism -/

section Periods

variable {α : Type*} [AddCommGroup α]
variable {r : G →+ α} {Cx Cy : α → ℤ} {H : G → ℤ}

/-- Every kernel translation preserves the lifted current, so the stream
increment is independent of the base point. -/
theorem IsStream.kernel_increment (hH : IsStream r Cx Cy H)
    {t : G} (ht : r t = 0) (u : G) :
    H (u + t) - H u = H t - H 0 := by
  have hperiod (C : α → ℤ) : ∀ x y : ℤ,
      liftCurrent r C (x + t.re) (y + t.im) = liftCurrent r C x y := by
    intro x y
    change C (r ((⟨x, y⟩ : G) + t)) = C (r ⟨x, y⟩)
    rw [map_add, ht, add_zero]
  exact DiscreteStream.translation_increment_constant hH t.re t.im
    (hperiod Cx) (hperiod Cy) u.re u.im

/-- The integer period increment is an additive homomorphism on `ker r`.
This packages all positive and negative integer multiples of a period. -/
def IsStream.periodHom (hH : IsStream r Cx Cy H) : r.ker →+ ℤ where
  toFun t := H t - H 0
  map_zero' := sub_self _
  map_add' t μ := by
    change H ((t : G) + (μ : G)) - H 0 = (H t - H 0) + (H μ - H 0)
    have h := hH.kernel_increment μ.property (t : G)
    omega

@[simp] theorem IsStream.periodHom_apply (hH : IsStream r Cx Cy H) (t : r.ker) :
    hH.periodHom t = H t - H 0 := rfl

/-- The period formula on the integer span of `p` and `I*p`. -/
theorem IsStream.span_increment (hH : IsStream r Cx Cy H)
    (p : G) (hp : r p = 0) (hIp : r (I * p) = 0) (m n : ℤ) (u : G) :
    H (u + (m • p + n • (I * p))) - H u =
      m * (H p - H 0) + n * (H (I * p) - H 0) := by
  let P : r.ker := ⟨p, hp⟩
  let Q : r.ker := ⟨I * p, hIp⟩
  calc
    H (u + (m • p + n • (I * p))) - H u = hH.periodHom (m • P + n • Q) :=
      hH.kernel_increment (m • P + n • Q).property u
    _ = m * (H p - H 0) + n * (H (I * p) - H 0) := by
      rw [map_add, map_zsmul, map_zsmul]
      simp [P, Q]

/-- On translation vectors the inverse affine rotation sends `p` to `-I*p`
and `I*p` to `p`. The affine offset cancels. -/
theorem Rinv_span (u p : G) (m n : ℤ) :
    Rinv (u + (m • p + n • (I * p))) =
      Rinv u + (n • p + (-m) • (I * p)) := by
  ext <;> simp [Rinv, I, zsmul_eq_mul] <;> ring

/-- The second invariant has period increment `n*α₀ - m*β₀`. -/
theorem IsStream.rotated_span_increment (hH : IsStream r Cx Cy H)
    (p : G) (hp : r p = 0) (hIp : r (I * p) = 0) (m n : ℤ) (u : G) :
    H (Rinv (u + (m • p + n • (I * p)))) - H (Rinv u) =
      n * (H p - H 0) - m * (H (I * p) - H 0) := by
  rw [Rinv_span]
  simpa only [neg_mul, sub_eq_add_neg] using hH.span_increment p hp hIp n (-m) (Rinv u)

/-- If the two basic periods vanish, the stream is constant on residue fibers. -/
theorem IsStream.eq_of_residue_of_zero_periods (hH : IsStream r Cx Cy H)
    (p : G) (hp : r p = 0) (hIp : r (I * p) = 0)
    (hker : ∀ u v : G, r u = r v →
      ∃ m n : ℤ, v - u = m • p + n • (I * p))
    (ha : H p - H 0 = 0) (hb : H (I * p) - H 0 = 0)
    {u v : G} (huv : r u = r v) : H u = H v := by
  obtain ⟨m, n, hmn⟩ := hker u v huv
  have he : u + (m • p + n • (I * p)) = v := by rw [← hmn]; abel
  have hd := hH.span_increment p hp hIp m n u
  rw [he, ha, hb] at hd
  omega

end Periods

/- ## Finite-quotient descent detects nonzero periods -/

section FiniteQuotient

variable {α : Type*} [AddCommGroup α] [Fintype α]

/-- A forward difference on a finite additive group has total sum zero.
Translation is a permutation, even if the translating element is zero. -/
theorem sum_eq_zero_of_forward_difference (F C : α → ℤ) (a : α)
    (h : ∀ b, F (b + a) - F b = C (b + a)) : (∑ b : α, C b) = 0 := by
  have hs : (∑ b : α, (F (b + a) - F b)) = ∑ b : α, C (b + a) :=
    Finset.sum_congr rfl (fun b _ => h b)
  have hsum (f : α → ℤ) : (∑ b : α, f (b + a)) = ∑ b : α, f b := by
    simpa only [Equiv.coe_addRight] using Equiv.sum_comp (Equiv.addRight a) f
  rw [Finset.sum_sub_distrib, hsum F, sub_self, hsum C] at hs
  exact hs.symm

variable {r : G →+ α} {Cx Cy : α → ℤ} {H : G → ℤ}

/-- A stream descending to the finite quotient forces both current totals
to vanish. Surjectivity is used to obtain gradients at every residue. -/
theorem IsStream.sums_eq_zero_of_descends (hH : IsStream r Cx Cy H)
    (hr : Function.Surjective r) (F : α → ℤ) (hF : ∀ u, F (r u) = H u) :
    (∑ a : α, Cx a) = 0 ∧ (∑ a : α, Cy a) = 0 := by
  have hx : ∀ a : α, F (a + r 1) - F a = Cy (a + r 1) := by
    intro a
    obtain ⟨u, rfl⟩ := hr a
    simpa only [← map_add, hF] using hH.east u
  have hy : ∀ a : α, (-F (a + r I)) - (-F a) = Cx (a + r I) := by
    intro a
    obtain ⟨u, rfl⟩ := hr a
    have h := hH.north u
    simp only [← map_add, hF]
    omega
  exact ⟨sum_eq_zero_of_forward_difference (fun a => -F a) Cx (r I) hy,
    sum_eq_zero_of_forward_difference F Cy (r 1) hx⟩

/-- Nonzero total current forbids simultaneous vanishing of the two basic
period increments. No rectangular coordinate period is assumed. -/
theorem IsStream.periods_not_both_zero (hH : IsStream r Cx Cy H)
    (hr : Function.Surjective r) (p : G) (hp : r p = 0) (hIp : r (I * p) = 0)
    (hker : ∀ u v : G, r u = r v →
      ∃ m n : ℤ, v - u = m • p + n • (I * p))
    (hflux : (∑ a : α, Cx a) ≠ 0 ∨ (∑ a : α, Cy a) ≠ 0) :
    H p - H 0 ≠ 0 ∨ H (I * p) - H 0 ≠ 0 := by
  classical
  by_contra h
  push_neg at h
  obtain ⟨ha, hb⟩ := h
  have hr' := hr
  choose s hs using hr'
  let F : α → ℤ := fun a => H (s a)
  have hF : ∀ u, F (r u) = H u := by
    intro u
    exact hH.eq_of_residue_of_zero_periods p hp hIp hker ha hb (hs (r u))
  obtain ⟨hx, hy⟩ := hH.sums_eq_zero_of_descends hr F hF
  exact hflux.elim (fun h => h hx) (fun h => h hy)

end FiniteQuotient

/- ## Two invariants separate vertices of the same residue -/

/-- The determinant of the two period equations is a positive sum of squares. -/
theorem zero_of_two_period_equations {a b m n : ℤ} (hab : a ≠ 0 ∨ b ≠ 0)
    (h₁ : m * a + n * b = 0) (h₂ : n * a - m * b = 0) : m = 0 ∧ n = 0 := by
  have hpos : 0 < a ^ 2 + b ^ 2 := by
    rcases hab with ha | hb
    · nlinarith [sq_pos_of_ne_zero ha, sq_nonneg b]
    · nlinarith [sq_pos_of_ne_zero hb, sq_nonneg a]
  have hm : m * (a ^ 2 + b ^ 2) = 0 := by
    calc
      m * (a ^ 2 + b ^ 2) = (m * a + n * b) * a - (n * a - m * b) * b := by ring
      _ = 0 := by rw [h₁, h₂]; ring
  have hn : n * (a ^ 2 + b ^ 2) = 0 := by
    calc
      n * (a ^ 2 + b ^ 2) = (m * a + n * b) * b + (n * a - m * b) * a := by ring
      _ = 0 := by rw [h₁, h₂]; ring
  exact ⟨(mul_eq_zero.mp hm).resolve_right (ne_of_gt hpos),
    (mul_eq_zero.mp hn).resolve_right (ne_of_gt hpos)⟩

section Separation

variable {α : Type*} [AddCommGroup α]
variable {r : G →+ α} {Cx Cy : α → ℤ} {H : G → ℤ}

/-- Equal residues and equal values of both invariants force equal vertices.
This is purely the period calculation; finiteness enters only when proving
that the basic periods cannot both be zero. -/
theorem IsStream.eq_of_residue_and_invariants (hH : IsStream r Cx Cy H)
    (p : G) (hp : r p = 0) (hIp : r (I * p) = 0)
    (hker : ∀ u v : G, r u = r v →
      ∃ m n : ℤ, v - u = m • p + n • (I * p))
    (hperiod : H p - H 0 ≠ 0 ∨ H (I * p) - H 0 ≠ 0)
    {u v : G} (huv : r u = r v) (h₁ : H u = H v) (h₂ : H (Rinv u) = H (Rinv v)) :
    u = v := by
  obtain ⟨m, n, hmn⟩ := hker u v huv
  have he : u + (m • p + n • (I * p)) = v := by rw [← hmn]; abel
  have hd := hH.span_increment p hp hIp m n u
  have hk := hH.rotated_span_increment p hp hIp m n u
  rw [he] at hd hk
  have hm : m * (H p - H 0) + n * (H (I * p) - H 0) = 0 := by omega
  have hn : n * (H p - H 0) - m * (H (I * p) - H 0) = 0 := by omega
  obtain ⟨hm0, hn0⟩ := zero_of_two_period_equations hperiod hm hn
  rw [hm0, hn0, zero_smul, zero_smul, zero_add] at hmn
  exact (sub_eq_zero.mp hmn).symm

end Separation

/- ## The generic finite-wall theorem -/

section Wall

variable {α : Type*} [AddCommGroup α] [Fintype α]

/-- A finite quotient current with nonzero flux supplies two white-king
invariants which, together with the residue, separate all lattice vertices.
The second invariant is exactly `H ∘ Rinv`, not a rotated stream construction. -/
theorem exists_separating_white_invariants
    (r : G →+ α) (hr : Function.Surjective r)
    (p : G) (hp : r p = 0) (hIp : r (I * p) = 0)
    (hker : ∀ u v : G, r u = r v →
      ∃ m n : ℤ, v - u = m • p + n • (I * p))
    (B : G → Prop) (hR : ∀ u, ¬ B u → ¬ B (Rinv u))
    (Cx Cy : α → ℤ) (hdiv : DivergenceFree r Cx Cy) (hw : WhiteZero r B Cx Cy)
    (hflux : (∑ a : α, Cx a) ≠ 0 ∨ (∑ a : α, Cy a) ≠ 0) :
    ∃ H K : G → ℤ, H 0 = 0 ∧ IsStream r Cx Cy H ∧ K = H ∘ Rinv ∧
      (∀ u v, ¬ B u → ¬ B v → KingAdjacent u v → H u = H v ∧ K u = K v) ∧
      (∀ u v, r u = r v → H u = H v → K u = K v → u = v) := by
  obtain ⟨H, h0, hH⟩ := exists_stream r Cx Cy hdiv
  have hperiod := hH.periods_not_both_zero hr p hp hIp hker hflux
  refine ⟨H, H ∘ Rinv, h0, hH, rfl, ?_, ?_⟩
  · intro u v hu hv huv
    exact ⟨hH.eq_of_white_king hw hu hv huv,
      hH.rotated_eq_of_white_king hw hR hu hv huv⟩
  · intro u v huv h₁ h₂
    exact hH.eq_of_residue_and_invariants p hp hIp hker hperiod huv h₁ h₂

/-- Consecutive equality of an invariant makes its value constant along a
sequence. No injectivity or finiteness assumption is involved here. -/
theorem sequence_invariant_eq {X Y : Type*} (F : X → Y) (f : ℕ → X)
    (h : ∀ n, F (f n) = F (f (n + 1))) (n : ℕ) : F (f n) = F (f 0) := by
  induction n with
  | zero => rfl
  | succ n ih => exact (h n).symm.trans ih

/-- On any white king sequence, its residue determines its vertex. In
particular the sequence can visit at most `Fintype.card α` distinct vertices. -/
theorem white_king_sequence_eq_of_residue_eq
    (r : G →+ α) (hr : Function.Surjective r)
    (p : G) (hp : r p = 0) (hIp : r (I * p) = 0)
    (hker : ∀ u v : G, r u = r v →
      ∃ m n : ℤ, v - u = m • p + n • (I * p))
    (B : G → Prop) (hR : ∀ u, ¬ B u → ¬ B (Rinv u))
    (Cx Cy : α → ℤ) (hdiv : DivergenceFree r Cx Cy) (hw : WhiteZero r B Cx Cy)
    (hflux : (∑ a : α, Cx a) ≠ 0 ∨ (∑ a : α, Cy a) ≠ 0)
    (f : ℕ → G) (hf : ∀ n, ¬ B (f n))
    (hstep : ∀ n, KingAdjacent (f n) (f (n + 1)))
    {i j : ℕ} (hij : r (f i) = r (f j)) : f i = f j := by
  obtain ⟨H, K, _, _, _, hedge, hsep⟩ :=
    exists_separating_white_invariants r hr p hp hIp hker B hR Cx Cy hdiv hw hflux
  have he (n : ℕ) := hedge (f n) (f (n + 1)) (hf n) (hf (n + 1)) (hstep n)
  have hH := sequence_invariant_eq H f (fun n => (he n).1)
  have hK := sequence_invariant_eq K f (fun n => (he n).2)
  exact hsep (f i) (f j) hij ((hH i).trans (hH j).symm) ((hK i).trans (hK j).symm)

/-- **Finite-wall obstruction.** No injective infinite white king sequence
exists under the finite quotient, current, support, and rotation hypotheses.
The nonzero-period-vector hypothesis matches the usual wall application;
the preceding stronger algebraic lemmas do not need it separately. -/
theorem not_injective_white_king_sequence
    (r : G →+ α) (hr : Function.Surjective r) (p : G) (_hp : p ≠ 0)
    (hrp : r p = 0) (hrIp : r (I * p) = 0)
    (hker : ∀ u v : G, r u = r v →
      ∃ m n : ℤ, v - u = m • p + n • (I * p))
    (B : G → Prop) (hR : ∀ u, ¬ B u → ¬ B (Rinv u))
    (Cx Cy : α → ℤ) (hdiv : DivergenceFree r Cx Cy) (hw : WhiteZero r B Cx Cy)
    (hflux : (∑ a : α, Cx a) ≠ 0 ∨ (∑ a : α, Cy a) ≠ 0)
    (f : ℕ → G) (hf : ∀ n, ¬ B (f n))
    (hstep : ∀ n, KingAdjacent (f n) (f (n + 1))) : ¬ Function.Injective f := by
  intro hinj
  obtain ⟨i, j, hne, hij⟩ := Finite.exists_ne_map_eq_of_infinite (fun n => r (f n))
  exact hne (hinj (white_king_sequence_eq_of_residue_eq
    r hr p hrp hrIp hker B hR Cx Cy hdiv hw hflux f hf hstep hij))

/-- Existential form of the generic finite-wall obstruction. -/
theorem no_injective_white_king_sequence
    (r : G →+ α) (hr : Function.Surjective r) (p : G) (hp : p ≠ 0)
    (hrp : r p = 0) (hrIp : r (I * p) = 0)
    (hker : ∀ u v : G, r u = r v →
      ∃ m n : ℤ, v - u = m • p + n • (I * p))
    (B : G → Prop) (hR : ∀ u, ¬ B u → ¬ B (Rinv u))
    (Cx Cy : α → ℤ) (hdiv : DivergenceFree r Cx Cy) (hw : WhiteZero r B Cx Cy)
    (hflux : (∑ a : α, Cx a) ≠ 0 ∨ (∑ a : α, Cy a) ≠ 0) :
    ¬ ∃ f : ℕ → G, Function.Injective f ∧ (∀ n, ¬ B (f n)) ∧
      ∀ n, KingAdjacent (f n) (f (n + 1)) := by
  rintro ⟨f, hinj, hf, hstep⟩
  exact not_injective_white_king_sequence
    r hr p hp hrp hrIp hker B hR Cx Cy hdiv hw hflux f hf hstep hinj

/-- Black preservation by the affine quarter turn is enough for the wall
obstruction: it gives inverse white preservation by contraposition. Thus
this applies in particular when blackness is preserved by both `R` and `Rinv`. -/
theorem no_injective_white_king_sequence_of_black_rotation
    (r : G →+ α) (hr : Function.Surjective r) (p : G) (hp : p ≠ 0)
    (hrp : r p = 0) (hrIp : r (I * p) = 0)
    (hker : ∀ u v : G, r u = r v →
      ∃ m n : ℤ, v - u = m • p + n • (I * p))
    (B : G → Prop) (hR : ∀ u, B u → B (R u))
    (Cx Cy : α → ℤ) (hdiv : DivergenceFree r Cx Cy) (hw : WhiteZero r B Cx Cy)
    (hflux : (∑ a : α, Cx a) ≠ 0 ∨ (∑ a : α, Cy a) ≠ 0) :
    ¬ ∃ f : ℕ → G, Function.Injective f ∧ (∀ n, ¬ B (f n)) ∧
      ∀ n, KingAdjacent (f n) (f (n + 1)) :=
  no_injective_white_king_sequence r hr p hp hrp hrIp hker B
    (fun _ hu => white_Rinv_of_black_R hR hu) Cx Cy hdiv hw hflux

end Wall

end Erdos952.WallObstruction
