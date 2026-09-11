import FormalConjectures.Util.ProblemImports

open Nat Finset
open scoped BigOperators

/--
The coefficient of $x^k$ in the expansion of $(x^2 + b x + c)^k$.
$$ T_k(b, c) = \sum_{i=0}^{\lfloor k/2 \rfloor} \binom{k}{i} \binom{k-i}{i} b^{k-2i} c^i $$
-/
def T_k (k : ℕ) (b c : ℤ) : ℚ :=
  Finset.sum (range (k / 2 + 1)) (fun i : ℕ =>
    -- The multinomial coefficient $\binom{k}{i, i, k-2i}$
    ((k.choose i * (k - i).choose i : ℕ) : ℚ) *
    -- Powers of b and c
    ((b : ℚ) ^ (k - 2 * i) * (c : ℚ) ^ i))

/--
A336981: $$a(n) = \frac{\sum_{k=0}^{n-1} (4290k + 367) \cdot 3136^{n-1-k} \cdot \binom{2k}{k} \cdot T_k(14, 1) \cdot T_k(17, 16)}{n \cdot \binom{2n-1}{n-1}}$$
where $T_k(b, c)$ denotes the coefficient of $x^k$ in the expansion of $(x^2 + b x + c)^k$.
The sequence is defined as a function $\mathbb{N} \to \mathbb{Q}$.
-/
noncomputable def a (n : ℕ) : ℚ :=
  if n = 0 then 0
  else
    let numerator_sum : ℚ :=
      Finset.sum (range n) (fun k : ℕ =>
        let T1k : ℚ := T_k k 14 1
        let T2k : ℚ := T_k k 17 16

        let k_q : ℚ := k
        -- We use casting for the exponent subtraction to ensure it stays non-negative when k <= n-1
        let n_prime : ℕ := n - 1 - k

        let term_factor : ℚ := 4290 * k_q + 367
        let power_factor : ℚ := (3136 : ℚ) ^ n_prime
        let central_binomial : ℚ := (Nat.choose (2 * k) k : ℚ)

        term_factor * power_factor * central_binomial * T1k * T2k)

    let divisor : ℚ := (n : ℚ) * (Nat.choose (2 * n - 1) (n - 1) : ℚ)

    numerator_sum / divisor

-- Definition for t(k) for the infinite sum
/--
$$t(k) = \frac{4290k+367}{3136^k} \cdot \binom{2k}{k} \cdot T_k(14, 1) \cdot T_k(17, 16)$$
-/
noncomputable def t (k : ℕ) : ℝ :=
  let T1k : ℝ := T_k k 14 1
  let T2k : ℝ := T_k k 17 16
  let k_r : ℝ := k
  let central_binomial : ℝ := (Nat.choose (2 * k) k : ℝ)

  let term_factor : ℝ := 4290 * k_r + 367
  let power_factor : ℝ := (3136 : ℝ) ^ k

  term_factor / power_factor * central_binomial * T1k * T2k


/-! ## Section P0 -/

noncomputable section
namespace Sun

/-! ### Horner-form polynomials -/

/-- Horner evaluation of a polynomial given by its coefficient list (low degree first). -/
def evalH : List ℂ → ℂ → ℂ
  | [], _ => 0
  | c :: cs, y => c + y * evalH cs y

/-- Derivative of Horner evaluation. -/
def evalH' : List ℂ → ℂ → ℂ
  | [], _ => 0
  | _ :: cs, y => evalH cs y + y * evalH' cs y

theorem evalH_hasDerivAt (cs : List ℂ) (y : ℂ) :
    HasDerivAt (fun y => evalH cs y) (evalH' cs y) y := by
  induction cs generalizing y with
  | nil => simpa [evalH, evalH'] using hasDerivAt_const y (0:ℂ)
  | cons c cs ih =>
    simp only [evalH, evalH']
    have := ((hasDerivAt_id y).mul (ih y)).const_add c
    simpa [id] using this

theorem evalH_continuous (cs : List ℂ) : Continuous (fun y => evalH cs y) := by
  induction cs with
  | nil => simp only [evalH]; fun_prop
  | cons c cs ih => simp only [evalH]; fun_prop

theorem evalH'_continuous (cs : List ℂ) : Continuous (fun y => evalH' cs y) := by
  induction cs with
  | nil => simp only [evalH']; fun_prop
  | cons c cs ih => simp only [evalH']; have := evalH_continuous cs; fun_prop

/-- bivariate: outer list indexes powers of y, inner lists are polynomials in w. -/
def evalH2 (css : List (List ℂ)) (y w : ℂ) : ℂ := evalH (css.map (fun cs => evalH cs w)) y
def evalH2_y (css : List (List ℂ)) (y w : ℂ) : ℂ := evalH' (css.map (fun cs => evalH cs w)) y
def evalH2_w (css : List (List ℂ)) (y w : ℂ) : ℂ := evalH (css.map (fun cs => evalH' cs w)) y

theorem evalH2_hasDerivAt_y (css : List (List ℂ)) (y w : ℂ) :
    HasDerivAt (fun y => evalH2 css y w) (evalH2_y css y w) y :=
  evalH_hasDerivAt _ y

theorem evalH2_hasDerivAt_w (css : List (List ℂ)) (y w : ℂ) :
    HasDerivAt (fun w => evalH2 css y w) (evalH2_w css y w) w := by
  induction css with
  | nil => simpa [evalH2, evalH2_w, evalH] using hasDerivAt_const w (0:ℂ)
  | cons cs rest ih =>
    simp only [evalH2, evalH2_w, List.map, evalH] at ih ⊢
    exact (evalH_hasDerivAt cs w).add ((ih).const_mul y)

theorem evalH2_continuous (css : List (List ℂ)) :
    Continuous (fun p : ℂ × ℂ => evalH2 css p.1 p.2) := by
  induction css with
  | nil => simp only [evalH2, List.map, evalH]; fun_prop
  | cons cs rest ih =>
    simp only [evalH2, List.map, evalH] at ih ⊢
    have := evalH_continuous cs
    fun_prop

theorem evalH2_y_continuous (css : List (List ℂ)) :
    Continuous (fun p : ℂ × ℂ => evalH2_y css p.1 p.2) := by
  induction css with
  | nil => simp only [evalH2_y, List.map, evalH']; fun_prop
  | cons cs rest ih =>
    have h2 := evalH2_continuous rest
    simp only [evalH2_y, evalH2, List.map, evalH'] at ih h2 ⊢
    have := evalH_continuous cs
    fun_prop

theorem evalH2_w_continuous (css : List (List ℂ)) :
    Continuous (fun p : ℂ × ℂ => evalH2_w css p.1 p.2) := by
  induction css with
  | nil => simp only [evalH2_w, List.map, evalH]; fun_prop
  | cons cs rest ih =>
    simp only [evalH2_w, List.map, evalH] at ih ⊢
    have := evalH'_continuous cs
    fun_prop

/-! ### The explicit polynomials -/

def BnL : List (List ℂ) := [[(0:ℂ)], [(0:ℂ), (-69300:ℂ), (-522900:ℂ), (2916900:ℂ), (-522900:ℂ), (-69300:ℂ)], [(-3889536:ℂ), (-34906424:ℂ), (199043656:ℂ), (-122477992:ℂ), (199043656:ℂ), (-34906424:ℂ), (-3889536:ℂ)], [(-457755648:ℂ), (2540755728:ℂ), (-3782286704:ℂ), (10161583152:ℂ), (-3782286704:ℂ), (2540755728:ℂ), (-457755648:ℂ)], [(-6288105600:ℂ), (34561871512:ℂ), (-2457433832:ℂ), (-25902367288:ℂ), (-2457433832:ℂ), (34561871512:ℂ), (-6288105600:ℂ)], [(-6833670144:ℂ), (-215802719748:ℂ), (2349513373340:ℂ), (-6422620273356:ℂ), (2349513373340:ℂ), (-215802719748:ℂ), (-6833670144:ℂ)], [(34382127360:ℂ), (-1576148827568:ℂ), (17036763527504:ℂ), (-56716109303056:ℂ), (17036763527504:ℂ), (-1576148827568:ℂ), (34382127360:ℂ)], [(0:ℂ)], [(-34382127360:ℂ), (1576148827568:ℂ), (-17036763527504:ℂ), (56716109303056:ℂ), (-17036763527504:ℂ), (1576148827568:ℂ), (-34382127360:ℂ)], [(6833670144:ℂ), (215802719748:ℂ), (-2349513373340:ℂ), (6422620273356:ℂ), (-2349513373340:ℂ), (215802719748:ℂ), (6833670144:ℂ)], [(6288105600:ℂ), (-34561871512:ℂ), (2457433832:ℂ), (25902367288:ℂ), (2457433832:ℂ), (-34561871512:ℂ), (6288105600:ℂ)], [(457755648:ℂ), (-2540755728:ℂ), (3782286704:ℂ), (-10161583152:ℂ), (3782286704:ℂ), (-2540755728:ℂ), (457755648:ℂ)], [(3889536:ℂ), (34906424:ℂ), (-199043656:ℂ), (122477992:ℂ), (-199043656:ℂ), (34906424:ℂ), (3889536:ℂ)], [(0:ℂ), (69300:ℂ), (522900:ℂ), (-2916900:ℂ), (522900:ℂ), (69300:ℂ)]]
def PtL : List (List ℂ) := [[(0:ℂ), (0:ℂ), (69300:ℂ), (294525:ℂ), (0:ℂ), (-294525:ℂ), (-69300:ℂ)], [(0:ℂ), (3889536:ℂ), (22492400:ℂ), (-12324508:ℂ), (0:ℂ), (12324508:ℂ), (-22492400:ℂ), (-3889536:ℂ)], [(0:ℂ), (389184768:ℂ), (-351966552:ℂ), (611175866:ℂ), (0:ℂ), (-611175866:ℂ), (351966552:ℂ), (-389184768:ℂ)], [(0:ℂ), (4609670016:ℂ), (-4938186960:ℂ), (-16992372012:ℂ), (0:ℂ), (16992372012:ℂ), (4938186960:ℂ), (-4609670016:ℂ)], [(0:ℂ), (-55190037504:ℂ), (227961000204:ℂ), (-909895465549:ℂ), (0:ℂ), (909895465549:ℂ), (-227961000204:ℂ), (55190037504:ℂ)], [(0:ℂ), (26383166208:ℂ), (-944072254496:ℂ), (-744960434232:ℂ), (0:ℂ), (744960434232:ℂ), (944072254496:ℂ), (-26383166208:ℂ)], [(0:ℂ), (47608253952:ℂ), (-6133564617936:ℂ), (63953076732972:ℂ), (0:ℂ), (-63953076732972:ℂ), (6133564617936:ℂ), (-47608253952:ℂ)], [(0:ℂ), (26383166208:ℂ), (-944072254496:ℂ), (-744960434232:ℂ), (0:ℂ), (744960434232:ℂ), (944072254496:ℂ), (-26383166208:ℂ)], [(0:ℂ), (-55190037504:ℂ), (227961000204:ℂ), (-909895465549:ℂ), (0:ℂ), (909895465549:ℂ), (-227961000204:ℂ), (55190037504:ℂ)], [(0:ℂ), (4609670016:ℂ), (-4938186960:ℂ), (-16992372012:ℂ), (0:ℂ), (16992372012:ℂ), (4938186960:ℂ), (-4609670016:ℂ)], [(0:ℂ), (389184768:ℂ), (-351966552:ℂ), (611175866:ℂ), (0:ℂ), (-611175866:ℂ), (351966552:ℂ), (-389184768:ℂ)], [(0:ℂ), (3889536:ℂ), (22492400:ℂ), (-12324508:ℂ), (0:ℂ), (12324508:ℂ), (-22492400:ℂ), (-3889536:ℂ)], [(0:ℂ), (0:ℂ), (69300:ℂ), (294525:ℂ), (0:ℂ), (-294525:ℂ), (-69300:ℂ)]]
def DmL : List (List ℂ) := [[(0:ℂ), (0:ℂ), (225:ℂ), (-450:ℂ), (225:ℂ)], [(0:ℂ), (14896:ℂ), (-34540:ℂ), (35688:ℂ), (-34540:ℂ), (14896:ℂ)], [(196608:ℂ), (-558560:ℂ), (1027010:ℂ), (-1738020:ℂ), (1027010:ℂ), (-558560:ℂ), (196608:ℂ)], [(2359296:ℂ), (-7390608:ℂ), (-1134140:ℂ), (-1290552:ℂ), (-1134140:ℂ), (-7390608:ℂ), (2359296:ℂ)], [(-5505024:ℂ), (54770048:ℂ), (-626497521:ℂ), (1112411234:ℂ), (-626497521:ℂ), (54770048:ℂ), (-5505024:ℂ)], [(-2359296:ℂ), (258653024:ℂ), (-4948463320:ℂ), (13758627280:ℂ), (-4948463320:ℂ), (258653024:ℂ), (-2359296:ℂ)], [(10616832:ℂ), (-610977600:ℂ), (1486528156:ℂ), (47573320968:ℂ), (1486528156:ℂ), (-610977600:ℂ), (10616832:ℂ)], [(-2359296:ℂ), (258653024:ℂ), (-4948463320:ℂ), (13758627280:ℂ), (-4948463320:ℂ), (258653024:ℂ), (-2359296:ℂ)], [(-5505024:ℂ), (54770048:ℂ), (-626497521:ℂ), (1112411234:ℂ), (-626497521:ℂ), (54770048:ℂ), (-5505024:ℂ)], [(2359296:ℂ), (-7390608:ℂ), (-1134140:ℂ), (-1290552:ℂ), (-1134140:ℂ), (-7390608:ℂ), (2359296:ℂ)], [(196608:ℂ), (-558560:ℂ), (1027010:ℂ), (-1738020:ℂ), (1027010:ℂ), (-558560:ℂ), (196608:ℂ)], [(0:ℂ), (14896:ℂ), (-34540:ℂ), (35688:ℂ), (-34540:ℂ), (14896:ℂ)], [(0:ℂ), (0:ℂ), (225:ℂ), (-450:ℂ), (225:ℂ)]]
def ML : List (List ℂ) := [[(0:ℂ)], [(0:ℂ), (-4:ℂ), (-17:ℂ), (-4:ℂ)], [(0:ℂ), (-56:ℂ), (546:ℂ), (-56:ℂ)], [(0:ℂ), (-4:ℂ), (-17:ℂ), (-4:ℂ)]]

def Bn (y w : ℂ) : ℂ := evalH2 BnL y w
def Pt (y w : ℂ) : ℂ := evalH2 PtL y w
def Dm (y w : ℂ) : ℂ := evalH2 DmL y w
def Mp (y w : ℂ) : ℂ := evalH2 ML y w

/-- The factors of `Dm`. -/
def D0a (y w : ℂ) : ℂ := y^2 + 48*y*w - 2*y + 1
def D0b (y w : ℂ) : ℂ := y^2*w - 2*y*w + 48*y + w
def D1 (y w : ℂ) : ℂ := (y-1)^2*(w^2+1) - 2*(y^2+6*y+1)*w
def D2 (y w : ℂ) : ℂ := 4096*y*(y^4+16*y^3+30*y^2+16*y+1)*(w^2+1)
  + (225*y^6-3398*y^5-197329*y^4-1696148*y^3-197329*y^2-3398*y+225)*w

set_option maxRecDepth 8000 in
set_option maxHeartbeats 1000000 in
theorem Dm_factor (y w : ℂ) : Dm y w = D0a y w * D0b y w * D1 y w * D2 y w := by
  simp only [Dm, D0a, D0b, D1, D2, evalH2, DmL, List.map, evalH]
  ring

theorem Mp_eq (y w : ℂ) : Mp y w = 784*y^2*w^2 - y*w*(y^2+14*y+1)*(4*w^2+17*w+4) := by
  simp only [Mp, evalH2, ML, List.map, evalH]
  ring

theorem Mp_y_eq (y w : ℂ) : evalH2_y ML y w =
    1568*y*w^2 - w*(y^2+14*y+1)*(4*w^2+17*w+4) - y*w*(2*y+14)*(4*w^2+17*w+4) := by
  simp only [evalH2_y, ML, List.map, evalH, evalH']
  ring

theorem Mp_w_eq (y w : ℂ) : evalH2_w ML y w =
    1568*y^2*w - y*(y^2+14*y+1)*(4*w^2+17*w+4) - y*w*(y^2+14*y+1)*(8*w+17) := by
  simp only [evalH2_w, ML, List.map, evalH, evalH']
  ring

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem key_identity (y w Z : ℂ) (hZ : Z^2 = Mp y w) :
    ((evalH2_y BnL y w * Dm y w - Bn y w * evalH2_y DmL y w) * Z^2
        - Bn y w * Dm y w * evalH2_y ML y w / 2)
      - ((evalH2_w PtL y w * Dm y w - Pt y w * evalH2_w DmL y w) * Z^2
        - Pt y w * Dm y w * evalH2_w ML y w / 2)
      = (-1778 * Z^2 + 1681680 * y^2 * w^2) * Dm y w ^ 2 := by
  linear_combination (norm := skip) ((evalH2_y BnL y w * Dm y w - Bn y w * evalH2_y DmL y w)
      - (evalH2_w PtL y w * Dm y w - Pt y w * evalH2_w DmL y w) + 1778 * Dm y w ^ 2) * hZ
  simp only [Bn, Pt, Dm, Mp, evalH2, evalH2_y, evalH2_w, BnL, PtL, DmL, ML, List.map, evalH, evalH']
  ring1

end Sun

end

/-! ## Section P1 -/

noncomputable section
namespace Sun
open Complex

def Phi2 (y : ℂ) : ℂ := y + 14 + y⁻¹
def Phi3 (w : ℂ) : ℂ := 4 * w + 17 + 4 * w⁻¹
def PQ (y w : ℂ) : ℂ := Phi2 y * Phi3 w / 784
def S (y w : ℂ) : ℂ := (1 - PQ y w) ^ (1/2 : ℂ)
def Z (y w : ℂ) : ℂ := 28 * y * w * S y w
def G (y w : ℂ) : ℂ := -1778 / Z y w + 1681680 * (y*w)^2 / (Z y w)^3
def Bhat (y w : ℂ) : ℂ := Bn y w / (Dm y w * Z y w)
def Af (y w : ℂ) : ℂ := Pt y w / (Dm y w * Z y w)
def PQ_y (y w : ℂ) : ℂ := (1 - (y^2)⁻¹) * Phi3 w / 784
def PQ_w (y w : ℂ) : ℂ := Phi2 y * (4 - 4 * (w^2)⁻¹) / 784
def S_y (y w : ℂ) : ℂ := -(PQ_y y w) / (2 * S y w)
def S_w (y w : ℂ) : ℂ := -(PQ_w y w) / (2 * S y w)
def Z_y (y w : ℂ) : ℂ := 28 * w * S y w + 28 * y * w * S_y y w
def Z_w (y w : ℂ) : ℂ := 28 * y * S y w + 28 * y * w * S_w y w
def By (y w : ℂ) : ℂ := (evalH2_y BnL y w * (Dm y w * Z y w)
  - Bn y w * (evalH2_y DmL y w * Z y w + Dm y w * Z_y y w)) / (Dm y w * Z y w)^2
def Aw (y w : ℂ) : ℂ := (evalH2_w PtL y w * (Dm y w * Z y w)
  - Pt y w * (evalH2_w DmL y w * Z y w + Dm y w * Z_w y w)) / (Dm y w * Z y w)^2

set_option linter.unnecessarySimpa false in
theorem S_sq (y w : ℂ) : S y w ^ 2 = 1 - PQ y w := by
  have := Complex.cpow_nat_inv_pow (1 - PQ y w) (n := 2) two_ne_zero
  simpa [S, one_div] using this

theorem S_ne_zero {y w : ℂ} (h : 1 - PQ y w ≠ 0) : S y w ≠ 0 := by
  intro h0
  have := S_sq y w
  rw [h0] at this
  exact h (by simpa using this.symm)

theorem Z_sq {y w : ℂ} (hy : y ≠ 0) (hw : w ≠ 0) : Z y w ^ 2 = Mp y w := by
  unfold Z
  rw [mul_pow, S_sq, Mp_eq]
  unfold PQ Phi2 Phi3
  field_simp
  ring

theorem Z_ne_zero {y w : ℂ} (hy : y ≠ 0) (hw : w ≠ 0) (h : 1 - PQ y w ≠ 0) : Z y w ≠ 0 := by
  unfold Z
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) hy) hw) (S_ne_zero h)

theorem hasDerivAt_PQ_y {y : ℂ} (w : ℂ) (hy : y ≠ 0) :
    HasDerivAt (fun y => PQ y w) (PQ_y y w) y := by
  have h := ((((hasDerivAt_id y).add_const (14:ℂ)).add (hasDerivAt_inv hy)).mul_const
    (Phi3 w)).div_const (784:ℂ)
  exact h.congr_deriv (by simp only [PQ_y]; ring)

theorem hasDerivAt_PQ_w (y : ℂ) {w : ℂ} (hw : w ≠ 0) :
    HasDerivAt (fun w => PQ y w) (PQ_w y w) w := by
  have h := (((((hasDerivAt_id w).const_mul (4:ℂ)).add_const (17:ℂ)).add
    ((hasDerivAt_inv hw).const_mul 4)).const_mul (Phi2 y)).div_const (784:ℂ)
  exact h.congr_deriv (by simp only [PQ_w]; ring)

theorem cpow_half_sub_one (x : ℂ) : x ^ ((1/2 : ℂ) - 1) = (x ^ (1/2 : ℂ))⁻¹ := by
  rw [show (1/2 : ℂ) - 1 = -(1/2) by norm_num, Complex.cpow_neg]

theorem hasDerivAt_S_y {y : ℂ} (w : ℂ) (hy : y ≠ 0) (hs : 1 - PQ y w ∈ slitPlane) :
    HasDerivAt (fun y => S y w) (S_y y w) y := by
  have h := ((hasDerivAt_PQ_y w hy).const_sub 1).cpow_const (c := (1/2 : ℂ)) hs
  refine h.congr_deriv ?_
  rw [cpow_half_sub_one]
  simp only [S_y, S]
  ring

theorem hasDerivAt_S_w (y : ℂ) {w : ℂ} (hw : w ≠ 0) (hs : 1 - PQ y w ∈ slitPlane) :
    HasDerivAt (fun w => S y w) (S_w y w) w := by
  have h := ((hasDerivAt_PQ_w y hw).const_sub 1).cpow_const (c := (1/2 : ℂ)) hs
  refine h.congr_deriv ?_
  rw [cpow_half_sub_one]
  simp only [S_w, S]
  ring

theorem hasDerivAt_Z_y {y : ℂ} (w : ℂ) (hy : y ≠ 0) (hs : 1 - PQ y w ∈ slitPlane) :
    HasDerivAt (fun y => Z y w) (Z_y y w) y := by
  have h := (((hasDerivAt_id y).const_mul (28:ℂ)).mul_const w).mul (hasDerivAt_S_y w hy hs)
  exact h.congr_deriv (by simp only [Z_y, id]; ring)

theorem hasDerivAt_Z_w (y : ℂ) {w : ℂ} (hw : w ≠ 0) (hs : 1 - PQ y w ∈ slitPlane) :
    HasDerivAt (fun w => Z y w) (Z_w y w) w := by
  have h := ((hasDerivAt_id w).const_mul (28 * y)).mul (hasDerivAt_S_w y hw hs)
  have e : (fun w => Z y w) = (fun w => 28 * y * id w) * (fun w => S y w) := by
    funext w; simp [Z]
  rw [e]
  exact h.congr_deriv (by simp only [Z_w, id]; ring)

theorem Z_mul_Z_y {y w : ℂ} (hy : y ≠ 0) (hw : w ≠ 0) (h : 1 - PQ y w ≠ 0) :
    Z y w * Z_y y w = evalH2_y ML y w / 2 := by
  have hS := S_sq y w
  have hS0 := S_ne_zero h
  have e : Z y w * Z_y y w = 784*y*w^2*S y w^2 - 392*y^2*w^2*PQ_y y w := by
    unfold Z Z_y S_y
    field_simp
    ring
  rw [e, hS, Mp_y_eq]
  unfold PQ PQ_y Phi2 Phi3
  field_simp
  ring

theorem Z_mul_Z_w {y w : ℂ} (hy : y ≠ 0) (hw : w ≠ 0) (h : 1 - PQ y w ≠ 0) :
    Z y w * Z_w y w = evalH2_w ML y w / 2 := by
  have hS := S_sq y w
  have hS0 := S_ne_zero h
  have e : Z y w * Z_w y w = 784*y^2*w*S y w^2 - 392*y^2*w^2*PQ_w y w := by
    unfold Z Z_w S_w
    field_simp
    ring
  rw [e, hS, Mp_w_eq]
  unfold PQ PQ_w Phi2 Phi3
  field_simp
  ring

theorem hasDerivAt_Bhat_y {y w : ℂ} (hy : y ≠ 0) (hw : w ≠ 0) (hs : 1 - PQ y w ∈ slitPlane)
    (hD : Dm y w ≠ 0) : HasDerivAt (fun y => Bhat y w) (By y w) y := by
  have hZ := Z_ne_zero hy hw (slitPlane_ne_zero hs)
  exact (evalH2_hasDerivAt_y BnL y w).div
    ((evalH2_hasDerivAt_y DmL y w).mul (hasDerivAt_Z_y w hy hs)) (mul_ne_zero hD hZ)

theorem hasDerivAt_Af_w {y w : ℂ} (hy : y ≠ 0) (hw : w ≠ 0) (hs : 1 - PQ y w ∈ slitPlane)
    (hD : Dm y w ≠ 0) : HasDerivAt (fun w => Af y w) (Aw y w) w := by
  have hZ := Z_ne_zero hy hw (slitPlane_ne_zero hs)
  exact (evalH2_hasDerivAt_w PtL y w).div
    ((evalH2_hasDerivAt_w DmL y w).mul (hasDerivAt_Z_w y hw hs)) (mul_ne_zero hD hZ)

theorem By_eq {y w : ℂ} (hy : y ≠ 0) (hw : w ≠ 0) (h : 1 - PQ y w ≠ 0) (hD : Dm y w ≠ 0) :
    By y w = ((evalH2_y BnL y w * Dm y w - Bn y w * evalH2_y DmL y w) * Z y w ^ 2
        - Bn y w * Dm y w * evalH2_y ML y w / 2) / (Dm y w ^ 2 * Z y w ^ 3) := by
  have hZ := Z_ne_zero hy hw h
  have hZZ := Z_mul_Z_y hy hw h
  unfold By
  rw [div_eq_div_iff (pow_ne_zero _ (mul_ne_zero hD hZ)) (mul_ne_zero (pow_ne_zero _ hD) (pow_ne_zero _ hZ))]
  linear_combination (-(Bn y w) * Dm y w ^ 3 * Z y w ^ 2) * hZZ

theorem Aw_eq {y w : ℂ} (hy : y ≠ 0) (hw : w ≠ 0) (h : 1 - PQ y w ≠ 0) (hD : Dm y w ≠ 0) :
    Aw y w = ((evalH2_w PtL y w * Dm y w - Pt y w * evalH2_w DmL y w) * Z y w ^ 2
        - Pt y w * Dm y w * evalH2_w ML y w / 2) / (Dm y w ^ 2 * Z y w ^ 3) := by
  have hZ := Z_ne_zero hy hw h
  have hZZ := Z_mul_Z_w hy hw h
  unfold Aw
  rw [div_eq_div_iff (pow_ne_zero _ (mul_ne_zero hD hZ)) (mul_ne_zero (pow_ne_zero _ hD) (pow_ne_zero _ hZ))]
  linear_combination (-(Pt y w) * Dm y w ^ 3 * Z y w ^ 2) * hZZ

theorem stokes_identity {y w : ℂ} (hy : y ≠ 0) (hw : w ≠ 0) (h : 1 - PQ y w ≠ 0)
    (hD : Dm y w ≠ 0) : By y w - Aw y w = G y w := by
  have hZ := Z_ne_zero hy hw h
  rw [By_eq hy hw h hD, Aw_eq hy hw h hD, div_sub_div_same, key_identity y w (Z y w) (Z_sq hy hw)]
  unfold G
  field_simp

end Sun

end

/-! ## Section P2 -/

noncomputable section
namespace Sun
open Complex

/-! ### Expressions in terms of `c` where `y + y⁻¹ = 2c` -/

def qpoly (c : ℂ) : ℂ := -1800*c^3 + 13592*c^2 + 396008*c + 1689352

theorem c_eq {y c : ℂ} (hyc : y + y⁻¹ = 2 * c) : c = (y + y⁻¹) / 2 := by
  rw [hyc]; ring

theorem Phi2_eq {y c : ℂ} (hyc : y + y⁻¹ = 2 * c) : Phi2 y = 14 + 2 * c := by
  unfold Phi2; linear_combination hyc

theorem D0a_eq {y c : ℂ} (hy0 : y ≠ 0) (hyc : y + y⁻¹ = 2 * c) (w : ℂ) :
    D0a y w = y * (2*c - 2 + 48*w) := by
  rw [c_eq hyc]; unfold D0a; field_simp; ring

theorem D0b_eq {y c : ℂ} (hy0 : y ≠ 0) (hyc : y + y⁻¹ = 2 * c) (w : ℂ) :
    D0b y w = y * (w*(2*c - 2) + 48) := by
  rw [c_eq hyc]; unfold D0b; field_simp; ring

theorem D1_eq {y c : ℂ} (hy0 : y ≠ 0) (hyc : y + y⁻¹ = 2 * c) (w : ℂ) :
    D1 y w = y * ((2*c - 2)*(w^2+1) - (4*c + 12)*w) := by
  rw [c_eq hyc]; unfold D1; field_simp; ring

theorem D2_eq {y c : ℂ} (hy0 : y ≠ 0) (hyc : y + y⁻¹ = 2 * c) (w : ℂ) :
    D2 y w = y^3 * (16384*(c+1)*(c+7)*(w^2+1) - qpoly c * w) := by
  rw [c_eq hyc]; unfold D2 qpoly; field_simp; ring

/-! ### Nonvanishing -/

theorem D0a_ne_zero {y w : ℂ} {c : ℝ} (hy0 : y ≠ 0) (hyc : y + y⁻¹ = 2 * (c:ℂ))
    (hc1 : -1 ≤ c) (hc2 : c ≤ 1) (hw : 1/6 ≤ ‖w‖) : D0a y w ≠ 0 := by
  rw [D0a_eq hy0 hyc]
  refine mul_ne_zero hy0 ?_
  intro h
  have h1 : (48:ℂ) * w = ((2 - 2*c : ℝ) : ℂ) := by push_cast; linear_combination h
  have h2 : ‖(48:ℂ) * w‖ = |2 - 2*c| := by rw [h1, Complex.norm_real, Real.norm_eq_abs]
  rw [norm_mul, Complex.norm_ofNat] at h2
  have h3 : |2 - 2*c| ≤ 4 := by rw [abs_le]; constructor <;> linarith
  linarith

theorem D0b_ne_zero {y w : ℂ} {c : ℝ} (hy0 : y ≠ 0) (hyc : y + y⁻¹ = 2 * (c:ℂ))
    (hc1 : -1 ≤ c) (hc2 : c ≤ 1) (hw : ‖w‖ ≤ 1) : D0b y w ≠ 0 := by
  rw [D0b_eq hy0 hyc]
  refine mul_ne_zero hy0 ?_
  intro h
  have h1 : w * ((2*c - 2 : ℝ) : ℂ) = -48 := by push_cast; linear_combination h
  have h2 : ‖w * ((2*c - 2 : ℝ) : ℂ)‖ = 48 := by rw [h1]; simp
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs] at h2
  have h3 : |2*c - 2| ≤ 4 := by rw [abs_le]; constructor <;> linarith
  have h4 : ‖w‖ * |2*c - 2| ≤ 1 * 4 :=
    mul_le_mul hw h3 (abs_nonneg _) zero_le_one
  linarith

theorem D1_ne_zero_half {y w : ℂ} {c : ℝ} (hy0 : y ≠ 0) (hyc : y + y⁻¹ = 2 * (c:ℂ))
    (hc2 : c ≤ 1) (hc : -7/9 < c) (hw : ‖w‖ = 1/2) : D1 y w ≠ 0 := by
  rw [D1_eq hy0 hyc]
  refine mul_ne_zero hy0 ?_
  intro h
  have h1 : ((2*c - 2 : ℝ) : ℂ) * (w^2+1) = ((4*c + 12 : ℝ) : ℂ) * w := by
    push_cast; linear_combination h
  have h2 := congrArg (‖·‖) h1
  simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, hw] at h2
  have h3 : ‖w^2 + 1‖ ≤ 5/4 := by
    calc ‖w^2 + 1‖ ≤ ‖w^2‖ + ‖(1:ℂ)‖ := norm_add_le _ _
      _ = 5/4 := by rw [norm_pow, hw]; norm_num
  have h4 : |2*c - 2| = 2 - 2*c := by rw [abs_of_nonpos (by linarith)]; ring
  have h5 : |4*c + 12| = 4*c + 12 := abs_of_nonneg (by linarith)
  rw [h4, h5] at h2
  nlinarith [norm_nonneg (w^2+1)]

theorem D1_ne_zero_sixth {y w : ℂ} {c : ℝ} (hy0 : y ≠ 0) (hyc : y + y⁻¹ = 2 * (c:ℂ))
    (hc1 : -1 ≤ c) (hc : c < -1/47) (hw : ‖w‖ = 1/6) : D1 y w ≠ 0 := by
  rw [D1_eq hy0 hyc]
  refine mul_ne_zero hy0 ?_
  intro h
  have h1 : ((2*c - 2 : ℝ) : ℂ) * (w^2+1) = ((4*c + 12 : ℝ) : ℂ) * w := by
    push_cast; linear_combination h
  have h2 := congrArg (‖·‖) h1
  simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, hw] at h2
  have h3 : 35/36 ≤ ‖w^2 + 1‖ := by
    have := norm_sub_norm_le (1:ℂ) (-(w^2))
    have e : ‖(1:ℂ) - -(w^2)‖ = ‖w^2 + 1‖ := by congr 1; ring
    rw [e, norm_neg, norm_pow, hw, norm_one] at this
    norm_num at this ⊢; linarith
  have h4 : |2*c - 2| = 2 - 2*c := by rw [abs_of_nonpos (by linarith)]; ring
  have h5 : |4*c + 12| = 4*c + 12 := abs_of_nonneg (by linarith)
  rw [h4, h5] at h2
  have h6 : (2 - 2*c) * (35/36) ≤ (2 - 2*c) * ‖w^2+1‖ :=
    mul_le_mul_of_nonneg_left h3 (by linarith)
  nlinarith [norm_nonneg (w^2+1)]

theorem qpoly_bound {c : ℝ} (hc1 : -1 ≤ c) (hc2 : c ≤ 1) :
    131072*(c+1)*(c+7) ≤ -1800*c^3 + 13592*c^2 + 396008*c + 1689352 := by
  have : 0 ≤ (1 - c) * (1800*c^2 + 119280*c + 771848) := by
    apply mul_nonneg (by linarith)
    nlinarith
  nlinarith

theorem qpoly_pos {c : ℝ} (hc1 : -1 ≤ c) (hc2 : c ≤ 1) :
    0 < -1800*c^3 + 13592*c^2 + 396008*c + 1689352 := by
  nlinarith [sq_nonneg c, sq_nonneg (c+1), sq_nonneg (c-1)]

theorem D2_ne_zero {y w : ℂ} {c : ℝ} (hy0 : y ≠ 0) (hyc : y + y⁻¹ = 2 * (c:ℂ))
    (hc1 : -1 ≤ c) (hc2 : c ≤ 1) (hw1 : 1/6 ≤ ‖w‖) (hw2 : ‖w‖ ≤ 1) : D2 y w ≠ 0 := by
  rw [D2_eq hy0 hyc]
  refine mul_ne_zero (pow_ne_zero _ hy0) ?_
  intro h
  have h1 : ((16384*(c+1)*(c+7) : ℝ) : ℂ) * (w^2+1) =
      ((-1800*c^3 + 13592*c^2 + 396008*c + 1689352 : ℝ) : ℂ) * w := by
    unfold qpoly at h; push_cast; linear_combination h
  have h2 := congrArg (‖·‖) h1
  simp only at h2
  rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
    Real.norm_eq_abs] at h2
  have hP : 0 ≤ 16384*(c+1)*(c+7) := by
    have : 0 ≤ (c+1)*(c+7) := mul_nonneg (by linarith) (by linarith)
    nlinarith
  have hq := qpoly_pos hc1 hc2
  rw [abs_of_nonneg hP, abs_of_pos hq] at h2
  have h3 : ‖w^2 + 1‖ ≤ ‖w‖^2 + 1 := by
    calc ‖w^2 + 1‖ ≤ ‖w^2‖ + ‖(1:ℂ)‖ := norm_add_le _ _
      _ = ‖w‖^2 + 1 := by rw [norm_pow, norm_one]
  have hqb := qpoly_bound hc1 hc2
  set r := ‖w‖ with hr
  set P := 16384*(c+1)*(c+7) with hPdef
  set q := -1800*c^3 + 13592*c^2 + 396008*c + 1689352 with hqdef
  -- h2 : P * ‖w^2+1‖ = q * r
  have h4 : q * r ≤ P * (r^2 + 1) := by
    rw [← h2]; exact mul_le_mul_of_nonneg_left h3 hP
  have h5 : 8 * P * r ≤ P * (r^2 + 1) := by nlinarith
  have h6 : P * (8*r - r^2 - 1) ≤ 0 := by nlinarith
  have h7 : 0 < 8*r - r^2 - 1 := by nlinarith
  have h8 : P ≤ 0 := by nlinarith
  have h9 : P = 0 := le_antisymm h8 hP
  rw [h9] at h4
  nlinarith

theorem Dm_ne_zero_half {y w : ℂ} {c : ℝ} (hy0 : y ≠ 0) (hyc : y + y⁻¹ = 2 * (c:ℂ))
    (hc1 : -1 ≤ c) (hc2 : c ≤ 1) (hc : -7/9 < c) (hw : ‖w‖ = 1/2) : Dm y w ≠ 0 := by
  rw [Dm_factor]
  have hw1 : 1/6 ≤ ‖w‖ := by rw [hw]; norm_num
  have hw2 : ‖w‖ ≤ 1 := by rw [hw]; norm_num
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero (D0a_ne_zero hy0 hyc hc1 hc2 hw1)
    (D0b_ne_zero hy0 hyc hc1 hc2 hw2)) (D1_ne_zero_half hy0 hyc hc2 hc hw))
    (D2_ne_zero hy0 hyc hc1 hc2 hw1 hw2)

theorem Dm_ne_zero_sixth {y w : ℂ} {c : ℝ} (hy0 : y ≠ 0) (hyc : y + y⁻¹ = 2 * (c:ℂ))
    (hc1 : -1 ≤ c) (hc2 : c ≤ 1) (hc : c < -1/47) (hw : ‖w‖ = 1/6) : Dm y w ≠ 0 := by
  rw [Dm_factor]
  have hw1 : 1/6 ≤ ‖w‖ := by rw [hw]
  have hw2 : ‖w‖ ≤ 1 := by rw [hw]; norm_num
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero (D0a_ne_zero hy0 hyc hc1 hc2 hw1)
    (D0b_ne_zero hy0 hyc hc1 hc2 hw2)) (D1_ne_zero_sixth hy0 hyc hc1 hc hw))
    (D2_ne_zero hy0 hyc hc1 hc2 hw1 hw2)

/-! ### Positivity of `Re (1 - PQ)` -/

theorem re_one_sub_PQ_pos {y w : ℂ} {c : ℝ} (hyc : y + y⁻¹ = 2 * (c:ℂ))
    (hc1 : -1 ≤ c) (hc2 : c ≤ 1) (hw1 : 1/6 ≤ ‖w‖) (hw2 : ‖w‖ ≤ 1) :
    0 < (1 - PQ y w).re := by
  have hPhi2 : Phi2 y = ((14 + 2*c : ℝ) : ℂ) := by rw [Phi2_eq hyc]; push_cast; ring
  have hre : (PQ y w).re = (14 + 2*c) * (Phi3 w).re / 784 := by
    unfold PQ; rw [hPhi2, Complex.div_ofNat_re, Complex.re_ofReal_mul]
  have h3 : (Phi3 w).re = 4 * w.re + 17 + 4 * (w⁻¹).re := by
    simp [Phi3, Complex.add_re, Complex.mul_re]
  have hw0 : 0 < ‖w‖ := by linarith
  have hre1 : w.re ≤ 1 := (Complex.re_le_norm w).trans hw2
  have hre2 : (w⁻¹).re ≤ 6 := by
    refine (Complex.re_le_norm _).trans ?_
    rw [norm_inv]
    exact inv_le_of_inv_le₀ (by norm_num) (by rw [← one_div]; exact hw1)
  have hΦ : (Phi3 w).re ≤ 45 := by rw [h3]; linarith
  rw [Complex.sub_re, Complex.one_re, hre]
  rcases le_or_gt 0 (Phi3 w).re with h | h
  · nlinarith
  · nlinarith

theorem one_sub_PQ_mem_slitPlane {y w : ℂ} {c : ℝ} (hyc : y + y⁻¹ = 2 * (c:ℂ))
    (hc1 : -1 ≤ c) (hc2 : c ≤ 1) (hw1 : 1/6 ≤ ‖w‖) (hw2 : ‖w‖ ≤ 1) :
    1 - PQ y w ∈ slitPlane :=
  mem_slitPlane_iff.2 (Or.inl (re_one_sub_PQ_pos hyc hc1 hc2 hw1 hw2))

/-! ### The unit circle parametrisation -/

def yc (β : ℝ) : ℂ := Complex.exp (β * I)

theorem yc_ne_zero (β : ℝ) : yc β ≠ 0 := Complex.exp_ne_zero _

theorem yc_inv (β : ℝ) : (yc β)⁻¹ = Complex.exp (-(β * I)) := by
  rw [yc, ← Complex.exp_neg]

theorem yc_add_inv (β : ℝ) : yc β + (yc β)⁻¹ = 2 * ((Real.cos β : ℝ) : ℂ) := by
  rw [yc_inv, yc, Complex.exp_mul_I, ← neg_mul, Complex.exp_mul_I, Complex.cos_neg,
    Complex.sin_neg, Complex.ofReal_cos]
  ring

theorem norm_yc (β : ℝ) : ‖yc β‖ = 1 := by
  rw [yc, Complex.norm_exp_ofReal_mul_I]

theorem hasDerivAt_yc (β : ℝ) : HasDerivAt yc (yc β * I) β := by
  have h : HasDerivAt (fun x : ℂ => Complex.exp (x * I)) (Complex.exp (β * I) * I) β := by
    have := (Complex.hasDerivAt_exp (β * I)).comp (β : ℂ) ((hasDerivAt_id (β:ℂ)).mul_const I)
    simpa using this
  exact h.comp_ofReal

theorem continuous_yc : Continuous yc := by
  unfold yc; fun_prop

theorem yc_periodic (β : ℝ) : yc (β + 2 * Real.pi) = yc β := by
  unfold yc
  push_cast
  rw [add_mul, Complex.exp_add, Complex.exp_two_pi_mul_I, mul_one]

end Sun

end

/-! ## Section P3 -/

noncomputable section
namespace Sun
open Complex Set Metric

/-! ### Continuity of the basic functions (as functions of the pair `(y, w)`) -/

theorem continuousAt_PQ {p : ℂ × ℂ} (h1 : p.1 ≠ 0) (h2 : p.2 ≠ 0) :
    ContinuousAt (fun p : ℂ × ℂ => PQ p.1 p.2) p := by
  unfold PQ Phi2 Phi3
  fun_prop (disch := assumption)

theorem continuousAt_S {p : ℂ × ℂ} (h1 : p.1 ≠ 0) (h2 : p.2 ≠ 0)
    (hs : 1 - PQ p.1 p.2 ∈ slitPlane) :
    ContinuousAt (fun p : ℂ × ℂ => S p.1 p.2) p := by
  unfold S
  exact (continuousAt_const.sub (continuousAt_PQ h1 h2)).cpow continuousAt_const hs

theorem continuousAt_Z {p : ℂ × ℂ} (h1 : p.1 ≠ 0) (h2 : p.2 ≠ 0)
    (hs : 1 - PQ p.1 p.2 ∈ slitPlane) :
    ContinuousAt (fun p : ℂ × ℂ => Z p.1 p.2) p := by
  have := continuousAt_S h1 h2 hs
  unfold Z
  fun_prop

theorem continuousAt_G {p : ℂ × ℂ} (h1 : p.1 ≠ 0) (h2 : p.2 ≠ 0)
    (hs : 1 - PQ p.1 p.2 ∈ slitPlane) :
    ContinuousAt (fun p : ℂ × ℂ => G p.1 p.2) p := by
  have hZ := continuousAt_Z h1 h2 hs
  have hZ0 : Z p.1 p.2 ≠ 0 := Z_ne_zero h1 h2 (slitPlane_ne_zero hs)
  have hZ3 : Z p.1 p.2 ^ 3 ≠ 0 := pow_ne_zero _ hZ0
  unfold G
  fun_prop (disch := assumption)

theorem continuousAt_Bhat {p : ℂ × ℂ} (h1 : p.1 ≠ 0) (h2 : p.2 ≠ 0)
    (hs : 1 - PQ p.1 p.2 ∈ slitPlane) (hD : Dm p.1 p.2 ≠ 0) :
    ContinuousAt (fun p : ℂ × ℂ => Bhat p.1 p.2) p := by
  have hZ := continuousAt_Z h1 h2 hs
  have hZ0 : Z p.1 p.2 ≠ 0 := Z_ne_zero h1 h2 (slitPlane_ne_zero hs)
  have hDZ : Dm p.1 p.2 * Z p.1 p.2 ≠ 0 := mul_ne_zero hD hZ0
  have hB : Continuous (fun p : ℂ × ℂ => Bn p.1 p.2) := evalH2_continuous BnL
  have hDc : Continuous (fun p : ℂ × ℂ => Dm p.1 p.2) := evalH2_continuous DmL
  unfold Bhat
  fun_prop (disch := assumption)

theorem continuousAt_Af {p : ℂ × ℂ} (h1 : p.1 ≠ 0) (h2 : p.2 ≠ 0)
    (hs : 1 - PQ p.1 p.2 ∈ slitPlane) (hD : Dm p.1 p.2 ≠ 0) :
    ContinuousAt (fun p : ℂ × ℂ => Af p.1 p.2) p := by
  have hZ := continuousAt_Z h1 h2 hs
  have hZ0 : Z p.1 p.2 ≠ 0 := Z_ne_zero h1 h2 (slitPlane_ne_zero hs)
  have hDZ : Dm p.1 p.2 * Z p.1 p.2 ≠ 0 := mul_ne_zero hD hZ0
  have hB : Continuous (fun p : ℂ × ℂ => Pt p.1 p.2) := evalH2_continuous PtL
  have hDc : Continuous (fun p : ℂ × ℂ => Dm p.1 p.2) := evalH2_continuous DmL
  unfold Af
  fun_prop (disch := assumption)

theorem continuousAt_By {p : ℂ × ℂ} (h1 : p.1 ≠ 0) (h2 : p.2 ≠ 0)
    (hs : 1 - PQ p.1 p.2 ∈ slitPlane) (hD : Dm p.1 p.2 ≠ 0) :
    ContinuousAt (fun p : ℂ × ℂ => By p.1 p.2) p := by
  have hS := continuousAt_S h1 h2 hs
  have hZ := continuousAt_Z h1 h2 hs
  have hZ0 : Z p.1 p.2 ≠ 0 := Z_ne_zero h1 h2 (slitPlane_ne_zero hs)
  have hS0 : S p.1 p.2 ≠ 0 := S_ne_zero (slitPlane_ne_zero hs)
  have hS0' : 2 * S p.1 p.2 ≠ 0 := mul_ne_zero two_ne_zero hS0
  have hDZ : (Dm p.1 p.2 * Z p.1 p.2)^2 ≠ 0 := pow_ne_zero _ (mul_ne_zero hD hZ0)
  have hy2 : p.1 ^ 2 ≠ 0 := pow_ne_zero _ h1
  have hB : Continuous (fun p : ℂ × ℂ => Bn p.1 p.2) := evalH2_continuous BnL
  have hDc : Continuous (fun p : ℂ × ℂ => Dm p.1 p.2) := evalH2_continuous DmL
  have hBy : Continuous (fun p : ℂ × ℂ => evalH2_y BnL p.1 p.2) := evalH2_y_continuous BnL
  have hDy : Continuous (fun p : ℂ × ℂ => evalH2_y DmL p.1 p.2) := evalH2_y_continuous DmL
  unfold By Z_y S_y PQ_y Phi3
  fun_prop (disch := assumption)

theorem continuousAt_Aw {p : ℂ × ℂ} (h1 : p.1 ≠ 0) (h2 : p.2 ≠ 0)
    (hs : 1 - PQ p.1 p.2 ∈ slitPlane) (hD : Dm p.1 p.2 ≠ 0) :
    ContinuousAt (fun p : ℂ × ℂ => Aw p.1 p.2) p := by
  have hS := continuousAt_S h1 h2 hs
  have hZ := continuousAt_Z h1 h2 hs
  have hZ0 : Z p.1 p.2 ≠ 0 := Z_ne_zero h1 h2 (slitPlane_ne_zero hs)
  have hS0 : S p.1 p.2 ≠ 0 := S_ne_zero (slitPlane_ne_zero hs)
  have hS0' : 2 * S p.1 p.2 ≠ 0 := mul_ne_zero two_ne_zero hS0
  have hDZ : (Dm p.1 p.2 * Z p.1 p.2)^2 ≠ 0 := pow_ne_zero _ (mul_ne_zero hD hZ0)
  have hw2 : p.2 ^ 2 ≠ 0 := pow_ne_zero _ h2
  have hB : Continuous (fun p : ℂ × ℂ => Pt p.1 p.2) := evalH2_continuous PtL
  have hDc : Continuous (fun p : ℂ × ℂ => Dm p.1 p.2) := evalH2_continuous DmL
  have hBw : Continuous (fun p : ℂ × ℂ => evalH2_w PtL p.1 p.2) := evalH2_w_continuous PtL
  have hDw : Continuous (fun p : ℂ × ℂ => evalH2_w DmL p.1 p.2) := evalH2_w_continuous DmL
  unfold Aw Z_w S_w PQ_w Phi2
  fun_prop (disch := assumption)

theorem differentiableAt_G {y w : ℂ} (hy : y ≠ 0) (hw : w ≠ 0) (hs : 1 - PQ y w ∈ slitPlane) :
    DifferentiableAt ℂ (fun w => G y w) w := by
  have hZ := (hasDerivAt_Z_w y hw hs).differentiableAt
  have hZ0 : Z y w ≠ 0 := Z_ne_zero hy hw (slitPlane_ne_zero hs)
  have hZ3 : Z y w ^ 3 ≠ 0 := pow_ne_zero _ hZ0
  unfold G
  fun_prop (disch := assumption)

/-! ### Points on the circles -/

theorem norm_circleMap_zero' {ρ : ℝ} (hρ : 0 ≤ ρ) (γ : ℝ) : ‖circleMap 0 ρ γ‖ = ρ := by
  rw [norm_circleMap_zero, abs_of_nonneg hρ]

theorem circleMap_ne_zero' {ρ : ℝ} (hρ : 0 < ρ) (γ : ℝ) : circleMap 0 ρ γ ≠ 0 := by
  intro h
  have := norm_circleMap_zero' hρ.le γ
  rw [h, norm_zero] at this
  linarith

theorem cos_bounds (β : ℝ) : -1 ≤ Real.cos β ∧ Real.cos β ≤ 1 :=
  ⟨Real.neg_one_le_cos β, Real.cos_le_one β⟩

/-- Slit-plane condition on the annulus, for `y` on the unit circle. -/
theorem slit_yc (β : ℝ) {w : ℂ} (hw1 : 1/6 ≤ ‖w‖) (hw2 : ‖w‖ ≤ 1) :
    1 - PQ (yc β) w ∈ slitPlane :=
  one_sub_PQ_mem_slitPlane (yc_add_inv β) (cos_bounds β).1 (cos_bounds β).2 hw1 hw2

/-! ### Cauchy for `G` on the annulus -/

theorem circleIntegral_G_eq (β : ℝ) {ρ : ℝ} (h1 : 1/6 ≤ ρ) (h2 : ρ ≤ 1) :
    (∮ w in C(0, 1), G (yc β) w) = ∮ w in C(0, ρ), G (yc β) w := by
  have hd : ∀ w ∈ closedBall (0:ℂ) 1 \ ball 0 ρ, DifferentiableAt ℂ (fun w => G (yc β) w) w := by
    intro w hw
    simp only [mem_diff, mem_closedBall, mem_ball, _root_.dist_zero_right, not_lt] at hw
    have hw1 : 1/6 ≤ ‖w‖ := h1.trans hw.2
    have hw0 : w ≠ 0 := by
      intro h; rw [h, norm_zero] at hw1; linarith
    exact differentiableAt_G (yc_ne_zero β) hw0 (slit_yc β hw1 hw.1)
  refine circleIntegral_eq_of_differentiable_on_annulus_off_countable (by linarith) h2
    Set.countable_empty (fun w hw => (hd w hw).continuousAt.continuousWithinAt) ?_
  intro w hw
  apply hd
  simp only [mem_diff, mem_ball, mem_closedBall, _root_.dist_zero_right, not_le, mem_empty_iff_false,
    not_false_eq_true, and_true] at hw ⊢
  exact ⟨hw.1.le, not_lt.2 hw.2.le⟩

/-! ### Differentiation under the integral sign -/

theorem hasDerivAt_intervalIntegral_of_continuousOn {F F' : ℝ → ℝ → ℂ} {J : Set ℝ}
    (hJ : IsOpen J) {β₀ : ℝ} (hβ₀ : β₀ ∈ J) (a b : ℝ)
    (hF : ∀ β ∈ J, Continuous (F β))
    (hF' : ContinuousOn (fun p : ℝ × ℝ => F' p.1 p.2) (J ×ˢ univ))
    (hd : ∀ β ∈ J, ∀ γ, HasDerivAt (fun β => F β γ) (F' β γ) β) :
    HasDerivAt (fun β => ∫ γ in a..b, F β γ) (∫ γ in a..b, F' β₀ γ) β₀ := by
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hJ β₀ hβ₀
  have hcb : closedBall β₀ (ε/2) ⊆ J := (closedBall_subset_ball (by linarith)).trans hball
  have hK : IsCompact (closedBall β₀ (ε/2) ×ˢ uIcc a b) := (isCompact_closedBall _ _).prod isCompact_uIcc
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn
    (hF'.mono (prod_mono hcb (subset_univ _)))
  have hs : ball β₀ (ε/2) ∈ nhds β₀ := ball_mem_nhds _ (by linarith)
  have hsub : ball β₀ (ε/2) ⊆ J := ball_subset_closedBall.trans hcb
  refine (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le (bound := fun _ => C)
    hs ?_ ?_ ?_ ?_ ?_ ?_).2
  · exact Filter.eventually_of_mem hs fun x hx => (hF x (hsub hx)).aestronglyMeasurable
  · exact (hF β₀ hβ₀).intervalIntegrable a b
  · have : Continuous (F' β₀) :=
      hF'.comp_continuous (continuous_const.prodMk continuous_id) (fun γ => ⟨hβ₀, trivial⟩)
    exact this.aestronglyMeasurable
  · refine Filter.Eventually.of_forall fun t ht x hx => hC (x, t) ⟨ball_subset_closedBall hx, ?_⟩
    exact uIoc_subset_uIcc ht
  · exact intervalIntegrable_const
  · exact Filter.Eventually.of_forall fun t _ x hx => hd x (hsub hx) t

/-! ### `Ψ` and `K` -/

def Psi (ρ β : ℝ) : ℂ := ∮ w in C(0, ρ), Bhat (yc β) w
def Kc (ρ β : ℝ) : ℂ := I * yc β * ∮ w in C(0, ρ), G (yc β) w

theorem continuous_Kc {ρ : ℝ} (h1 : 1/6 ≤ ρ) (h2 : ρ ≤ 1) : Continuous (Kc ρ) := by
  have hρ : 0 < ρ := by linarith
  have hG : Continuous (fun p : ℝ × ℝ => circleMap 0 ρ p.2 * I * G (yc p.1) (circleMap 0 ρ p.2)) := by
    have hc : Continuous (fun p : ℝ × ℝ => (yc p.1, circleMap 0 ρ p.2)) :=
      (continuous_yc.comp continuous_fst).prodMk ((continuous_circleMap 0 ρ).comp continuous_snd)
    have hG' : Continuous (fun p : ℝ × ℝ => G (yc p.1) (circleMap 0 ρ p.2)) := by
      refine continuous_iff_continuousAt.2 fun p => ?_
      have := continuousAt_G (p := (yc p.1, circleMap 0 ρ p.2)) (yc_ne_zero _)
        (circleMap_ne_zero' hρ _) (slit_yc _ (by rw [norm_circleMap_zero' hρ.le]; exact h1)
          (by rw [norm_circleMap_zero' hρ.le]; exact h2))
      exact ContinuousAt.comp (g := fun p : ℂ × ℂ => G p.1 p.2)
        (f := fun p : ℝ × ℝ => (yc p.1, circleMap 0 ρ p.2)) this hc.continuousAt
    fun_prop
  have e : Kc ρ = fun β => I * yc β * ∫ γ in (0:ℝ)..2 * Real.pi,
      circleMap 0 ρ γ * I * G (yc β) (circleMap 0 ρ γ) := by
    funext β; simp only [Kc, circleIntegral, deriv_circleMap, smul_eq_mul]
  rw [e]
  have := intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    (f := fun β γ => circleMap 0 ρ γ * I * G (yc β) (circleMap 0 ρ γ)) (μ := MeasureTheory.volume)
    (a₀ := 0) (b₀ := 2 * Real.pi) (by exact hG)
  have h2 := continuous_yc
  fun_prop

theorem integral_Aw_eq_zero {ρ : ℝ} (hρ : 0 < ρ) (β : ℝ)
    (hD : ∀ w, ‖w‖ = ρ → Dm (yc β) w ≠ 0) (hslit : ∀ w, ‖w‖ = ρ → 1 - PQ (yc β) w ∈ slitPlane) :
    ∫ γ in (0:ℝ)..2 * Real.pi, Aw (yc β) (circleMap 0 ρ γ) * (circleMap 0 ρ γ * I) = 0 := by
  have hderiv : ∀ γ, HasDerivAt (fun γ => Af (yc β) (circleMap 0 ρ γ))
      (Aw (yc β) (circleMap 0 ρ γ) * (circleMap 0 ρ γ * I)) γ := by
    intro γ
    have hw := norm_circleMap_zero' hρ.le γ
    exact (hasDerivAt_Af_w (yc_ne_zero β) (circleMap_ne_zero' hρ γ) (hslit _ hw) (hD _ hw)).comp γ
      (hasDerivAt_circleMap 0 ρ γ)
  have hcont : Continuous (fun γ => Aw (yc β) (circleMap 0 ρ γ) * (circleMap 0 ρ γ * I)) := by
    have hc : Continuous (fun γ : ℝ => (yc β, circleMap 0 ρ γ)) :=
      continuous_const.prodMk (continuous_circleMap 0 ρ)
    have hA : Continuous (fun γ => Aw (yc β) (circleMap 0 ρ γ)) := by
      refine continuous_iff_continuousAt.2 fun γ => ?_
      have hw := norm_circleMap_zero' hρ.le γ
      exact ContinuousAt.comp (g := fun p : ℂ × ℂ => Aw p.1 p.2)
        (f := fun γ : ℝ => (yc β, circleMap 0 ρ γ)) (continuousAt_Aw (p := (yc β, circleMap 0 ρ γ))
        (yc_ne_zero β) (circleMap_ne_zero' hρ γ) (hslit _ hw) (hD _ hw)) hc.continuousAt
    fun_prop
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun γ _ => hderiv γ)
    (hcont.intervalIntegrable _ _)]
  have hp := periodic_circleMap 0 ρ 0
  rw [zero_add] at hp
  rw [hp, sub_self]

theorem hasDerivAt_Psi {ρ : ℝ} (hρ1 : 1/6 ≤ ρ) (hρ2 : ρ ≤ 1) {J : Set ℝ} (hJ : IsOpen J)
    (hDm : ∀ β ∈ J, ∀ w, ‖w‖ = ρ → Dm (yc β) w ≠ 0) {β₀ : ℝ} (hβ₀ : β₀ ∈ J) :
    HasDerivAt (Psi ρ) (Kc ρ β₀) β₀ := by
  have hρ : 0 < ρ := by linarith
  have hslit : ∀ β, ∀ w, ‖w‖ = ρ → 1 - PQ (yc β) w ∈ slitPlane := fun β w hw =>
    slit_yc β (by rw [hw]; exact hρ1) (by rw [hw]; exact hρ2)
  have hwn : ∀ γ, ‖circleMap 0 ρ γ‖ = ρ := norm_circleMap_zero' hρ.le
  have hc : Continuous (fun p : ℝ × ℝ => (yc p.1, circleMap 0 ρ p.2)) :=
    (continuous_yc.comp continuous_fst).prodMk ((continuous_circleMap 0 ρ).comp continuous_snd)
  -- the integrand and its β-derivative
  set F : ℝ → ℝ → ℂ := fun β γ => circleMap 0 ρ γ * I * Bhat (yc β) (circleMap 0 ρ γ) with hF
  set F' : ℝ → ℝ → ℂ := fun β γ =>
    circleMap 0 ρ γ * I * (By (yc β) (circleMap 0 ρ γ) * (yc β * I)) with hF'
  have hPsi : Psi ρ = fun β => ∫ γ in (0:ℝ)..2 * Real.pi, F β γ := by
    funext β
    simp only [Psi, circleIntegral, deriv_circleMap, smul_eq_mul, hF]
  have key : HasDerivAt (fun β => ∫ γ in (0:ℝ)..2 * Real.pi, F β γ)
      (∫ γ in (0:ℝ)..2 * Real.pi, F' β₀ γ) β₀ := by
    refine hasDerivAt_intervalIntegral_of_continuousOn hJ hβ₀ _ _ ?_ ?_ ?_
    · intro β hβ
      have : Continuous (fun γ => Bhat (yc β) (circleMap 0 ρ γ)) := by
        refine continuous_iff_continuousAt.2 fun γ => ?_
        exact ContinuousAt.comp (g := fun p : ℂ × ℂ => Bhat p.1 p.2)
          (f := fun γ : ℝ => (yc β, circleMap 0 ρ γ))
          (continuousAt_Bhat (p := (yc β, circleMap 0 ρ γ)) (yc_ne_zero β)
          (circleMap_ne_zero' hρ γ) (hslit _ _ (hwn γ)) (hDm β hβ _ (hwn γ)))
          (continuous_const.prodMk (continuous_circleMap 0 ρ)).continuousAt
      simp only [hF]
      fun_prop
    · intro p hp
      have hBy : ContinuousAt (fun p : ℝ × ℝ => By (yc p.1) (circleMap 0 ρ p.2)) p :=
        ContinuousAt.comp (g := fun p : ℂ × ℂ => By p.1 p.2)
          (f := fun p : ℝ × ℝ => (yc p.1, circleMap 0 ρ p.2))
          (continuousAt_By (p := (yc p.1, circleMap 0 ρ p.2)) (yc_ne_zero _)
          (circleMap_ne_zero' hρ _) (hslit _ _ (hwn _)) (hDm p.1 hp.1 _ (hwn _)))
          hc.continuousAt
      have : ContinuousAt (fun p : ℝ × ℝ => F' p.1 p.2) p := by
        simp only [hF']
        have h2 := continuous_yc
        fun_prop
      exact this.continuousWithinAt
    · intro β hβ γ
      simp only [hF, hF']
      have h1 := (hasDerivAt_Bhat_y (yc_ne_zero β) (circleMap_ne_zero' hρ γ) (hslit _ _ (hwn γ))
        (hDm β hβ _ (hwn γ))).comp β (hasDerivAt_yc β)
      exact h1.const_mul _
  rw [hPsi]
  convert key using 1
  -- identify the integral of F' with Kc
  have hst : ∀ γ, F' β₀ γ = Aw (yc β₀) (circleMap 0 ρ γ) * (circleMap 0 ρ γ * I) * (yc β₀ * I)
      + (yc β₀ * I) * (circleMap 0 ρ γ * I * G (yc β₀) (circleMap 0 ρ γ)) := by
    intro γ
    simp only [hF']
    rw [← stokes_identity (yc_ne_zero β₀) (circleMap_ne_zero' hρ γ)
      (slitPlane_ne_zero (hslit _ _ (hwn γ))) (hDm β₀ hβ₀ _ (hwn γ))]
    ring
  simp_rw [hst]
  have hA : Continuous (fun γ => Aw (yc β₀) (circleMap 0 ρ γ) * (circleMap 0 ρ γ * I)) := by
    have hA' : Continuous (fun γ => Aw (yc β₀) (circleMap 0 ρ γ)) := by
      refine continuous_iff_continuousAt.2 fun γ => ?_
      exact ContinuousAt.comp (g := fun p : ℂ × ℂ => Aw p.1 p.2)
        (f := fun γ : ℝ => (yc β₀, circleMap 0 ρ γ))
        (continuousAt_Aw (p := (yc β₀, circleMap 0 ρ γ)) (yc_ne_zero β₀)
        (circleMap_ne_zero' hρ γ) (hslit _ _ (hwn γ)) (hDm β₀ hβ₀ _ (hwn γ)))
        (continuous_const.prodMk (continuous_circleMap 0 ρ)).continuousAt
    fun_prop
  have hGc : Continuous (fun γ => circleMap 0 ρ γ * I * G (yc β₀) (circleMap 0 ρ γ)) := by
    have hG' : Continuous (fun γ => G (yc β₀) (circleMap 0 ρ γ)) := by
      refine continuous_iff_continuousAt.2 fun γ => ?_
      exact ContinuousAt.comp (g := fun p : ℂ × ℂ => G p.1 p.2)
        (f := fun γ : ℝ => (yc β₀, circleMap 0 ρ γ))
        (continuousAt_G (p := (yc β₀, circleMap 0 ρ γ)) (yc_ne_zero β₀)
        (circleMap_ne_zero' hρ γ) (hslit _ _ (hwn γ)))
        (continuous_const.prodMk (continuous_circleMap 0 ρ)).continuousAt
    fun_prop
  rw [intervalIntegral.integral_add ((hA.mul continuous_const).intervalIntegrable _ _)
    ((continuous_const.mul hGc).intervalIntegrable _ _),
    intervalIntegral.integral_mul_const, integral_Aw_eq_zero hρ β₀ (hDm β₀ hβ₀) (hslit β₀),
    zero_mul, zero_add, intervalIntegral.integral_const_mul]
  simp only [Kc, circleIntegral, deriv_circleMap, smul_eq_mul]
  ring

end Sun

end

/-! ## Section P4 -/

noncomputable section
namespace Sun
open Complex Set Metric

/-! ### The residue computation at the crossing point `w = -1/4` -/

/-- `Drest = D0a * D0b * D2`: the part of `Dm` not vanishing at the crossing point. -/
def Drest (y w : ℂ) : ℂ := D0a y w * D0b y w * D2 y w

theorem D1_at_cstar {y : ℂ} (hy0 : y ≠ 0) (hyc : y + y⁻¹ = 2 * ((-7/25 : ℝ) : ℂ)) (w : ℂ) :
    D1 y w = -(64/25) * y * (w + 4) * (w + 1/4) := by
  rw [D1_eq hy0 hyc]; push_cast; ring

theorem Bhat_eq_div {y : ℂ} (hy0 : y ≠ 0) (hyc : y + y⁻¹ = 2 * ((-7/25 : ℝ) : ℂ)) (w : ℂ) :
    Bhat y w = (Bn y w / (-(64/25) * y * (w + 4) * Drest y w * Z y w)) / (w + 1/4) := by
  rw [Bhat, Dm_factor, D1_at_cstar hy0 hyc, div_div, Drest]
  congr 1
  ring

theorem Drest_ne_zero {y w : ℂ} {c : ℝ} (hy0 : y ≠ 0) (hyc : y + y⁻¹ = 2 * (c:ℂ))
    (hc1 : -1 ≤ c) (hc2 : c ≤ 1) (hw1 : 1/6 ≤ ‖w‖) (hw2 : ‖w‖ ≤ 1) : Drest y w ≠ 0 :=
  mul_ne_zero (mul_ne_zero (D0a_ne_zero hy0 hyc hc1 hc2 hw1) (D0b_ne_zero hy0 hyc hc1 hc2 hw2))
    (D2_ne_zero hy0 hyc hc1 hc2 hw1 hw2)

theorem differentiableAt_Drest (y w : ℂ) : DifferentiableAt ℂ (fun w => Drest y w) w := by
  unfold Drest D0a D0b D2
  fun_prop

/-- The regular part `f` of `Bhat` near the pole. -/
def fres (y w : ℂ) : ℂ := Bn y w / (-(64/25) * y * (w + 4) * Drest y w * Z y w)

theorem differentiableAt_fres {y w : ℂ} {c : ℝ} (hy0 : y ≠ 0) (hyc : y + y⁻¹ = 2 * (c:ℂ))
    (hc1 : -1 ≤ c) (hc2 : c ≤ 1) (hw1 : 1/6 ≤ ‖w‖) (hw2 : ‖w‖ ≤ 1) :
    DifferentiableAt ℂ (fun w => fres y w) w := by
  have hw0 : w ≠ 0 := by intro h; rw [h, norm_zero] at hw1; linarith
  have hs := one_sub_PQ_mem_slitPlane hyc hc1 hc2 hw1 hw2
  have hZ := (hasDerivAt_Z_w y hw0 hs).differentiableAt
  have hZ0 : Z y w ≠ 0 := Z_ne_zero hy0 hw0 (slitPlane_ne_zero hs)
  have hDr := Drest_ne_zero hy0 hyc hc1 hc2 hw1 hw2
  have hDrd := differentiableAt_Drest y w
  have hw4 : w + 4 ≠ 0 := by
    intro h
    have : w = -4 := by linear_combination h
    rw [this] at hw2; norm_num at hw2
  have hden : -(64/25) * y * (w + 4) * Drest y w * Z y w ≠ 0 := by
    refine mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) hy0) hw4) hDr) hZ0
  have hB := (evalH2_hasDerivAt_w BnL y w).differentiableAt
  unfold fres
  exact DifferentiableAt.div (by exact hB) (by fun_prop) hden

theorem residue_lemma {y : ℂ} (hy0 : y ≠ 0) (hyc : y + y⁻¹ = 2 * ((-7/25 : ℝ) : ℂ)) :
    (∮ w in C(0, 1/2), Bhat y w) - (∮ w in C(0, 1/6), Bhat y w)
      = 2 * Real.pi * I * fres y (-1/4) := by
  have hc1 : (-1:ℝ) ≤ -7/25 := by norm_num
  have hc2 : (-7/25:ℝ) ≤ 1 := by norm_num
  set a : ℂ := -1/4 with ha
  have hna : ‖a‖ = 1/4 := by rw [ha]; norm_num
  set g := dslope (fun w => fres y w) a with hg
  -- Bhat = g + fres a / (w - a) away from a
  have hsplit : ∀ w, w ≠ a → Bhat y w = g w + fres y a * (w - a)⁻¹ := by
    intro w hw
    rw [Bhat_eq_div hy0 hyc, hg, dslope_of_ne _ hw, slope_def_field]
    have : w - a ≠ 0 := sub_ne_zero.2 hw
    have e : w + 1/4 = w - a := by rw [ha]; ring
    rw [e]
    unfold fres
    field_simp
    ring
  -- the annulus is a neighbourhood of a
  have hnhds : closedBall (0:ℂ) (1/2) \ ball 0 (1/6) ∈ nhds a := by
    refine mem_nhds_iff.2 ⟨ball (0:ℂ) (1/2) \ closedBall 0 (1/6), ?_,
      isOpen_ball.sdiff isClosed_closedBall, ?_⟩
    · intro w hw
      simp only [mem_diff, mem_ball, mem_closedBall, _root_.dist_zero_right, not_le, not_lt] at hw ⊢
      exact ⟨hw.1.le, hw.2.le⟩
    · simp only [mem_diff, mem_ball, mem_closedBall, _root_.dist_zero_right, not_le, hna]; norm_num
  have hfd : ∀ w ∈ closedBall (0:ℂ) (1/2) \ ball 0 (1/6), DifferentiableAt ℂ (fun w => fres y w) w := by
    intro w hw
    simp only [mem_diff, mem_closedBall, mem_ball, _root_.dist_zero_right, not_lt] at hw
    exact differentiableAt_fres hy0 hyc hc1 hc2 hw.2 (hw.1.trans (by norm_num))
  have hamem : a ∈ closedBall (0:ℂ) (1/2) \ ball 0 (1/6) := by
    simp only [mem_diff, mem_ball, mem_closedBall, _root_.dist_zero_right, not_lt, hna]; norm_num
  -- g is continuous on the closed annulus and differentiable off a
  have hgc : ContinuousOn g (closedBall (0:ℂ) (1/2) \ ball 0 (1/6)) :=
    (continuousOn_dslope hnhds).2 ⟨fun w hw => (hfd w hw).continuousAt.continuousWithinAt, hfd a hamem⟩
  have hgd : ∀ w ∈ (ball (0:ℂ) (1/2) \ closedBall 0 (1/6)) \ {a}, DifferentiableAt ℂ g w := by
    intro w hw
    simp only [mem_diff, mem_singleton_iff] at hw
    refine (differentiableAt_dslope_of_ne hw.2).2 (hfd w ?_)
    simp only [mem_diff, mem_ball, mem_closedBall, _root_.dist_zero_right, not_le, not_lt] at hw ⊢
    exact ⟨hw.1.1.le, hw.1.2.le⟩
  have hg_eq : (∮ w in C(0, 1/2), g w) = ∮ w in C(0, 1/6), g w :=
    circleIntegral_eq_of_differentiable_on_annulus_off_countable (by norm_num) (by norm_num)
      (countable_singleton a) hgc hgd
  -- splitting the circle integrals
  have hsphere : ∀ ρ : ℝ, ρ ≠ 1/4 → ∀ w ∈ sphere (0:ℂ) ρ, w ≠ a := by
    intro ρ hρ w hw h
    rw [mem_sphere_zero_iff_norm, h, hna] at hw
    exact hρ hw.symm
  have hsplit_int : ∀ ρ : ℝ, 0 ≤ ρ → ρ ≠ 1/4 →
      ContinuousOn g (sphere (0:ℂ) ρ) →
      (∮ w in C(0, ρ), Bhat y w) = (∮ w in C(0, ρ), g w) + fres y a * ∮ w in C(0, ρ), (w - a)⁻¹ := by
    intro ρ hρ hρ' hgcont
    rw [circleIntegral.integral_congr hρ (fun w hw => hsplit w (hsphere ρ hρ' w hw)),
      circleIntegral.integral_add (hgcont.circleIntegrable hρ), circleIntegral.integral_const_mul]
    refine ContinuousOn.circleIntegrable hρ (continuousOn_const.mul ?_)
    refine ContinuousOn.inv₀ (continuousOn_id.sub continuousOn_const) ?_
    intro w hw
    exact sub_ne_zero.2 (hsphere ρ hρ' w hw)
  have hsub1 : sphere (0:ℂ) (1/2) ⊆ closedBall (0:ℂ) (1/2) \ ball 0 (1/6) := by
    intro w hw
    rw [mem_sphere_zero_iff_norm] at hw
    simp only [mem_diff, mem_ball, mem_closedBall, _root_.dist_zero_right, not_lt, hw]; norm_num
  have hsub2 : sphere (0:ℂ) (1/6) ⊆ closedBall (0:ℂ) (1/2) \ ball 0 (1/6) := by
    intro w hw
    rw [mem_sphere_zero_iff_norm] at hw
    simp only [mem_diff, mem_ball, mem_closedBall, _root_.dist_zero_right, not_lt, hw]; norm_num
  rw [hsplit_int (1/2) (by norm_num) (by norm_num) (hgc.mono hsub1),
    hsplit_int (1/6) (by norm_num) (by norm_num) (hgc.mono hsub2), hg_eq]
  have h1 : (∮ w in C(0, 1/2), (w - a)⁻¹) = 2 * Real.pi * I := by
    apply circleIntegral.integral_sub_inv_of_mem_ball
    simp only [mem_ball, _root_.dist_zero_right, hna]; norm_num
  have h2 : (∮ w in C(0, 1/6), (w - a)⁻¹) = 0 := by
    apply circleIntegral_eq_zero_of_differentiable_on_off_countable (by norm_num) countable_empty
    · refine ContinuousOn.inv₀ (continuousOn_id.sub continuousOn_const) ?_
      intro w hw
      simp only [mem_closedBall, _root_.dist_zero_right] at hw
      intro h
      have : w = a := sub_eq_zero.1 h
      rw [this, hna] at hw; norm_num at hw
    · intro w hw
      simp only [mem_diff, mem_ball, _root_.dist_zero_right, mem_empty_iff_false, not_false_eq_true,
        and_true] at hw
      have : w - a ≠ 0 := by
        intro h
        have : w = a := sub_eq_zero.1 h
        rw [this, hna] at hw; norm_num at hw
      exact (differentiableAt_id.sub_const a).inv this
  rw [h1, h2]
  ring

/-! ### Evaluation of the residue -/

theorem Z_at_quarter (y : ℂ) : Z y (-1/4) = -7 * y := by
  have h3 : Phi3 (-1/4) = 0 := by unfold Phi3; norm_num
  have hPQ : PQ y (-1/4) = 0 := by unfold PQ; rw [h3]; simp
  unfold Z S
  rw [hPQ, sub_zero, Complex.one_cpow]
  ring

theorem fres_at_quarter {y : ℂ} : fres y (-1/4) = Bn y (-1/4) / ((336/5) * y^2 * Drest y (-1/4)) := by
  unfold fres
  rw [Z_at_quarter]
  congr 1
  ring

set_option maxRecDepth 4000 in
theorem Bn_at_quarter {y : ℂ} (hm : 25*y^2 + 14*y + 25 = 0) :
    Bn y (-1/4) = (2295075749707475440369664/3814697265625:ℂ)
      + (-398895279373821343594184704/95367431640625:ℂ)*y := by
  simp only [Bn, evalH2, BnL, List.map, evalH]
  linear_combination ((-2295075749707475440369664/95367431640625:ℂ) + (176548386353307158417449481/976562500000000:ℂ)*y + (-188411848414021268919169/2441406250000:ℂ)*y^2 + (-215044704178500175999789/1562500000000:ℂ)*y^3 + (300110590018338158843/1953125000:ℂ)*y^4 + (79661222904205283733/1250000000:ℂ)*y^5 + (-35720586355277824/390625:ℂ)*y^6 + (-25039891448875877/2000000:ℂ)*y^7 + (2778608971173/5000:ℂ)*y^8 + (388259203101/6400:ℂ)*y^9 + (-12823615/16:ℂ)*y^10 + (644175/256:ℂ)*y^11) * hm

theorem Drest_at_quarter {y : ℂ} (hm : 25*y^2 + 14*y + 25 = 0) :
    y^2 * Drest y (-1/4) = (-1336582694359969824768/3814697265625:ℂ)
      + (-13614104370181153226752/95367431640625:ℂ)*y := by
  simp only [Drest, D0a, D0b, D2]
  linear_combination ((1336582694359969824768/95367431640625:ℂ) + (-8156885361373478912/3814697265625:ℂ)*y + (-31293087888807957047/2441406250000:ℂ)*y^2 + (227441232147341387/24414062500:ℂ)*y^3 + (7433448384036017/976562500:ℂ)*y^4 + (-526493109769403/39062500:ℂ)*y^5 + (-6669695120621/3125000:ℂ)*y^6 + (5892110357/62500:ℂ)*y^7 + (28131537/2500:ℂ)*y^8 + (-16933/100:ℂ)*y^9 + (9/16:ℂ)*y^10) * hm

def ystar : ℂ := (-7 + 24 * I) / 25
def ystar' : ℂ := (-7 - 24 * I) / 25

theorem ystar_m : 25 * ystar^2 + 14 * ystar + 25 = 0 := by
  unfold ystar; ring_nf; rw [I_sq]; ring

theorem ystar'_m : 25 * ystar'^2 + 14 * ystar' + 25 = 0 := by
  unfold ystar'; ring_nf; rw [I_sq]; ring

theorem fres_ystar : fres ystar (-1/4) = (385/2) * I := by
  rw [fres_at_quarter, show (336/5 : ℂ) * ystar^2 * Drest ystar (-1/4) = (336/5) * (ystar^2 * Drest ystar (-1/4)) by ring,
    Drest_at_quarter ystar_m, Bn_at_quarter ystar_m]
  rw [div_eq_iff]
  · unfold ystar; ring_nf; rw [I_sq]; try ring
  · unfold ystar
    intro h
    have h2 := congrArg Complex.im h
    simp at h2

theorem fres_ystar' : fres ystar' (-1/4) = -(385/2) * I := by
  rw [fres_at_quarter, show (336/5 : ℂ) * ystar'^2 * Drest ystar' (-1/4) = (336/5) * (ystar'^2 * Drest ystar' (-1/4)) by ring,
    Drest_at_quarter ystar'_m, Bn_at_quarter ystar'_m]
  rw [div_eq_iff]
  · unfold ystar'; ring_nf; rw [I_sq]; try ring
  · unfold ystar'
    intro h
    have h2 := congrArg Complex.im h
    simp at h2

end Sun

end

/-! ## Section P5 -/

noncomputable section
namespace Sun
open Complex Set Metric

/-! ### The special angle β* = arccos(-7/25) -/

def βs : ℝ := Real.arccos (-7/25)

theorem cos_βs : Real.cos βs = -7/25 := Real.cos_arccos (by norm_num) (by norm_num)

theorem sin_βs : Real.sin βs = 24/25 := by
  unfold βs
  rw [Real.sin_arccos]
  rw [show (1 - (-7/25:ℝ)^2) = (24/25)^2 by norm_num]
  exact Real.sqrt_sq (by norm_num)

theorem βs_pos : 0 < βs := Real.arccos_pos.mpr (by norm_num)
theorem βs_lt_pi : βs < Real.pi := by
  unfold βs
  rw [Real.arccos_eq_pi_div_two_sub_arcsin]
  have := Real.neg_pi_div_two_lt_arcsin.mpr (show (-1:ℝ) < -7/25 by norm_num)
  linarith

theorem yc_βs : yc βs = ystar := by
  unfold yc ystar
  rw [Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin, cos_βs, sin_βs]
  push_cast; ring

theorem yc_neg_βs : yc (-βs) = ystar' := by
  unfold yc ystar'
  rw [Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin,
    Real.cos_neg, Real.sin_neg, cos_βs, sin_βs]
  push_cast; ring

/-! ### Arcs -/

theorem cos_gt_of_mem_arc1 {β : ℝ} (h : β ∈ Icc (-βs) βs) : -7/9 < Real.cos β := by
  have h1 : Real.cos βs ≤ Real.cos |β| := by
    apply Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg _) βs_lt_pi.le
    rw [abs_le]; exact ⟨h.1, h.2⟩
  rw [Real.cos_abs, cos_βs] at h1
  linarith

theorem cos_lt_of_mem_arc2 {β : ℝ} (h : β ∈ Icc βs (2 * Real.pi - βs)) :
    Real.cos β < -1/47 := by
  rcases le_or_gt β Real.pi with hβ | hβ
  · have h1 : Real.cos β ≤ Real.cos βs :=
      Real.cos_le_cos_of_nonneg_of_le_pi βs_pos.le hβ h.1
    rw [cos_βs] at h1; linarith
  · have h1 : Real.cos (2 * Real.pi - β) ≤ Real.cos βs := by
      apply Real.cos_le_cos_of_nonneg_of_le_pi βs_pos.le
      · linarith
      · linarith [h.2]
    rw [Real.cos_two_pi_sub, cos_βs] at h1; linarith

def J1 : Set ℝ := {β | -7/9 < Real.cos β}
def J2 : Set ℝ := {β | Real.cos β < -1/47}

theorem isOpen_J1 : IsOpen J1 := isOpen_lt continuous_const Real.continuous_cos
theorem isOpen_J2 : IsOpen J2 := isOpen_lt Real.continuous_cos continuous_const

theorem hDm_J1 : ∀ β ∈ J1, ∀ w : ℂ, ‖w‖ = 1/2 → Dm (yc β) w ≠ 0 := fun β hβ w hw =>
  Dm_ne_zero_half (yc_ne_zero β) (yc_add_inv β) (cos_bounds β).1 (cos_bounds β).2 hβ hw

theorem hDm_J2 : ∀ β ∈ J2, ∀ w : ℂ, ‖w‖ = 1/6 → Dm (yc β) w ≠ 0 := fun β hβ w hw =>
  Dm_ne_zero_sixth (yc_ne_zero β) (yc_add_inv β) (cos_bounds β).1 (cos_bounds β).2 hβ hw

/-! ### Fundamental theorem of calculus on the two arcs -/

theorem Kc_eq_Kc_one {ρ : ℝ} (h1 : 1/6 ≤ ρ) (h2 : ρ ≤ 1) (β : ℝ) : Kc ρ β = Kc 1 β := by
  unfold Kc; rw [circleIntegral_G_eq β h1 h2]

theorem integral_arc1 :
    ∫ β in (-βs)..βs, Kc 1 β = Psi (1/2) βs - Psi (1/2) (-βs) := by
  have hint : IntervalIntegrable (Kc 1) MeasureTheory.volume (-βs) βs :=
    (continuous_Kc (by norm_num) le_rfl).intervalIntegrable _ _
  rw [← intervalIntegral.integral_eq_sub_of_hasDerivAt (f := Psi (1/2)) (f' := Kc 1) _ hint]
  intro β hβ
  rw [Set.uIcc_of_le (by linarith [βs_pos])] at hβ
  rw [← Kc_eq_Kc_one (ρ := 1/2) (by norm_num) (by norm_num) β]
  exact hasDerivAt_Psi (by norm_num) (by norm_num) isOpen_J1 hDm_J1 (cos_gt_of_mem_arc1 hβ)

theorem integral_arc2 :
    ∫ β in βs..(2 * Real.pi - βs), Kc 1 β = Psi (1/6) (-βs) - Psi (1/6) βs := by
  have hint : IntervalIntegrable (Kc 1) MeasureTheory.volume βs (2 * Real.pi - βs) :=
    (continuous_Kc (by norm_num) le_rfl).intervalIntegrable _ _
  have hper : Psi (1/6) (2 * Real.pi - βs) = Psi (1/6) (-βs) := by
    rw [show 2 * Real.pi - βs = -βs + 2 * Real.pi by ring]
    unfold Psi; rw [yc_periodic]
  rw [← hper,
    ← intervalIntegral.integral_eq_sub_of_hasDerivAt (f := Psi (1/6)) (f' := Kc 1) _ hint]
  intro β hβ
  rw [Set.uIcc_of_le (by linarith [βs_lt_pi])] at hβ
  rw [← Kc_eq_Kc_one (ρ := 1/6) (by norm_num) (by norm_num) β]
  exact hasDerivAt_Psi (by norm_num) (by norm_num) isOpen_J2 hDm_J2 (cos_lt_of_mem_arc2 hβ)

theorem hyc_ystar : ystar + ystar⁻¹ = 2 * ((-7/25 : ℝ) : ℂ) := by
  rw [← yc_βs, yc_add_inv, cos_βs]

theorem hyc_ystar' : ystar' + ystar'⁻¹ = 2 * ((-7/25 : ℝ) : ℂ) := by
  rw [← yc_neg_βs, yc_add_inv, Real.cos_neg, cos_βs]

theorem ystar_ne_zero : ystar ≠ 0 := by rw [← yc_βs]; exact yc_ne_zero _
theorem ystar'_ne_zero : ystar' ≠ 0 := by rw [← yc_neg_βs]; exact yc_ne_zero _

theorem integral_Kc_full :
    ∫ β in (-βs)..(2 * Real.pi - βs), Kc 1 β = -770 * Real.pi := by
  have hc := continuous_Kc (ρ := 1) (by norm_num) le_rfl
  rw [← intervalIntegral.integral_add_adjacent_intervals (b := βs)
    (hc.intervalIntegrable _ _) (hc.intervalIntegrable _ _), integral_arc1, integral_arc2]
  have e1 : Psi (1/2) βs - Psi (1/6) βs = 2 * Real.pi * I * fres ystar (-1/4) := by
    unfold Psi; rw [yc_βs]; exact residue_lemma ystar_ne_zero hyc_ystar
  have e2 : Psi (1/2) (-βs) - Psi (1/6) (-βs) = 2 * Real.pi * I * fres ystar' (-1/4) := by
    unfold Psi; rw [yc_neg_βs]; exact residue_lemma ystar'_ne_zero hyc_ystar'
  have : Psi (1/2) βs - Psi (1/2) (-βs) + (Psi (1/6) (-βs) - Psi (1/6) βs)
      = (Psi (1/2) βs - Psi (1/6) βs) - (Psi (1/2) (-βs) - Psi (1/6) (-βs)) := by ring
  rw [this, e1, e2, fres_ystar, fres_ystar']
  ring_nf; rw [I_sq]; ring

end Sun

end

/-! ## Section P6 -/

noncomputable section
namespace Sun
open Complex Set Metric

/-! ### The real integrand and its identification with `G` on the torus -/

def pq (β γ : ℝ) : ℝ := (14 + 2 * Real.cos β) * (17 + 8 * Real.cos γ) / 784
def Fr (β γ : ℝ) : ℝ := (367 + 1778 * pq β γ) / (Real.sqrt (1 - pq β γ))^3

theorem pq_le (β γ : ℝ) : pq β γ ≤ 400/784 := by
  unfold pq
  have h1 := cos_bounds β
  have h2 := cos_bounds γ
  have : (14 + 2 * Real.cos β) * (17 + 8 * Real.cos γ) ≤ 16 * 25 := by
    apply mul_le_mul <;> linarith
  linarith

theorem one_sub_pq_pos (β γ : ℝ) : 0 < 1 - pq β γ := by
  have := pq_le β γ; linarith

theorem circleMap_eq_yc (γ : ℝ) : circleMap 0 1 γ = yc γ := by
  simp [circleMap, yc]

theorem PQ_yc (β γ : ℝ) : PQ (yc β) (yc γ) = ((pq β γ : ℝ) : ℂ) := by
  unfold PQ Phi2 Phi3 pq
  have h1 := yc_add_inv β
  have h2 := yc_add_inv γ
  push_cast at h1 h2 ⊢
  linear_combination (1/784) * ((4 * yc γ + 17 + 4 * (yc γ)⁻¹) * h1 + 4 * (14 + 2 * Complex.cos β) * h2)

theorem S_yc (β γ : ℝ) : S (yc β) (yc γ) = ((Real.sqrt (1 - pq β γ) : ℝ) : ℂ) := by
  unfold S
  rw [PQ_yc, Real.sqrt_eq_rpow, Complex.ofReal_cpow (one_sub_pq_pos β γ).le]
  push_cast; norm_num

theorem Fr_eq (β γ : ℝ) : ((Fr β γ : ℝ) : ℂ) = 28 * yc β * yc γ * G (yc β) (yc γ) := by
  have hpos := one_sub_pq_pos β γ
  set s := Real.sqrt (1 - pq β γ) with hs
  have hs2 : s^2 = 1 - pq β γ := Real.sq_sqrt hpos.le
  have hs0 : s ≠ 0 := (Real.sqrt_pos.mpr hpos).ne'
  have hFr : Fr β γ = (367 + 1778 * (1 - s^2)) / s^3 := by
    unfold Fr; rw [hs2]; ring
  have hsc : (s : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hs0
  have hy := yc_ne_zero β
  have hw := yc_ne_zero γ
  rw [hFr]; unfold G Z; rw [S_yc, ← hs]
  push_cast
  field_simp
  ring

def Ir (β : ℝ) : ℝ := ∫ γ in (0:ℝ)..(2 * Real.pi), Fr β γ

theorem Ir_eq (β : ℝ) : ((Ir β : ℝ) : ℂ) = -28 * Kc 1 β := by
  unfold Ir Kc circleIntegral
  rw [← intervalIntegral.integral_ofReal]
  simp only [deriv_circleMap, smul_eq_mul, circleMap_eq_yc, Fr_eq]
  rw [← mul_assoc, ← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro γ _
  simp only
  ring_nf; rw [I_sq]; ring

theorem Kc_periodic : Function.Periodic (Kc 1) (2 * Real.pi) := by
  intro β; unfold Kc; rw [yc_periodic]

theorem integral_Kc_two_pi : ∫ β in (0:ℝ)..(2 * Real.pi), Kc 1 β = -770 * Real.pi := by
  have h := Kc_periodic.intervalIntegral_add_eq (-βs) 0
  rw [zero_add] at h
  rw [← h, show -βs + 2 * Real.pi = 2 * Real.pi - βs by ring]
  exact integral_Kc_full

theorem continuous_Ir : Continuous Ir := by
  have : Ir = fun β => (-28 * Kc 1 β).re := by
    funext β; rw [← Ir_eq]; simp
  rw [this]
  exact Complex.continuous_re.comp (continuous_const.mul (continuous_Kc (by norm_num) le_rfl))

theorem integral_Ir_two_pi : ∫ β in (0:ℝ)..(2 * Real.pi), Ir β = 21560 * Real.pi := by
  have : ((∫ β in (0:ℝ)..(2 * Real.pi), Ir β : ℝ) : ℂ) = 21560 * Real.pi := by
    rw [← intervalIntegral.integral_ofReal]
    simp_rw [Ir_eq]
    rw [intervalIntegral.integral_const_mul, integral_Kc_two_pi]; ring
  exact_mod_cast this

/-! ### Even periodic functions -/

theorem integral_even_periodic {f : ℝ → ℝ} (hc : Continuous f) (heven : ∀ x, f (-x) = f x)
    (hper : Function.Periodic f (2 * Real.pi)) :
    ∫ x in (0:ℝ)..(2 * Real.pi), f x = 2 * ∫ x in (0:ℝ)..Real.pi, f x := by
  have h := hper.intervalIntegral_add_eq (-Real.pi) 0
  rw [zero_add] at h
  rw [← h, show -Real.pi + 2 * Real.pi = Real.pi by ring,
    ← intervalIntegral.integral_add_adjacent_intervals (b := 0)
      (hc.intervalIntegrable _ _) (hc.intervalIntegrable _ _)]
  have h2 : ∫ x in (-Real.pi)..(0:ℝ), f x = ∫ x in (0:ℝ)..Real.pi, f x := by
    have := intervalIntegral.integral_comp_neg (a := 0) (b := Real.pi) f
    rw [neg_zero] at this
    rw [← this]
    simp_rw [heven]
  rw [h2]; ring

theorem continuous_Fr (β : ℝ) : Continuous (fun γ => Fr β γ) := by
  unfold Fr
  apply Continuous.div
  · unfold pq; fun_prop
  · apply Continuous.pow
    apply Real.continuous_sqrt.comp
    unfold pq; fun_prop
  · intro γ
    exact pow_ne_zero _ (Real.sqrt_pos.mpr (one_sub_pq_pos β γ)).ne'

theorem Fr_even_right (β γ : ℝ) : Fr β (-γ) = Fr β γ := by
  unfold Fr pq; rw [Real.cos_neg]

theorem Fr_periodic_right (β : ℝ) : Function.Periodic (fun γ => Fr β γ) (2 * Real.pi) := by
  intro γ; simp only [Fr, pq, Real.cos_add_two_pi]

theorem Ir_even (β : ℝ) : Ir (-β) = Ir β := by
  unfold Ir; simp only [Fr, pq, Real.cos_neg]

theorem Ir_periodic : Function.Periodic Ir (2 * Real.pi) := by
  intro β; unfold Ir; simp only [Fr, pq, Real.cos_add_two_pi]

theorem Ir_eq_two_mul (β : ℝ) : Ir β = 2 * ∫ γ in (0:ℝ)..Real.pi, Fr β γ :=
  integral_even_periodic (continuous_Fr β) (Fr_even_right β) (Fr_periodic_right β)

theorem partB : ∫ β in (0:ℝ)..Real.pi, ∫ γ in (0:ℝ)..Real.pi, Fr β γ = 5390 * Real.pi := by
  have h1 := integral_Ir_two_pi
  rw [integral_even_periodic continuous_Ir Ir_even Ir_periodic] at h1
  simp_rw [Ir_eq_two_mul] at h1
  rw [intervalIntegral.integral_const_mul] at h1
  linarith

end Sun

end

/-! ## Section A1 -/

noncomputable section
namespace Sun
open Real

/-! ### Cosine moments -/

theorem integral_cos_pow_even_pi (n : ℕ) :
    ∫ x in (0:ℝ)..π, cos x ^ (2*n) = π * (Nat.centralBinom n : ℝ) / 4^n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show 2 * (n+1) = 2*n + 2 by ring, integral_cos_pow, ih]
    simp only [sin_pi, sin_zero, mul_zero, sub_zero, zero_div, zero_add]
    have h := Nat.succ_mul_centralBinom_succ n
    have h' : ((n:ℝ) + 1) * (Nat.centralBinom (n+1) : ℝ) = 2 * (2 * n + 1) * Nat.centralBinom n := by
      exact_mod_cast h
    have hn : ((n:ℝ) + 1) ≠ 0 := by positivity
    have h4 : (4:ℝ)^n ≠ 0 := by positivity
    push_cast
    field_simp
    linear_combination (-2 * 4^n) * h'

theorem integral_cos_pow_odd_pi (n : ℕ) :
    ∫ x in (0:ℝ)..π, cos x ^ (2*n+1) = 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show 2 * (n+1) + 1 = (2*n + 1) + 2 by ring, integral_cos_pow, ih]
    simp [sin_pi, sin_zero]

theorem sum_range_two_mul (h : ℕ → ℝ) (n : ℕ) :
    ∑ j ∈ Finset.range (2*n), h j = ∑ i ∈ Finset.range n, (h (2*i) + h (2*i+1)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show 2 * (n+1) = 2*n + 1 + 1 by ring, Finset.sum_range_succ, Finset.sum_range_succ, ih,
      Finset.sum_range_succ]
    ring

/-- Reindexing a sum whose odd terms vanish. -/
theorem sum_range_even (h : ℕ → ℝ) (k : ℕ) (hodd : ∀ i, h (2*i+1) = 0) :
    ∑ j ∈ Finset.range (k+1), h j = ∑ i ∈ Finset.range (k/2+1), h (2*i) := by
  have : ∑ j ∈ Finset.range (k+1), h j = ∑ j ∈ Finset.range (2*(k/2+1)), h j := by
    rcases Nat.even_or_odd k with ⟨m, hm⟩ | ⟨m, hm⟩
    · subst hm
      rw [show (m + m)/2 + 1 = m + 1 by omega, show 2 * (m+1) = (m + m + 1) + 1 by ring,
        Finset.sum_range_succ _ (m+m+1), show m + m + 1 = 2*m+1 by ring, hodd, add_zero]
    · subst hm
      rw [show (2*m+1)/2 + 1 = m + 1 by omega, show 2*m+1+1 = 2*(m+1) by ring]
  rw [this, sum_range_two_mul]
  simp only [hodd, add_zero]

end Sun

end

/-! ## Section A2 -/

noncomputable section
namespace Sun
open Real

theorem T_k_integral (k : ℕ) (b m : ℤ) :
    ((T_k k b (m^2) : ℚ) : ℝ) = (1/π) * ∫ θ in (0:ℝ)..π, ((b:ℝ) + 2 * m * cos θ)^k := by
  have hexp : ∀ θ : ℝ, ((b:ℝ) + 2 * m * cos θ)^k
      = ∑ j ∈ Finset.range (k+1), (2*m*cos θ)^j * (b:ℝ)^(k-j) * (k.choose j : ℝ) := by
    intro θ; rw [add_comm, add_pow]
  simp_rw [hexp]
  rw [intervalIntegral.integral_finset_sum (fun j _ => (by fun_prop : Continuous _).intervalIntegrable _ _)]
  have : ∀ j, ∫ θ in (0:ℝ)..π, (2*m*cos θ)^j * (b:ℝ)^(k-j) * (k.choose j : ℝ)
      = (2*m)^j * (b:ℝ)^(k-j) * (k.choose j) * ∫ θ in (0:ℝ)..π, cos θ ^ j := by
    intro j
    rw [← intervalIntegral.integral_const_mul]
    congr 1; funext θ; rw [mul_pow]; ring
  simp_rw [this]
  rw [Finset.mul_sum]
  set h : ℕ → ℝ := fun j => 1/π * ((2*m)^j * (b:ℝ)^(k-j) * (k.choose j) * ∫ θ in (0:ℝ)..π, cos θ ^ j)
    with hh
  rw [show ∑ j ∈ Finset.range (k+1), 1/π * ((2*m)^j * (b:ℝ)^(k-j) * (k.choose j) * ∫ θ in (0:ℝ)..π, cos θ ^ j) = ∑ j ∈ Finset.range (k+1), h j from rfl]
  rw [sum_range_even h k (fun i => by simp [hh, integral_cos_pow_odd_pi])]
  unfold T_k; push_cast
  apply Finset.sum_congr rfl
  intro i hi
  simp only [hh, integral_cos_pow_even_pi]
  have hi' : i ≤ 2*i := by omega
  have hc := Nat.choose_mul (n := k) (k := 2*i) (s := i) hi'
  rw [show 2*i - i = i by omega] at hc
  have hc' : (k.choose (2*i) : ℝ) * ((2*i).choose i) = k.choose i * (k-i).choose i := by exact_mod_cast hc
  rw [Nat.centralBinom_eq_two_mul_choose]
  have hpi : π ≠ 0 := pi_ne_zero
  have h4 : (4:ℝ)^i ≠ 0 := by positivity
  field_simp
  have e1 : ((m:ℝ) * 2)^(2*i) = 4^i * ((m:ℝ)^2)^i := by
    rw [mul_pow, ← pow_mul, show (2:ℝ)^(2*i) = 4^i by rw [pow_mul]; norm_num, mul_comm]
  rw [e1]
  linear_combination (-(b:ℝ)^(k-2*i) * ((m:ℝ)^2)^i * 4^i) * hc'

end Sun

namespace Sun
open Real

theorem centralBinom_integral (k : ℕ) :
    (((2*k).choose k : ℕ) : ℝ) = (1/π) * ∫ α in (0:ℝ)..π, (2 + 2 * cos α)^k := by
  have h1 : ∀ α : ℝ, (2 + 2 * cos α)^k = 4^k * cos (α/2) ^ (2*k) := by
    intro α
    rw [pow_mul, cos_sq, show 2 * (α/2) = α by ring, ← mul_pow]; ring
  simp_rw [h1]
  rw [intervalIntegral.integral_const_mul]
  have h2 : ∫ α in (0:ℝ)..π, cos (α/2) ^ (2*k) = 2 * ∫ u in (0:ℝ)..(π/2), cos u ^ (2*k) := by
    have := intervalIntegral.integral_comp_div (a := 0) (b := π) (c := 2) (fun u => cos u ^ (2*k)) two_ne_zero
    simp only [zero_div, smul_eq_mul] at this
    exact this
  have h3 : ∫ u in (0:ℝ)..(π/2), cos u ^ (2*k) = ∫ u in (π/2)..π, cos u ^ (2*k) := by
    have := intervalIntegral.integral_comp_sub_left (a := 0) (b := π/2) (fun u => cos u ^ (2*k)) π
    simp only [sub_zero, cos_pi_sub] at this
    rw [show π - π/2 = π/2 by ring] at this
    rw [← this]
    congr 1; funext u; rw [Even.neg_pow ⟨k, by ring⟩]
  have hc : Continuous (fun u : ℝ => cos u ^ (2*k)) := by fun_prop
  have h4 : ∫ u in (0:ℝ)..π, cos u ^ (2*k) = 2 * ∫ u in (0:ℝ)..(π/2), cos u ^ (2*k) := by
    rw [← intervalIntegral.integral_add_adjacent_intervals (b := π/2) (hc.intervalIntegrable _ _)
      (hc.intervalIntegrable _ _), ← h3]; ring
  rw [h2, ← h4, integral_cos_pow_even_pi, Nat.centralBinom_eq_two_mul_choose]
  have hpi : π ≠ 0 := pi_ne_zero
  have h4 : (4:ℝ)^k ≠ 0 := by positivity
  field_simp

end Sun

end

/-! ## Section A3 -/

noncomputable section
namespace Sun
open Real

theorem hasSum_series {X : ℝ} (h0 : 0 ≤ X) (h1 : X < 1) :
    HasSum (fun k : ℕ => (4290 * (k:ℝ) + 367) * X^k) ((367 + 3923 * X) / (1 - X)^2) := by
  have hn : ‖X‖ < 1 := by rw [Real.norm_eq_abs, abs_of_nonneg h0]; exact h1
  have h := ((hasSum_coe_mul_geometric_of_norm_lt_one hn).mul_left 4290).add
    ((hasSum_geometric_of_lt_one h0 h1).mul_left 367)
  have hX : (1 - X) ≠ 0 := by linarith
  convert h using 1
  · funext k; ring
  · field_simp; ring

/-- Derivative of the arctan part. -/
theorem hasDerivAt_arc {A B D : ℝ} (hB : 0 ≤ B) (hAB : B < A) (hD : 0 < D) (hD2 : D^2 = A^2 - B^2) (α : ℝ) :
    HasDerivAt (fun α => α + 2 * arctan (B * sin α / (A - B * cos α + D)))
      (D / (A - B * cos α)) α := by
  have hc := cos_le_one α
  have hc' := neg_one_le_cos α
  have hE : A - B * cos α + D ≠ 0 := by nlinarith
  have hA : A - B * cos α ≠ 0 := by nlinarith
  have hu : HasDerivAt (fun α => B * sin α / (A - B * cos α + D))
      ((B * cos α * (A - B * cos α + D) - B * sin α * (B * sin α)) / (A - B * cos α + D)^2) α := by
    have h1 : HasDerivAt (fun α => B * sin α) (B * cos α) α := (hasDerivAt_sin α).const_mul B
    have h2 : HasDerivAt (fun α => A - B * cos α + D) (B * sin α) α := by
      have := ((hasDerivAt_cos α).const_mul B).const_sub A
      have := this.add_const D
      convert this using 1; ring
    exact h1.div h2 hE
  have h := (hasDerivAt_id α).add ((hu.arctan).const_mul 2)
  have hsc := sin_sq_add_cos_sq α
  have hAD : A + D ≠ 0 := by linarith
  have hden : 1 + (B * sin α / (A - B * cos α + D)) ^ 2 ≠ 0 := by positivity
  convert h using 1
  field_simp
  linear_combination (A*B^2 - B^3*cos α + B^2*D) * hsc + (A - B*cos α + D) * hD2

theorem hasDerivAt_part2 {A B : ℝ} (hB : 0 ≤ B) (hAB : B < A) (α : ℝ) :
    HasDerivAt (fun α => B * sin α / (A - B * cos α))
      ((A * B * cos α - B^2) / (A - B * cos α)^2) α := by
  have hc := cos_le_one α
  have hA : A - B * cos α ≠ 0 := by nlinarith
  have h1 : HasDerivAt (fun α => B * sin α) (B * cos α) α := (hasDerivAt_sin α).const_mul B
  have h2 : HasDerivAt (fun α => A - B * cos α) (B * sin α) α := by
    have := ((hasDerivAt_cos α).const_mul B).const_sub A
    convert this using 1; ring
  have hsc := sin_sq_add_cos_sq α
  convert h1.div h2 hA using 1
  field_simp
  linear_combination B^2 * hsc

def Xa (p α : ℝ) : ℝ := p * (1 + cos α) / 2
def fa (p α : ℝ) : ℝ := (367 + 3923 * Xa p α) / (1 - Xa p α)^2

def Phi (p α : ℝ) : ℝ :=
  (-3923 + 4290 * (1 - p/2) / (1 - p)) *
    ((α + 2 * arctan ((p/2) * sin α / ((1 - p/2) - (p/2) * cos α + √(1 - p)))) / √(1 - p))
  + (4290 / (1 - p)) * ((p/2) * sin α / ((1 - p/2) - (p/2) * cos α))

theorem hasDerivAt_Phi {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p < 1) (α : ℝ) :
    HasDerivAt (Phi p) (fa p α) α := by
  have hD : 0 < √(1 - p) := Real.sqrt_pos.mpr (by linarith)
  have hD2 : (√(1 - p))^2 = (1 - p/2)^2 - (p/2)^2 := by
    rw [Real.sq_sqrt (by linarith)]; ring
  have hB : 0 ≤ p/2 := by linarith
  have hAB : p/2 < 1 - p/2 := by linarith
  have h1 := hasDerivAt_arc hB hAB hD hD2 α
  have h2 := hasDerivAt_part2 hB hAB α
  have h := ((h1.div_const (√(1 - p))).const_mul (-3923 + 4290 * (1 - p/2) / (1 - p))).add
    (h2.const_mul (4290 / (1 - p)))
  have hc := cos_le_one α
  have hA : (1 - p/2) - (p/2) * cos α ≠ 0 := by nlinarith
  have hp : (1 - p) ≠ 0 := by linarith
  convert h using 1
  unfold fa Xa
  have hX : 1 - p * (1 + cos α) / 2 ≠ 0 := by nlinarith
  field_simp
  ring

end Sun

namespace Sun
open Real

theorem continuous_fa {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p < 1) : Continuous (fa p) := by
  unfold fa Xa
  apply Continuous.div
  · fun_prop
  · fun_prop
  · intro α
    have hc := cos_le_one α
    have : 1 - p * (1 + cos α) / 2 ≠ 0 := by nlinarith
    exact pow_ne_zero _ this

theorem integral_fa {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p < 1) :
    ∫ α in (0:ℝ)..π, fa p α = π * (367 + 1778 * p) / (√(1 - p))^3 := by
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun α _ => hasDerivAt_Phi hp0 hp1 α)
    ((continuous_fa hp0 hp1).intervalIntegrable _ _)]
  have hD : 0 < √(1 - p) := Real.sqrt_pos.mpr (by linarith)
  have hD2 : (√(1 - p))^2 = 1 - p := Real.sq_sqrt (by linarith)
  have hp : (1 - p) ≠ 0 := by linarith
  unfold Phi
  simp only [sin_pi, sin_zero, mul_zero, zero_div, arctan_zero, add_zero, zero_add]
  field_simp
  rw [hD2]
  ring

theorem pq_nonneg (β γ : ℝ) : 0 ≤ pq β γ := by
  unfold pq
  have h1 := cos_bounds β
  have h2 := cos_bounds γ
  have : 0 ≤ (14 + 2 * Real.cos β) * (17 + 8 * Real.cos γ) := by
    apply mul_nonneg <;> linarith
  linarith

theorem pq_lt_one (β γ : ℝ) : pq β γ < 1 := by
  have := pq_le β γ; linarith

theorem Fr_eq_integral (β γ : ℝ) : Fr β γ = (1/π) * ∫ α in (0:ℝ)..π, fa (pq β γ) α := by
  rw [integral_fa (pq_nonneg β γ) (pq_lt_one β γ)]
  unfold Fr
  have hpi : π ≠ 0 := pi_ne_zero
  field_simp

end Sun

end

/-! ## Section A4 -/

noncomputable section
namespace Sun
open Real

/-- the geometric ratio bound -/
def rr : ℝ := 400/784

def F1 (p : ℝ) (k : ℕ) (α : ℝ) : ℝ := (4290 * (k:ℝ) + 367) * (Xa p α)^k
def I1 (p : ℝ) (k : ℕ) : ℝ := ∫ α in (0:ℝ)..π, F1 p k α
def bnd (k : ℕ) : ℝ := (4290 * (k:ℝ) + 367) * rr^k

theorem rr_nonneg : 0 ≤ rr := by unfold rr; norm_num
theorem rr_lt_one : rr < 1 := by unfold rr; norm_num

theorem summable_bnd : Summable bnd := (hasSum_series rr_nonneg rr_lt_one).summable

theorem Xa_nonneg {p : ℝ} (hp0 : 0 ≤ p) (α : ℝ) : 0 ≤ Xa p α := by
  unfold Xa; have := neg_one_le_cos α; have : 0 ≤ 1 + cos α := by linarith
  positivity

theorem Xa_le {p : ℝ} (hp0 : 0 ≤ p) (α : ℝ) : Xa p α ≤ p := by
  unfold Xa; have := cos_le_one α; nlinarith

theorem continuous_F1 (p : ℝ) (k : ℕ) : Continuous (F1 p k) := by
  unfold F1 Xa; fun_prop

theorem norm_F1_le {p : ℝ} (hp0 : 0 ≤ p) (hpr : p ≤ rr) (k : ℕ) (α : ℝ) : ‖F1 p k α‖ ≤ bnd k := by
  unfold F1 bnd
  rw [Real.norm_eq_abs, abs_of_nonneg (by have := Xa_nonneg hp0 α; positivity)]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact pow_le_pow_left₀ (Xa_nonneg hp0 α) ((Xa_le hp0 α).trans hpr) k

/-- Level 1: the α-integral. -/
theorem hasSum_I1 {p : ℝ} (hp0 : 0 ≤ p) (hpr : p ≤ rr) :
    HasSum (fun k => I1 p k) (∫ α in (0:ℝ)..π, fa p α) := by
  have hp1 : p < 1 := hpr.trans_lt rr_lt_one
  apply intervalIntegral.hasSum_integral_of_dominated_convergence (fun k _ => bnd k)
  · intro k; exact (continuous_F1 p k).aestronglyMeasurable
  · intro k
    exact Filter.Eventually.of_forall (fun α _ => norm_F1_le hp0 hpr k α)
  · exact Filter.Eventually.of_forall (fun α _ => summable_bnd)
  · exact intervalIntegrable_const
  · refine Filter.Eventually.of_forall (fun α _ => ?_)
    unfold F1 fa
    exact hasSum_series (Xa_nonneg hp0 α) ((Xa_le hp0 α).trans_lt hp1)

theorem norm_I1_le {p : ℝ} (hp0 : 0 ≤ p) (hpr : p ≤ rr) (k : ℕ) : ‖I1 p k‖ ≤ π * bnd k := by
  unfold I1
  have := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := π) (f := F1 p k) (C := bnd k)
    (fun α _ => norm_F1_le hp0 hpr k α)
  rw [sub_zero, abs_of_pos pi_pos] at this
  linarith

theorem I1_closed (p : ℝ) (k : ℕ) :
    I1 p k = π * (4290 * (k:ℝ) + 367) * ((2*k).choose k : ℝ) * (p/4)^k := by
  unfold I1 F1 Xa
  have : ∀ α : ℝ, (4290 * (k:ℝ) + 367) * (p * (1 + cos α) / 2)^k
      = ((4290 * (k:ℝ) + 367) * (p/4)^k) * (2 + 2 * cos α)^k := by
    intro α; rw [mul_assoc, ← mul_pow]; congr 2; ring
  simp_rw [this]
  rw [intervalIntegral.integral_const_mul, centralBinom_integral k]
  have hpi : π ≠ 0 := pi_ne_zero
  field_simp

end Sun

namespace Sun
open Real

theorem pq_le_rr (β γ : ℝ) : pq β γ ≤ rr := by unfold rr; exact pq_le β γ

def I2 (β : ℝ) (k : ℕ) : ℝ := ∫ γ in (0:ℝ)..π, I1 (pq β γ) k

theorem continuous_I1_pq (β : ℝ) (k : ℕ) : Continuous (fun γ => I1 (pq β γ) k) := by
  have : (fun γ => I1 (pq β γ) k)
      = fun γ => π * (4290 * (k:ℝ) + 367) * ((2*k).choose k : ℝ) * (pq β γ/4)^k :=
    funext (fun γ => I1_closed _ _)
  rw [this]; unfold pq; fun_prop

theorem hasSum_I2 (β : ℝ) :
    HasSum (fun k => I2 β k) (∫ γ in (0:ℝ)..π, ∫ α in (0:ℝ)..π, fa (pq β γ) α) := by
  apply intervalIntegral.hasSum_integral_of_dominated_convergence (fun k _ => π * bnd k)
  · intro k; exact (continuous_I1_pq β k).aestronglyMeasurable
  · intro k
    exact Filter.Eventually.of_forall (fun γ _ => norm_I1_le (pq_nonneg β γ) (pq_le_rr β γ) k)
  · exact Filter.Eventually.of_forall (fun γ _ => summable_bnd.mul_left π)
  · exact intervalIntegrable_const
  · exact Filter.Eventually.of_forall (fun γ _ => hasSum_I1 (pq_nonneg β γ) (pq_le_rr β γ))

theorem norm_I2_le (β : ℝ) (k : ℕ) : ‖I2 β k‖ ≤ π * (π * bnd k) := by
  unfold I2
  have := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := π)
    (f := fun γ => I1 (pq β γ) k) (C := π * bnd k)
    (fun γ _ => norm_I1_le (pq_nonneg β γ) (pq_le_rr β γ) k)
  rw [sub_zero, abs_of_pos pi_pos] at this
  linarith

theorem T2_integral (k : ℕ) :
    ∫ γ in (0:ℝ)..π, (17 + 8 * cos γ)^k = π * ((T_k k 17 16 : ℚ) : ℝ) := by
  have := T_k_integral k 17 4
  norm_num at this
  rw [this]; have hpi : π ≠ 0 := pi_ne_zero; field_simp

theorem T1_integral (k : ℕ) :
    ∫ β in (0:ℝ)..π, (14 + 2 * cos β)^k = π * ((T_k k 14 1 : ℚ) : ℝ) := by
  have := T_k_integral k 14 1
  norm_num at this
  rw [this]; have hpi : π ≠ 0 := pi_ne_zero; field_simp

theorem I2_closed (β : ℝ) (k : ℕ) :
    I2 β k = π^2 * (4290 * (k:ℝ) + 367) * ((2*k).choose k : ℝ) * ((14 + 2 * cos β)/3136)^k
      * ((T_k k 17 16 : ℚ) : ℝ) := by
  unfold I2
  simp_rw [I1_closed]
  have : ∀ γ : ℝ, π * (4290 * (k:ℝ) + 367) * ((2*k).choose k : ℝ) * (pq β γ/4)^k
      = (π * (4290 * (k:ℝ) + 367) * ((2*k).choose k : ℝ) * ((14 + 2 * cos β)/3136)^k)
        * (17 + 8 * cos γ)^k := by
    intro γ; unfold pq; rw [mul_assoc _ _ ((17 + 8 * cos γ)^k), ← mul_pow]; congr 2; ring
  simp_rw [this]
  rw [intervalIntegral.integral_const_mul, T2_integral]
  ring

def I3 (k : ℕ) : ℝ := ∫ β in (0:ℝ)..π, I2 β k

theorem continuous_I2 (k : ℕ) : Continuous (fun β => I2 β k) := by
  have : (fun β => I2 β k) = fun β => π^2 * (4290 * (k:ℝ) + 367) * ((2*k).choose k : ℝ)
      * ((14 + 2 * cos β)/3136)^k * ((T_k k 17 16 : ℚ) : ℝ) :=
    funext (fun β => I2_closed _ _)
  rw [this]; fun_prop

theorem hasSum_I3 :
    HasSum I3 (∫ β in (0:ℝ)..π, ∫ γ in (0:ℝ)..π, ∫ α in (0:ℝ)..π, fa (pq β γ) α) := by
  apply intervalIntegral.hasSum_integral_of_dominated_convergence (fun k _ => π * (π * bnd k))
  · intro k; exact (continuous_I2 k).aestronglyMeasurable
  · intro k
    exact Filter.Eventually.of_forall (fun β _ => norm_I2_le β k)
  · exact Filter.Eventually.of_forall (fun β _ => (summable_bnd.mul_left π).mul_left π)
  · exact intervalIntegrable_const
  · exact Filter.Eventually.of_forall (fun β _ => hasSum_I2 β)

theorem I3_eq (k : ℕ) : I3 k = π^3 * t k := by
  unfold I3
  simp_rw [I2_closed]
  have : ∀ β : ℝ, π^2 * (4290 * (k:ℝ) + 367) * ((2*k).choose k : ℝ) * ((14 + 2 * cos β)/3136)^k
      * ((T_k k 17 16 : ℚ) : ℝ)
      = (π^2 * (4290 * (k:ℝ) + 367) * ((2*k).choose k : ℝ) * (1/3136)^k * ((T_k k 17 16 : ℚ) : ℝ))
        * (14 + 2 * cos β)^k := by
    intro β; rw [div_eq_mul_one_div, mul_pow]; ring
  simp_rw [this]
  rw [intervalIntegral.integral_const_mul, T1_integral]
  unfold t
  simp only
  have h : (3136:ℝ)^k ≠ 0 := by positivity
  rw [one_div_pow]
  field_simp

theorem hasSum_t : HasSum t (5390 / π) := by
  have h := hasSum_I3
  have h2 : ∫ β in (0:ℝ)..π, ∫ γ in (0:ℝ)..π, ∫ α in (0:ℝ)..π, fa (pq β γ) α
      = π * (5390 * π) := by
    rw [← partB, ← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro β _
    simp only
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro γ _
    simp only
    rw [Fr_eq_integral]
    have hpi : π ≠ 0 := pi_ne_zero
    field_simp
  rw [h2] at h
  have h3 := h.mul_left (1/π^3)
  have hpi : π ≠ 0 := pi_ne_zero
  convert h3 using 1
  · funext k; rw [I3_eq]; field_simp
  · field_simp

theorem main_theorem : (∑' (k : ℕ), t k) = 5390 / Real.pi := hasSum_t.tsum_eq

end Sun

end

/--
Conjecture 2 (i): We have $\sum_{k \ge 0} t(k) = 5390/\pi$.

Denote (4290k+367)/3136^k*C(2k,k)*T_k(14,1)*T_k(17,16) by t(k).
(i) We have Sum_{k>=0}t(k) = 5390/Pi.
-/
theorem oeis_a336981_conjecture_2_i :
  (∑' (k : ℕ), t k) = 5390 / Real.pi := Sun.main_theorem

theorem oeis_a336981_conjecture_2_i.disproof : ¬ (type_of% @oeis_a336981_conjecture_2_i) := sorry
