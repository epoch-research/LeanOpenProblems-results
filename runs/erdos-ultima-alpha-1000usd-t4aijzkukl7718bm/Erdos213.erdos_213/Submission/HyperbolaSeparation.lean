import Submission.UnitEdge

/-! Quantitative separation along the hyperbolas determined by an integral
edge. This development does not assert a scale-independent cardinality bound. -/
namespace Erdos213.HyperbolaSeparation

lemma error_bounds {c d t y : ℝ} (hc : 0<c) (hc1 : c≤1) (hd : 0<d)
    (ht : d/2<t) (hy : 0<y) (h : y^2=c^2*(t^2-d^2/4)) :
    0<c*t-y ∧ c*t-y<d/2 := by
  have ht0 : 0<t := by linarith only [ht,hd]
  have hct : 0<c*t := mul_pos hc ht0
  have hdiff : (c*t)^2-y^2=c^2*d^2/4 := by nlinarith only [h]
  have hpos : 0<c^2*d^2/4 := by positivity
  have hlow : 0<c*t-y := by nlinarith only [hdiff,hpos,hct,hy]
  have ht' : 0<t-d/2 := sub_pos.mpr ht
  have hsmall : 0<c*(t-d/2) := mul_pos hc ht'
  have hdiff' : y^2-(c*(t-d/2))^2=c^2*d*(t-d/2) := by nlinarith only [h]
  have hpos' : 0<c^2*d*(t-d/2) := by positivity
  have hy' : c*(t-d/2)<y := by nlinarith only [hdiff',hpos',hsmall,hy]
  have hbound : c*d/2≤d/2 := by nlinarith only [hc1,hd]
  constructor
  · exact hlow
  · nlinarith only [hy',hbound]

lemma same_branch_dist_le {p q : ℂ} {b c d t u e f : ℝ}
    (hv : b^2+c^2=1)
    (hp : p.re=d/2+b*t) (hp' : p.im=c*t-e)
    (hq : q.re=d/2+b*u) (hq' : q.im=c*u-f) :
    dist p q ≤ |t-u|+|e-f| := by
  let v : ℂ := ⟨b,c⟩
  have hn : ‖v‖=1 := by
    have hh := Complex.sq_norm v
    simp only [Complex.normSq_apply,v] at hh
    nlinarith only [hh,hv,norm_nonneg v]
  have he : p-q=((t-u : ℝ) : ℂ)*v-((e-f : ℝ) : ℂ)*Complex.I := by
    apply Complex.ext
    · simp only [Complex.sub_re,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,
        Complex.I_re,Complex.I_im,v,hp,hq]
      ring
    · simp only [Complex.sub_im,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,
        Complex.I_re,Complex.I_im,v,hp',hq']
      ring
  rw [dist_eq_norm,he]
  calc ‖((t-u : ℝ) : ℂ)*v-((e-f : ℝ) : ℂ)*Complex.I‖
      ≤ ‖((t-u : ℝ) : ℂ)*v‖+‖((e-f : ℝ) : ℂ)*Complex.I‖ := norm_sub_le _ _
    _ = |t-u|+|e-f| := by
      rw [norm_mul,norm_mul,hn,Complex.norm_I]
      simp only [Complex.norm_real,Real.norm_eq_abs,mul_one]

lemma abs_sub_lt_one_of_floor_eq {e f : ℝ} (h : ⌊e⌋=⌊f⌋) : |e-f|<1 := by
  have he := Int.floor_le e
  have he' := Int.lt_floor_add_one e
  have hf := Int.floor_le f
  have hf' := Int.lt_floor_add_one f
  rw [h] at he he'
  exact abs_lt.mpr ⟨by linarith,by linarith⟩

lemma integer_reverse_triangle_gap {p q : ℂ} {r s k : ℤ}
    (hr : ‖p‖=(r : ℝ)) (hs : ‖q‖=(s : ℝ)) (hk : dist p q=(k : ℝ))
    (ht : ¬ Collinear ℝ ({0,p,q} : Set ℂ)) :
    |(r : ℝ)-(s : ℝ)|+1≤dist p q := by
  have h1 : dist 0 p < dist 0 q+dist q p := by
    apply dist_lt_dist_add_dist_iff.mpr
    intro h
    apply ht
    convert h.collinear using 1
    ext z
    simp only [Set.mem_insert_iff,Set.mem_singleton_iff]
    tauto
  have h2 : dist 0 q < dist 0 p+dist p q := by
    apply dist_lt_dist_add_dist_iff.mpr
    exact fun h => ht h.collinear
  rw [dist_zero_left,dist_zero_left,hr,hs,dist_comm q p,hk] at h1
  rw [dist_zero_left,dist_zero_left,hr,hs,hk] at h2
  have habs : |(r : ℝ)-(s : ℝ)|<(k : ℝ) := abs_lt.mpr ⟨by linarith,by linarith⟩
  have habs' : |r-s|<k := by exact_mod_cast habs
  have hgap : |r-s|+1≤k := by omega
  rw [hk]
  exact_mod_cast hgap

noncomputable def difference (d : ℝ) (p : ℂ) : ℝ := ‖p‖-dist p (d : ℂ)
noncomputable def beta (d : ℝ) (p : ℂ) : ℝ := difference d p/d
noncomputable def speed (d : ℝ) (p : ℂ) : ℝ := Real.sqrt (1-(beta d p)^2)
noncomputable def time (d : ℝ) (p : ℂ) : ℝ := ‖p‖-difference d p/2
noncomputable def error (d : ℝ) (p : ℂ) : ℝ := speed d p*time d p-|p.im|
noncomputable def folded (p : ℂ) : ℂ := ⟨p.re,|p.im|⟩

lemma profile {d : ℝ} (hd : 0<d) {p : ℂ}
    (ht : ¬ Collinear ℝ ({0,(d : ℂ),p} : Set ℂ)) :
    (-d<difference d p ∧ difference d p<d) ∧
    (beta d p)^2+(speed d p)^2=1 ∧
    p.re=d/2+beta d p*time d p ∧
    0<error d p ∧ error d p<d/2 := by
  have hdp : dist (0 : ℂ) (d : ℂ)=d := by
    simp only [dist_zero_left,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hd]
  have h1 : ‖p‖ < d+dist p (d : ℂ) := by
    have hh : dist (0 : ℂ) p < dist 0 (d : ℂ)+dist (d : ℂ) p := by
      apply dist_lt_dist_add_dist_iff.mpr
      exact fun h => ht h.collinear
    simpa only [dist_zero_left,hdp,dist_comm (d : ℂ) p] using hh
  have h2 : dist p (d : ℂ) < d+‖p‖ := by
    have hh : dist (d : ℂ) p < dist (d : ℂ) 0+dist 0 p := by
      apply dist_lt_dist_add_dist_iff.mpr
      intro h
      exact ht (by simpa only [Set.insert_comm] using h.collinear)
    simpa only [dist_zero_left,dist_comm (d : ℂ) 0,hdp,dist_comm (d : ℂ) p] using hh
  have h3 : d < ‖p‖+dist p (d : ℂ) := by
    have hh : dist (0 : ℂ) (d : ℂ) < dist 0 p+dist p (d : ℂ) := by
      apply dist_lt_dist_add_dist_iff.mpr
      intro h
      apply ht
      convert h.collinear using 1
      ext z
      simp only [Set.mem_insert_iff,Set.mem_singleton_iff]
      tauto
    simpa only [dist_zero_left,hdp] using hh
  have hdiff : -d<difference d p ∧ difference d p<d := by
    dsimp [difference]
    constructor <;> linarith only [h1,h2]
  have hb : -1<beta d p ∧ beta d p<1 := by
    dsimp [beta]
    constructor
    · apply (lt_div_iff₀ hd).mpr
      linarith only [hdiff.1]
    · apply (div_lt_iff₀ hd).mpr
      linarith only [hdiff.2]
  have hb2 : (beta d p)^2<1 := by nlinarith only [hb.1,hb.2]
  have hc : 0<speed d p := Real.sqrt_pos.mpr (by linarith only [hb2])
  have hc2 : (speed d p)^2=1-(beta d p)^2 := by
    exact Real.sq_sqrt (by linarith only [hb2])
  have hc1 : speed d p ≤ 1 := by nlinarith only [hc2,sq_nonneg (beta d p),hc]
  have htt : d/2<time d p := by dsimp [time,difference]; linarith only [h3]
  have hp : p.re^2+p.im^2=‖p‖^2 := by
    simpa only [Complex.normSq_apply,pow_two] using (Complex.sq_norm p).symm
  have hpd : (p.re-d)^2+p.im^2=dist p (d : ℂ)^2 := by
    have hh := (Complex.sq_norm (p-(d : ℂ))).symm
    simpa only [Complex.normSq_apply,Complex.sub_re,Complex.sub_im,Complex.ofReal_re,
      Complex.ofReal_im,sub_zero,pow_two,dist_eq_norm] using hh
  have hpre : p.re=d/2+beta d p*time d p := by
    dsimp [beta,time,difference]
    field_simp
    nlinarith only [hp,hpd]
  have hpy : p.im^2=(speed d p)^2*((time d p)^2-d^2/4) := by
    rw [hc2]
    have hdif : difference d p=beta d p*d := by
      dsimp [beta]
      field_simp
    have hnorm : ‖p‖=time d p+beta d p*d/2 := by
      dsimp [time]
      rw [← hdif]
      ring
    rw [hpre,hnorm] at hp
    nlinarith only [hp]
  have him : p.im ≠ 0 := by
    intro hz
    have hpos : 0<(speed d p)^2*((time d p)^2-d^2/4) := by
      apply mul_pos (sq_pos_of_pos hc)
      nlinarith only [htt,hd]
    rw [hz] at hpy
    nlinarith only [hpy,hpos]
  have he := error_bounds hc hc1 hd htt (abs_pos.mpr him)
    (by simpa only [sq_abs] using hpy)
  exact ⟨hdiff,by linarith only [hc2],hpre,he⟩

lemma folded_re (p : ℂ) : (folded p).re=p.re := rfl
lemma folded_im (p : ℂ) : (folded p).im=|p.im| := rfl

lemma folded_norm (p : ℂ) : ‖folded p‖=‖p‖ := by
  have hh := Complex.sq_norm p
  have hh' := Complex.sq_norm (folded p)
  simp only [Complex.normSq_apply,folded_re,folded_im,← pow_two,sq_abs] at hh hh'
  nlinarith only [hh,hh',norm_nonneg p,norm_nonneg (folded p)]

lemma folded_dist {p q : ℂ} (h : (0≤p.im) ↔ (0≤q.im)) :
    dist (folded p) (folded q)=dist p q := by
  have hh := Complex.sq_norm (p-q)
  have hh' := Complex.sq_norm (folded p-folded q)
  simp only [Complex.normSq_apply,Complex.sub_re,Complex.sub_im,folded_re,folded_im,← pow_two] at hh hh'
  by_cases hp : 0≤p.im
  · rw [abs_of_nonneg hp,abs_of_nonneg (h.mp hp)] at hh'
    simp only [dist_eq_norm]
    nlinarith only [hh,hh',norm_nonneg (p-q),norm_nonneg (folded p-folded q)]
  · have hq : q.im<0 := lt_of_not_ge (fun hh => hp (h.mpr hh))
    rw [abs_of_neg (lt_of_not_ge hp),abs_of_neg hq] at hh'
    simp only [dist_eq_norm]
    nlinarith only [hh,hh',norm_nonneg (p-q),norm_nonneg (folded p-folded q)]

lemma distinct_error_floors {d : ℝ} (hd : 0<d) {p q : ℂ} {r s k : ℤ}
    (hr : ‖p‖=(r : ℝ)) (hs : ‖q‖=(s : ℝ)) (hk : dist p q=(k : ℝ))
    (hpt : ¬ Collinear ℝ ({0,(d : ℂ),p} : Set ℂ))
    (hqt : ¬ Collinear ℝ ({0,(d : ℂ),q} : Set ℂ))
    (hpq : ¬ Collinear ℝ ({0,p,q} : Set ℂ))
    (hside : (0≤p.im) ↔ (0≤q.im)) (hdiff : difference d p=difference d q) :
    ⌊error d p⌋ ≠ ⌊error d q⌋ := by
  intro he
  have pp := profile hd hpt
  have pq := profile hd hqt
  have hb : beta d p=beta d q := by simp only [beta,hdiff]
  have hc : speed d p=speed d q := by simp only [speed,hb]
  have hpi : (folded p).im=speed d p*time d p-error d p := by
    dsimp [folded,error]
    ring
  have hqi : (folded q).im=speed d p*time d q-error d q := by
    dsimp [folded,error]
    rw [hc]
    ring
  have hqre : (folded q).re=d/2+beta d p*time d q := by
    rw [folded_re,hb]
    exact pq.2.2.1
  have hle := same_branch_dist_le (p := folded p) (q := folded q) pp.2.1 pp.2.2.1 hpi hqre hqi
  have htime : time d p-time d q=‖p‖-‖q‖ := by
    dsimp [time]
    rw [hdiff]
    ring
  rw [folded_dist hside,htime,hr,hs] at hle
  have hgap := integer_reverse_triangle_gap hr hs hk hpq
  have herr := abs_sub_lt_one_of_floor_eq he
  linarith only [hle,hgap,herr]

noncomputable def key (d : ℝ) (p : ℂ) : ℤ × Bool × ℤ := by
  classical
  exact (⌊difference d p⌋,(decide (0≤p.im),⌊error d p⌋))

lemma difference_floor_cast {d : ℝ} {p : ℂ}
    (hr : ‖p‖ ∈ Set.range ((↑) : ℤ → ℝ))
    (hs : dist p (d : ℂ) ∈ Set.range ((↑) : ℤ → ℝ)) :
    ((⌊difference d p⌋ : ℤ) : ℝ)=difference d p := by
  obtain ⟨r,hr⟩ := hr
  obtain ⟨s,hs⟩ := hs
  simp only [difference,← hr,← hs,← Int.cast_sub,Int.floor_intCast]

lemma key_injOn {d : ℝ} (hd : 0<d) {S : Set ℂ}
    (htri : EuclideanGeometry.NonTrilinear S)
    (hint : S.Pairwise (fun x y => dist x y ∈ Set.range ((↑) : ℤ → ℝ)))
    (h0 : 0 ∈ S) (hdS : (d : ℂ) ∈ S) :
    Set.InjOn (key d) (S \ {0,(d : ℂ)}) := by
  intro p hp q hq he
  have hp0 : p ≠ 0 := by intro h; exact hp.2 (by simp [h])
  have hpd : p ≠ (d : ℂ) := by intro h; exact hp.2 (by simp [h])
  have hq0 : q ≠ 0 := by intro h; exact hq.2 (by simp [h])
  have hqd : q ≠ (d : ℂ) := by intro h; exact hq.2 (by simp [h])
  have h0d : (0 : ℂ) ≠ (d : ℂ) := by
    intro h
    have hh := congrArg Complex.re h
    simp only [Complex.zero_re,Complex.ofReal_re] at hh
    linarith only [hh,hd]
  by_contra hpq
  have hpt := htri h0 hdS hp.1 h0d hpd.symm hp0.symm
  have hqt := htri h0 hdS hq.1 h0d hqd.symm hq0.symm
  have hpqt := htri h0 hp.1 hq.1 hp0.symm hpq hq0.symm
  have hpr : ‖p‖ ∈ Set.range ((↑) : ℤ → ℝ) := by
    simpa only [dist_zero_right] using hint hp.1 h0 hp0
  have hqr : ‖q‖ ∈ Set.range ((↑) : ℤ → ℝ) := by
    simpa only [dist_zero_right] using hint hq.1 h0 hq0
  have hpd' := hint hp.1 hdS hpd
  have hqd' := hint hq.1 hdS hqd
  have hkey1 : ⌊difference d p⌋=⌊difference d q⌋ := congrArg Prod.fst he
  have hkey2 : decide (0≤p.im)=decide (0≤q.im) := congrArg (fun z => z.2.1) he
  have hkey3 : ⌊error d p⌋=⌊error d q⌋ := congrArg (fun z => z.2.2) he
  have hside : (0≤p.im) ↔ (0≤q.im) := by
    by_cases hp' : 0≤p.im <;> by_cases hq' : 0≤q.im <;> simp [hp',hq'] at hkey2 ⊢
  have hdiff : difference d p=difference d q := by
    rw [← difference_floor_cast hpr hpd',← difference_floor_cast hqr hqd',hkey1]
  obtain ⟨r,hr⟩ := hpr
  obtain ⟨s,hs⟩ := hqr
  obtain ⟨k,hk⟩ := hint hp.1 hq.1 hpq
  exact distinct_error_floors hd hr.symm hs.symm hk.symm hpt hqt hpqt hside hdiff hkey3

def keyBox (d : ℕ) : Set (ℤ × Bool × ℤ) :=
  Set.Ico (-(d : ℤ)) (d : ℤ) ×ˢ (Set.univ ×ˢ Set.Ico (0 : ℤ) (d : ℤ))

lemma keyBox_finite (d : ℕ) : (keyBox d).Finite :=
  (Set.finite_Ico _ _).prod ((Set.finite_univ).prod (Set.finite_Ico _ _))

lemma keyBox_ncard (d : ℕ) : (keyBox d).ncard=4*d^2 := by
  have hi : (Set.Ico (-(d : ℤ)) (d : ℤ)).ncard=2*d := by
    rw [← Finset.coe_Ico,Set.ncard_coe_finset,Int.card_Ico]
    omega
  have hj : (Set.Ico (0 : ℤ) (d : ℤ)).ncard=d := by
    rw [← Finset.coe_Ico,Set.ncard_coe_finset,Int.card_Ico]
    omega
  simp only [keyBox,Set.ncard_prod,hi,hj,Set.ncard_univ,Nat.card_eq_fintype_card,
    Fintype.card_bool]
  ring

lemma key_mem_box {d : ℕ} (hd : 0<d) {p : ℂ}
    (ht : ¬ Collinear ℝ ({0,((d : ℝ) : ℂ),p} : Set ℂ)) :
    key (d : ℝ) p ∈ keyBox d := by
  have hdR : (0 : ℝ)<d := by exact_mod_cast hd
  have hh := profile hdR ht
  change (- (d : ℤ) ≤ ⌊difference (d : ℝ) p⌋ ∧ ⌊difference (d : ℝ) p⌋ < (d : ℤ)) ∧
    (True ∧ (0 ≤ ⌊error (d : ℝ) p⌋ ∧ ⌊error (d : ℝ) p⌋ < (d : ℤ)))
  refine ⟨⟨?_,?_⟩,⟨trivial,?_,?_⟩⟩
  · apply Int.le_floor.mpr
    push_cast
    exact hh.1.1.le
  · apply Int.floor_lt.mpr
    simpa only [Int.cast_natCast] using hh.1.2
  · apply Int.le_floor.mpr
    simpa only [Int.cast_zero] using hh.2.2.2.1.le
  · apply Int.floor_lt.mpr
    push_cast
    linarith only [hh.2.2.2.2,hdR]

/-- A uniform bound for nontrilinear integral-distance sets containing a fixed
integral edge. The bound depends on the edge length and is NOT a disproof of
unbounded cardinality when all edge lengths may grow. -/
theorem ncard_bound_normalized {d : ℕ} (hd : 0<d) {S : Set ℂ}
    (htri : EuclideanGeometry.NonTrilinear S)
    (hint : S.Pairwise (fun x y => dist x y ∈ Set.range ((↑) : ℤ → ℝ)))
    (h0 : 0 ∈ S) (hdS : ((d : ℝ) : ℂ) ∈ S) : S.ncard ≤ 4*d^2+2 := by
  have hdR : (0 : ℝ)<d := by exact_mod_cast hd
  have h0d : (0 : ℂ) ≠ ((d : ℝ) : ℂ) := by
    intro h
    have hh := congrArg Complex.re h
    simp only [Complex.zero_re,Complex.ofReal_re] at hh
    linarith only [hh,hdR]
  have hmap : ∀ p ∈ S \ {0,((d : ℝ) : ℂ)}, key (d : ℝ) p ∈ keyBox d := by
    intro p hp
    apply key_mem_box hd
    apply htri h0 hdS hp.1 h0d
    · intro h; exact hp.2 (by simp [← h])
    · intro h; exact hp.2 (by simp [← h])
  have hb := Set.ncard_le_ncard_of_injOn (key (d : ℝ)) hmap
    (key_injOn hdR htri hint h0 hdS) (keyBox_finite d)
  rw [keyBox_ncard] at hb
  have hh := Set.ncard_le_ncard_diff_add_ncard S {0,((d : ℝ) : ℂ)}
  rw [Set.ncard_pair h0d] at hh
  omega

theorem complex_ncard_bound {d : ℕ} (hd : 0<d) {S : Set ℂ}
    (htri : EuclideanGeometry.NonTrilinear S)
    (hint : S.Pairwise (fun x y => dist x y ∈ Set.range ((↑) : ℤ → ℝ)))
    {a b : ℂ} (ha : a ∈ S) (hb : b ∈ S) (hab : dist a b=(d : ℝ)) :
    S.ncard ≤ 4*d^2+2 := by
  have hdR : (0 : ℝ)<d := by exact_mod_cast hd
  have hdC : ((d : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt hdR)
  have hn : ‖b-a‖=(d : ℝ) := by simpa only [dist_eq_norm,norm_sub_rev] using hab
  let k : ℂ := (starRingEnd ℂ) (b-a)/((d : ℝ) : ℂ)
  have hkn : ‖k‖=1 := by
    simp only [k,norm_div,Complex.norm_conj,hn,Complex.norm_real,Real.norm_eq_abs,
      abs_of_pos hdR,div_self (ne_of_gt hdR)]
  have hk : k ≠ 0 := by intro h; simpa [h] using hkn
  let f : ℂ ≃ᵃ[ℝ] ℂ := (AffineEquiv.constVAdd ℝ ℂ (-a)).trans
    ((LinearEquiv.smulOfNeZero ℂ ℂ k hk).restrictScalars ℝ).toAffineEquiv
  have hfe (z : ℂ) : f z=k*(z-a) := by
    change k*(-a+z)=k*(z-a)
    ring
  have hf (z w : ℂ) : dist (f z) (f w)=dist z w := by
    simp only [hfe,dist_eq_norm,← mul_sub,sub_sub_sub_cancel_right,norm_mul,hkn,one_mul]
  have hfa : f a=0 := by rw [hfe]; simp
  have hfb : f b=((d : ℝ) : ℂ) := by
    rw [hfe]
    dsimp [k]
    rw [div_mul_eq_mul_div,Complex.conj_mul',hn]
    push_cast
    field_simp [show (d : ℂ) ≠ 0 by exact_mod_cast (ne_of_gt hd)]
  have hT := UnitEdge.nontrilinear_affine_image f htri
  have hI : (f '' S).Pairwise (fun x y => dist x y ∈ Set.range ((↑) : ℤ → ℝ)) := by
    rintro _ ⟨x,hx,rfl⟩ _ ⟨y,hy,rfl⟩ hxy
    rw [hf]
    exact hint hx hy (fun he => hxy (he ▸ rfl))
  have h0 : 0 ∈ f '' S := hfa ▸ Set.mem_image_of_mem f ha
  have hdS : ((d : ℝ) : ℂ) ∈ f '' S := hfb ▸ Set.mem_image_of_mem f hb
  have hh := ncard_bound_normalized hd hT hI h0 hdS
  rwa [Set.ncard_image_of_injective _ f.injective] at hh

/-- Every edge in any nontrilinear integral-distance configuration imposes
this cardinality bound. No special curve, symmetry, or no-four-cocircular
assumption is involved. The dependence on d is essential to the scope. -/
theorem plane_ncard_bound {d : ℕ} (hd : 0<d) {S : Set (EuclideanSpace ℝ (Fin 2))}
    (htri : EuclideanGeometry.NonTrilinear S)
    (hint : S.Pairwise (fun x y => dist x y ∈ Set.range ((↑) : ℤ → ℝ)))
    {a b : EuclideanSpace ℝ (Fin 2)} (ha : a ∈ S) (hb : b ∈ S)
    (hab : dist a b=(d : ℝ)) : S.ncard ≤ 4*d^2+2 := by
  let e : EuclideanSpace ℝ (Fin 2) ≃ₗᵢ[ℝ] ℂ := Complex.orthonormalBasisOneI.repr.symm
  have hT : EuclideanGeometry.NonTrilinear (e '' S) :=
    UnitEdge.nontrilinear_affine_image e.toLinearEquiv.toAffineEquiv htri
  have hI : (e '' S).Pairwise (fun x y => dist x y ∈ Set.range ((↑) : ℤ → ℝ)) := by
    rintro _ ⟨x,hx,rfl⟩ _ ⟨y,hy,rfl⟩ hxy
    rw [e.isometry.dist_eq]
    exact hint hx hy (fun he => hxy (he ▸ rfl))
  have hh := complex_ncard_bound hd hT hI
    (Set.mem_image_of_mem e ha) (Set.mem_image_of_mem e hb)
    ((e.isometry.dist_eq a b).trans hab)
  rwa [Set.ncard_image_of_injective _ e.injective] at hh

#print axioms error_bounds
#print axioms same_branch_dist_le
#print axioms integer_reverse_triangle_gap
#print axioms profile
#print axioms folded_dist
#print axioms distinct_error_floors
#print axioms key_injOn
#print axioms ncard_bound_normalized
#print axioms complex_ncard_bound
#print axioms plane_ncard_bound
end Erdos213.HyperbolaSeparation
