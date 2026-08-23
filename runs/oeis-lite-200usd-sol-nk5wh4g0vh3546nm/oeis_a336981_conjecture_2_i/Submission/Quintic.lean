import Submission.Cubic

open Set Filter MeasureTheory
namespace Elliptic
local notation "r3" => Real.sqrt 3
local notation "r5" => Real.sqrt 5
local notation "r15" => Real.sqrt 15

noncomputable def quinC : ℝ := -14*r5/5 - 8*r15/5 + 4*r3 + 7
noncomputable def quinA : ℝ := -1280 - 568*r5 + 328*r15 + 740*r3
noncomputable def quinN : ℝ := -23440*r3 - 10480*r15 + 18152*r5 + 40600
noncomputable def quinB : ℝ := -94 - 42*r5 + 24*r15 + 56*r3
noncomputable def quinQ : ℝ := -288*r15/5 - 128*r3 + 496*r5/5 + 224
noncomputable def quinS (t : ℝ) : ℝ :=
  quinC*t*(t^4+quinA*t^2+quinN)/(t^4+quinB*t^2+quinQ)
noncomputable def quinD (t : ℝ) : ℝ := quinC *
  (t^8+(3*quinB-quinA)*t^6+(quinA*quinB-3*quinN+5*quinQ)*t^4+
    (3*quinA*quinQ-quinB*quinN)*t^2+quinN*quinQ) /
  (t^4+quinB*t^2+quinQ)^2
noncomputable def quinMul : ℝ := (5-r5)/2
noncomputable def mm2c : ℝ := 1-mm2

lemma quin_constants_pos :
    0 < quinC ∧ 0 < quinA ∧ 0 < quinN ∧ 0 < quinB ∧ 0 < quinQ ∧
    0 < 3*quinB-quinA ∧ 0 < quinA*quinB-3*quinN+5*quinQ ∧
    0 < 3*quinA*quinQ-quinB*quinN := by
  rcases radical_bounds with ⟨h3l,h3u,h5l,h5u,h15l,h15u⟩
  have hc : 1 < quinC ∧ quinC < 2 := by
    dsimp [quinC]; constructor <;> linarith
  have ha : (19/10:ℝ) < quinA ∧ quinA < 2 := by
    dsimp [quinA]; constructor <;> linarith
  have hn : (9/10:ℝ) < quinN ∧ quinN < 1 := by
    dsimp [quinN]; constructor <;> linarith
  have hb : 2 < quinB ∧ quinB < 21/10 := by
    dsimp [quinB]; constructor <;> linarith
  have hq : 1 < quinQ ∧ quinQ < 11/10 := by
    dsimp [quinQ]; constructor <;> linarith
  have hcp : 0 < quinC := by linarith
  have hap : 0 < quinA := by linarith
  have hnp : 0 < quinN := by linarith
  have hbp : 0 < quinB := by linarith
  have hqp : 0 < quinQ := by linarith
  refine ⟨hcp, hap, hnp, hbp, hqp, ?_, ?_, ?_⟩
  · linarith
  · nlinarith [mul_pos hap hbp, mul_pos hnp hqp]
  · nlinarith [mul_pos hap hqp, mul_pos hbp hnp]

lemma quinS_deriv (t : ℝ) : HasDerivAt quinS (quinD t) t := by
  have hden : t^4+quinB*t^2+quinQ ≠ 0 := by
    rcases quin_constants_pos with ⟨hc,ha,hn,hb,hq,hs1,hs2,hs3⟩
    nlinarith [sq_nonneg t, sq_nonneg (t^2)]
  unfold quinS quinD
  convert ((((hasDerivAt_const t quinC).mul (hasDerivAt_id t)).mul
    ((((hasDerivAt_id t).pow 4).add
      ((hasDerivAt_const t quinA).mul ((hasDerivAt_id t).pow 2))).add_const quinN)).div
    ((((hasDerivAt_id t).pow 4).add
      ((hasDerivAt_const t quinB).mul ((hasDerivAt_id t).pow 2))).add_const quinQ) hden) using 1 <;>
    simp only [id_eq, Pi.mul_apply, Pi.add_apply, Pi.pow_apply] <;>
    field_simp [hden] <;> ring

lemma quinD_pos (t : ℝ) : 0 < quinD t := by
  rcases quin_constants_pos with ⟨hc,ha,hn,hb,hq,hs1,hs2,hs3⟩
  have hp : 0 < t^8+(3*quinB-quinA)*t^6+
      (quinA*quinB-3*quinN+5*quinQ)*t^4+
      (3*quinA*quinQ-quinB*quinN)*t^2+quinN*quinQ := by
    have hnq : 0 < quinN*quinQ := mul_pos hn hq
    nlinarith [sq_nonneg t, sq_nonneg (t^2), sq_nonneg (t^3), sq_nonneg (t^4)]
  dsimp [quinD]
  positivity

lemma quinS_strictMono : StrictMono quinS := by
  apply strictMono_of_deriv_pos
  intro t
  rw [(quinS_deriv t).deriv]
  exact quinD_pos t

lemma quinMul_pos : 0 < quinMul := by
  rcases radical_bounds with ⟨h3l,h3u,h5l,h5u,h15l,h15u⟩
  dsimp [quinMul]
  linarith

lemma radical_pow3 (n : ℕ) : r3^(n+2) = 3*r3^n := by
  rw [pow_add, radical_relations.1]
  ring
lemma radical_pow5 (n : ℕ) : r5^(n+2) = 5*r5^n := by
  rw [pow_add, radical_relations.2.1]
  ring

lemma rp32 : r3^2 = 3 := by
  exact radical_relations.1
lemma rp33 : r3^3 = 3*r3 := by
  rw [radical_pow3 1]
  simp
lemma rp34 : r3^4 = 9 := by
  rw [radical_pow3 2, rp32]
  ring
lemma rp35 : r3^5 = 9*r3 := by
  rw [radical_pow3 3, rp33]
  ring
lemma rp36 : r3^6 = 27 := by
  rw [radical_pow3 4, rp34]
  ring
lemma rp37 : r3^7 = 27*r3 := by
  rw [radical_pow3 5, rp35]
  ring
lemma rp38 : r3^8 = 81 := by
  rw [radical_pow3 6, rp36]
  ring
lemma rp39 : r3^9 = 81*r3 := by
  rw [radical_pow3 7, rp37]
  ring
lemma rp310 : r3^10 = 243 := by
  rw [radical_pow3 8, rp38]
  ring
lemma rp311 : r3^11 = 243*r3 := by
  rw [radical_pow3 9, rp39]
  ring
lemma rp312 : r3^12 = 729 := by
  rw [radical_pow3 10, rp310]
  ring
lemma rp313 : r3^13 = 729*r3 := by
  rw [radical_pow3 11, rp311]
  ring
lemma rp314 : r3^14 = 2187 := by
  rw [radical_pow3 12, rp312]
  ring
lemma rp315 : r3^15 = 2187*r3 := by
  rw [radical_pow3 13, rp313]
  ring
lemma rp316 : r3^16 = 6561 := by
  rw [radical_pow3 14, rp314]
  ring
lemma rp317 : r3^17 = 6561*r3 := by
  rw [radical_pow3 15, rp315]
  ring
lemma rp318 : r3^18 = 19683 := by
  rw [radical_pow3 16, rp316]
  ring
lemma rp319 : r3^19 = 19683*r3 := by
  rw [radical_pow3 17, rp317]
  ring
lemma rp320 : r3^20 = 59049 := by
  rw [radical_pow3 18, rp318]
  ring
lemma rp52 : r5^2 = 5 := by
  exact radical_relations.2.1
lemma rp53 : r5^3 = 5*r5 := by
  rw [radical_pow5 1]
  simp
lemma rp54 : r5^4 = 25 := by
  rw [radical_pow5 2, rp52]
  ring
lemma rp55 : r5^5 = 25*r5 := by
  rw [radical_pow5 3, rp53]
  ring
lemma rp56 : r5^6 = 125 := by
  rw [radical_pow5 4, rp54]
  ring
lemma rp57 : r5^7 = 125*r5 := by
  rw [radical_pow5 5, rp55]
  ring
lemma rp58 : r5^8 = 625 := by
  rw [radical_pow5 6, rp56]
  ring
lemma rp59 : r5^9 = 625*r5 := by
  rw [radical_pow5 7, rp57]
  ring
lemma rp510 : r5^10 = 3125 := by
  rw [radical_pow5 8, rp58]
  ring
lemma rp511 : r5^11 = 3125*r5 := by
  rw [radical_pow5 9, rp59]
  ring
lemma rp512 : r5^12 = 15625 := by
  rw [radical_pow5 10, rp510]
  ring
lemma rp513 : r5^13 = 15625*r5 := by
  rw [radical_pow5 11, rp511]
  ring
lemma rp514 : r5^14 = 78125 := by
  rw [radical_pow5 12, rp512]
  ring
lemma rp515 : r5^15 = 78125*r5 := by
  rw [radical_pow5 13, rp513]
  ring
lemma rp516 : r5^16 = 390625 := by
  rw [radical_pow5 14, rp514]
  ring
lemma rp517 : r5^17 = 390625*r5 := by
  rw [radical_pow5 15, rp515]
  ring
lemma rp518 : r5^18 = 1953125 := by
  rw [radical_pow5 16, rp516]
  ring
lemma rp519 : r5^19 = 1953125*r5 := by
  rw [radical_pow5 17, rp517]
  ring
lemma rp520 : r5^20 = 9765625 := by
  rw [radical_pow5 18, rp518]
  ring


set_option maxRecDepth 10000
set_option maxHeartbeats 30000000

lemma quinC_minpoly : 25*quinC^4-700*quinC^3+1070*quinC^2-140*quinC+1 = 0 := by
  rcases radical_relations with ⟨h3,h5,h15⟩
  dsimp [quinC]
  rw [h15]
  ring_nf
  simp only [rp34, rp33, rp32, rp54, rp53, rp52]
  ring

lemma quinA_rep : quinA = 90175/88*quinC^3-2524275/88*quinC^2+3841985/88*quinC-477965/88 := by
  rcases radical_relations with ⟨h3,h5,h15⟩
  dsimp [quinA, quinC]
  rw [h15]
  ring_nf
  simp only [rp33, rp32, rp53, rp52]
  ring
lemma quinN_rep : quinN = -360350/11*quinC^3+10087075/11*quinC^2-15346700/11*quinC+1901895/11 := by
  rcases radical_relations with ⟨h3,h5,h15⟩
  dsimp [quinN, quinC]
  rw [h15]
  ring_nf
  simp only [rp33, rp32, rp53, rp52]
  ring
lemma quinB_rep : quinB = 6625/88*quinC^3-185465/88*quinC^2+282575/88*quinC-35383/88 := by
  rcases radical_relations with ⟨h3,h5,h15⟩
  dsimp [quinB, quinC]
  rw [h15]
  ring_nf
  simp only [rp33, rp32, rp53, rp52]
  ring
lemma quinQ_rep : quinQ = -1975/11*quinC^3+55285/11*quinC^2-84109/11*quinC+10431/11 := by
  rcases radical_relations with ⟨h3,h5,h15⟩
  dsimp [quinQ, quinC]
  rw [h15]
  ring_nf
  simp only [rp33, rp32, rp53, rp52]
  ring
lemma quinMul_rep : quinMul = 175/352*quinC^3-4875/352*quinC^2+6825/352*quinC+435/352 := by
  rcases radical_relations with ⟨h3,h5,h15⟩
  dsimp [quinMul, quinC]
  rw [h15]
  ring_nf
  simp only [rp33, rp32, rp53, rp52]
  ring
lemma mm1_rep : mm1 = -375/11264*quinC^3+10745/11264*quinC^2-22765/11264*quinC+11435/11264 := by
  rcases radical_relations with ⟨h3,h5,h15⟩
  dsimp [mm1, quinC]
  rw [h15]
  ring_nf
  simp only [rp33, rp32, rp53, rp52]
  ring
lemma mm2c_rep : mm2c = -725/11264*quinC^3+20055/11264*quinC^2-24095/11264*quinC+2909/11264 := by
  rcases radical_relations with ⟨h3,h5,h15⟩
  dsimp [mm2c, mm2, quinC]
  rw [h15]
  ring_nf
  simp only [rp33, rp32, rp53, rp52]
  ring

lemma quin_hc0 : quinC^2*quinN^2*quinQ^2 - quinQ^4*quinMul^2 = 0 := by
  simp only [quinA_rep, quinN_rep, quinB_rep, quinQ_rep, quinMul_rep, mm1_rep, mm2c_rep]
  linear_combination (-25*(2765*quinC^2 - 77004*quinC - 907497)*(1975*quinC^3 - 55285*quinC^2 + 84109*quinC - 10431)^2*(69125*quinC^6 - 3860600*quinC^5 + 84911205*quinC^4 - 867793640*quinC^3 + 1200576895*quinC^2 - 140814240*quinC - 907497)/1814078464) * quinC_minpoly
lemma quin_hc1 : 6*quinA*quinC^2*quinN*quinQ^2 - 2*quinB*quinC^2*quinN^2*quinQ - 4*quinB*quinQ^3*quinMul^2 - quinC^2*quinN^2*quinQ^2*mm1 + quinC^2*quinN^2*quinQ^2*mm2c*quinMul^2 - 2*quinC^2*quinN^2*quinQ^2*quinMul^2 + 2*quinC^2*quinN^2*quinQ^2 = 0 := by
  simp only [quinA_rep, quinN_rep, quinB_rep, quinQ_rep, quinMul_rep, mm1_rep, mm2c_rep]
  linear_combination (-25*(1975*quinC^3 - 55285*quinC^2 + 84109*quinC - 10431)*(9110668387329687500*quinC^16 - 1269604762140227187500*quinC^15 + 72556783918608561046875*quinC^14 - 2171431447522923948175000*quinC^13 + 35932511777339642563481250*quinC^12 - 318693305231129008047182500*quinC^11 + 1389648962493531909177388125*quinC^10 - 3133993494103900746018634000*quinC^9 + 3518087505942839177217406200*quinC^8 - 1275595587400164719527118580*quinC^7 - 890521357071016869227197435*quinC^6 + 770142660220314679264716200*quinC^5 - 77004734673911699415842374*quinC^4 - 10080667000782850371346236*quinC^3 + 1015683641054653750706979*quinC^2 + 24168591661013113425408*quinC + 164114779888623573504)/20433779818496) * quinC_minpoly
lemma quin_hc2 : 9*quinA^2*quinC^2*quinQ^2 - 4*quinA*quinB*quinC^2*quinN*quinQ - 6*quinA*quinC^2*quinN*quinQ^2*mm1 + 2*quinA*quinC^2*quinN*quinQ^2*mm2c*quinMul^2 - 4*quinA*quinC^2*quinN*quinQ^2*quinMul^2 + 12*quinA*quinC^2*quinN*quinQ^2 + quinB^2*quinC^2*quinN^2 - 6*quinB^2*quinQ^2*quinMul^2 + 2*quinB*quinC^2*quinN^2*quinQ*mm1 + 2*quinB*quinC^2*quinN^2*quinQ*mm2c*quinMul^2 - 4*quinB*quinC^2*quinN^2*quinQ*quinMul^2 - 4*quinB*quinC^2*quinN^2*quinQ + quinC^4*quinN^4*mm2c*quinMul^2 - quinC^4*quinN^4*quinMul^2 - quinC^2*quinN^2*quinQ^2*mm1 + quinC^2*quinN^2*quinQ^2 - 6*quinC^2*quinN^2*quinQ + 10*quinC^2*quinN*quinQ^2 - 4*quinQ^3*quinMul^2 = 0 := by
  simp only [quinA_rep, quinN_rep, quinB_rep, quinQ_rep, quinMul_rep, mm1_rep, mm2c_rep]
  linear_combination (-25*(2396029625292986388125000000*quinC^21 - 400966228396578508892375000000*quinC^20 + 28530432302138334532234878906250*quinC^19 - 1119486212534149253020196605859375*quinC^18 + 26255214794444317064925917590234375*quinC^17 - 373061615682036681846555910623359375*quinC^16 + 3126072743469324731851254754491046875*quinC^15 - 14823831073925709850142279336279884375*quinC^14 + 41359520272083448984942594449982096875*quinC^13 - 69463732624832759668249765315180311875*quinC^12 + 68455750948871907392453115473250731875*quinC^11 - 34707912998158261876518838075949096625*quinC^10 + 4051128797489859613707447909715448325*quinC^9 + 3153449912588126442261443009556473475*quinC^8 - 815395671993540333318516373575508495*quinC^7 + 15483930376632467889507661498260659*quinC^6 + 7853374275632869699065945034202633*quinC^5 - 193215179965407165835303772703537*quinC^4 - 27009777808726619957458370398713*quinC^3 - 201082693428725016451606492860*quinC^2 + 609093581174228051950853376*quinC + 4372185217214146234826880)/81735119273984) * quinC_minpoly
lemma quin_hc3 : 6*quinA^2*quinB*quinC^2*quinQ - 9*quinA^2*quinC^2*quinQ^2*mm1 + quinA^2*quinC^2*quinQ^2*mm2c*quinMul^2 - 2*quinA^2*quinC^2*quinQ^2*quinMul^2 + 18*quinA^2*quinC^2*quinQ^2 - 2*quinA*quinB^2*quinC^2*quinN + 4*quinA*quinB*quinC^2*quinN*quinQ*mm1 + 4*quinA*quinB*quinC^2*quinN*quinQ*mm2c*quinMul^2 - 8*quinA*quinB*quinC^2*quinN*quinQ*quinMul^2 - 8*quinA*quinB*quinC^2*quinN*quinQ + 4*quinA*quinC^4*quinN^3*mm2c*quinMul^2 - 4*quinA*quinC^4*quinN^3*quinMul^2 - 6*quinA*quinC^2*quinN*quinQ^2*mm1 + 6*quinA*quinC^2*quinN*quinQ^2 - 20*quinA*quinC^2*quinN*quinQ + 30*quinA*quinC^2*quinQ^2 - 4*quinB^3*quinQ*quinMul^2 - quinB^2*quinC^2*quinN^2*mm1 + quinB^2*quinC^2*quinN^2*mm2c*quinMul^2 - 2*quinB^2*quinC^2*quinN^2*quinMul^2 + 2*quinB^2*quinC^2*quinN^2 + 2*quinB*quinC^2*quinN^2*quinQ*mm1 - 2*quinB*quinC^2*quinN^2*quinQ + 6*quinB*quinC^2*quinN^2 - 4*quinB*quinC^2*quinN*quinQ - 12*quinB*quinQ^2*quinMul^2 + 6*quinC^2*quinN^2*quinQ*mm1 + 2*quinC^2*quinN^2*quinQ*mm2c*quinMul^2 - 4*quinC^2*quinN^2*quinQ*quinMul^2 - 12*quinC^2*quinN^2*quinQ - 10*quinC^2*quinN*quinQ^2*mm1 + 2*quinC^2*quinN*quinQ^2*mm2c*quinMul^2 - 4*quinC^2*quinN*quinQ^2*quinMul^2 + 20*quinC^2*quinN*quinQ^2 = 0 := by
  simp only [quinA_rep, quinN_rep, quinB_rep, quinQ_rep, quinMul_rep, mm1_rep, mm2c_rep]
  linear_combination (5*(23983568359738592762500000000*quinC^21 - 4013571917051773677203750000000*quinC^20 + 285583962650122148082748310546875*quinC^19 - 11205915113319867257676649732421875*quinC^18 + 262814188303860126932606688052734375*quinC^17 - 3734403719236573806572176549078515625*quinC^16 + 31293404026508737826509412538318671875*quinC^15 - 148401413372549032642300827826484203125*quinC^14 + 414085308775943917162342434184371671875*quinC^13 - 695549304833986709870920536379480378125*quinC^12 + 685598846912537344203107929187983298125*quinC^11 - 347754318157171328330518023242699364375*quinC^10 + 40690958881410460141783279939463651125*quinC^9 + 31567163958036567096635849619261056325*quinC^8 - 8176678320291639202027784891782900575*quinC^7 + 154091478284618273831321726436496265*quinC^6 + 79434549651472274852654461986723105*quinC^5 - 1967656371255728664847018973922255*quinC^4 - 276950222217413103038812596416236*quinC^3 - 1733251331754830714892496114506*quinC^2 + 13980180729649858531143874560*quinC + 100220539586564789992005120)/1307761908383744) * quinC_minpoly
lemma quin_hc4 : quinA^2*quinB^2*quinC^2 - 6*quinA^2*quinB*quinC^2*quinQ*mm1 + 2*quinA^2*quinB*quinC^2*quinQ*mm2c*quinMul^2 - 4*quinA^2*quinB*quinC^2*quinQ*quinMul^2 + 12*quinA^2*quinB*quinC^2*quinQ + 6*quinA^2*quinC^4*quinN^2*mm2c*quinMul^2 - 6*quinA^2*quinC^4*quinN^2*quinMul^2 - 9*quinA^2*quinC^2*quinQ^2*mm1 + 9*quinA^2*quinC^2*quinQ^2 - 6*quinA^2*quinC^2*quinQ + 2*quinA*quinB^2*quinC^2*quinN*mm1 + 2*quinA*quinB^2*quinC^2*quinN*mm2c*quinMul^2 - 4*quinA*quinB^2*quinC^2*quinN*quinMul^2 - 4*quinA*quinB^2*quinC^2*quinN + 4*quinA*quinB*quinC^2*quinN*quinQ*mm1 - 4*quinA*quinB*quinC^2*quinN*quinQ - 4*quinA*quinB*quinC^2*quinN + 28*quinA*quinB*quinC^2*quinQ + 20*quinA*quinC^2*quinN*quinQ*mm1 + 4*quinA*quinC^2*quinN*quinQ*mm2c*quinMul^2 - 8*quinA*quinC^2*quinN*quinQ*quinMul^2 - 40*quinA*quinC^2*quinN*quinQ - 30*quinA*quinC^2*quinQ^2*mm1 + 2*quinA*quinC^2*quinQ^2*mm2c*quinMul^2 - 4*quinA*quinC^2*quinQ^2*quinMul^2 + 60*quinA*quinC^2*quinQ^2 - quinB^4*quinMul^2 - quinB^2*quinC^2*quinN^2*mm1 + quinB^2*quinC^2*quinN^2 - 6*quinB^2*quinC^2*quinN - 12*quinB^2*quinQ*quinMul^2 - 6*quinB*quinC^2*quinN^2*mm1 + 2*quinB*quinC^2*quinN^2*mm2c*quinMul^2 - 4*quinB*quinC^2*quinN^2*quinMul^2 + 12*quinB*quinC^2*quinN^2 + 4*quinB*quinC^2*quinN*quinQ*mm1 + 4*quinB*quinC^2*quinN*quinQ*mm2c*quinMul^2 - 8*quinB*quinC^2*quinN*quinQ*quinMul^2 - 8*quinB*quinC^2*quinN*quinQ + 4*quinC^4*quinN^3*mm2c*quinMul^2 - 4*quinC^4*quinN^3*quinMul^2 + 6*quinC^2*quinN^2*quinQ*mm1 - 6*quinC^2*quinN^2*quinQ + 9*quinC^2*quinN^2 - 10*quinC^2*quinN*quinQ^2*mm1 + 10*quinC^2*quinN*quinQ^2 - 28*quinC^2*quinN*quinQ + 25*quinC^2*quinQ^2 - 6*quinQ^2*quinMul^2 = 0 := by
  simp only [quinA_rep, quinN_rep, quinB_rep, quinQ_rep, quinMul_rep, mm1_rep, mm2c_rep]
  linear_combination (-5*(4501286825668296660937500000*quinC^21 - 753278505408738968085000000000*quinC^20 + 53599476917684075801244990234375*quinC^19 - 2103183675516551859421783082031250*quinC^18 + 49326856151195167555916768903906250*quinC^17 - 700912378771720377445364368692968750*quinC^16 + 5873669933722261708299967640911093750*quinC^15 - 27856265392658937595206596712308593750*quinC^14 + 77736411753511255753765264923571781250*quinC^13 - 130601757814809899517293131807995043750*quinC^12 + 128780669828551217982146906222695042500*quinC^11 - 65375563572039795201319724725690621250*quinC^10 + 7690543653167311836010373531708538750*quinC^9 + 5921958392819486898088882036042391350*quinC^8 - 1541061762841121085852996544120037350*quinC^7 + 29731565518483658773659104054336110*quinC^6 + 14947381235131443845566597503989590*quinC^5 - 362349885970681001763245821464738*quinC^4 - 53937777983510087066341539468251*quinC^3 - 309364397644963210952904692164*quinC^2 + 6257210713850079717909563520*quinC + 44707895405121123349225920)/5231047633534976) * quinC_minpoly
lemma quin_hc5 : 4*quinA^3*quinC^4*quinN*mm2c*quinMul^2 - 4*quinA^3*quinC^4*quinN*quinMul^2 - quinA^2*quinB^2*quinC^2*mm1 + quinA^2*quinB^2*quinC^2*mm2c*quinMul^2 - 2*quinA^2*quinB^2*quinC^2*quinMul^2 + 2*quinA^2*quinB^2*quinC^2 - 6*quinA^2*quinB*quinC^2*quinQ*mm1 + 6*quinA^2*quinB*quinC^2*quinQ - 2*quinA^2*quinB*quinC^2 + 6*quinA^2*quinC^2*quinQ*mm1 + 2*quinA^2*quinC^2*quinQ*mm2c*quinMul^2 - 4*quinA^2*quinC^2*quinQ*quinMul^2 - 12*quinA^2*quinC^2*quinQ + 2*quinA*quinB^2*quinC^2*quinN*mm1 - 2*quinA*quinB^2*quinC^2*quinN + 6*quinA*quinB^2*quinC^2 + 4*quinA*quinB*quinC^2*quinN*mm1 + 4*quinA*quinB*quinC^2*quinN*mm2c*quinMul^2 - 8*quinA*quinB*quinC^2*quinN*quinMul^2 - 8*quinA*quinB*quinC^2*quinN - 28*quinA*quinB*quinC^2*quinQ*mm1 + 4*quinA*quinB*quinC^2*quinQ*mm2c*quinMul^2 - 8*quinA*quinB*quinC^2*quinQ*quinMul^2 + 56*quinA*quinB*quinC^2*quinQ + 12*quinA*quinC^4*quinN^2*mm2c*quinMul^2 - 12*quinA*quinC^4*quinN^2*quinMul^2 + 20*quinA*quinC^2*quinN*quinQ*mm1 - 20*quinA*quinC^2*quinN*quinQ + 6*quinA*quinC^2*quinN - 30*quinA*quinC^2*quinQ^2*mm1 + 30*quinA*quinC^2*quinQ^2 - 4*quinA*quinC^2*quinQ - 4*quinB^3*quinMul^2 + 6*quinB^2*quinC^2*quinN*mm1 + 2*quinB^2*quinC^2*quinN*mm2c*quinMul^2 - 4*quinB^2*quinC^2*quinN*quinMul^2 - 12*quinB^2*quinC^2*quinN - 6*quinB*quinC^2*quinN^2*mm1 + 6*quinB*quinC^2*quinN^2 + 4*quinB*quinC^2*quinN*quinQ*mm1 - 4*quinB*quinC^2*quinN*quinQ - 20*quinB*quinC^2*quinN + 30*quinB*quinC^2*quinQ - 12*quinB*quinQ*quinMul^2 - 9*quinC^2*quinN^2*mm1 + quinC^2*quinN^2*mm2c*quinMul^2 - 2*quinC^2*quinN^2*quinMul^2 + 18*quinC^2*quinN^2 + 28*quinC^2*quinN*quinQ*mm1 + 4*quinC^2*quinN*quinQ*mm2c*quinMul^2 - 8*quinC^2*quinN*quinQ*quinMul^2 - 56*quinC^2*quinN*quinQ - 25*quinC^2*quinQ^2*mm1 + quinC^2*quinQ^2*mm2c*quinMul^2 - 2*quinC^2*quinQ^2*quinMul^2 + 50*quinC^2*quinQ^2 = 0 := by
  simp only [quinA_rep, quinN_rep, quinB_rep, quinQ_rep, quinMul_rep, mm1_rep, mm2c_rep]
  linear_combination (5*(1501886275397580690625000000*quinC^21 - 251337663941694972729062500000*quinC^20 + 17884004128273145209661552734375*quinC^19 - 701753522534430085686860169921875*quinC^18 + 16458711671504820043985793317187500*quinC^17 - 233875566222771981254250653001562500*quinC^16 + 1959963356744163502633077904826875000*quinC^15 - 9296080369557355103241498727935000000*quinC^14 + 25946765088775752962639879602738687500*quinC^13 - 43608344944918469637028732468449762500*quinC^12 + 43032653273294065072267176493739668750*quinC^11 - 21885285833506029240527472685491728750*quinC^10 + 2605576316011939036131338220323094500*quinC^9 + 1972631926349852494566210058382126100*quinC^8 - 518871253517985424854221192896389600*quinC^7 + 10528303737911106862929341709229480*quinC^6 + 5092487207543253025565330333058980*quinC^5 - 142078478102725055429441850121900*quinC^4 - 16637193944556155694780061669325*quinC^3 - 148475917512118135404075694503*quinC^2 + 998078833773931260780380160*quinC + 6763997686601630922670080)/83696762136559616) * quinC_minpoly
lemma quin_hc6 : quinA^4*quinC^4*mm2c*quinMul^2 - quinA^4*quinC^4*quinMul^2 - quinA^2*quinB^2*quinC^2*mm1 + quinA^2*quinB^2*quinC^2 + 2*quinA^2*quinB*quinC^2*mm1 + 2*quinA^2*quinB*quinC^2*mm2c*quinMul^2 - 4*quinA^2*quinB*quinC^2*quinMul^2 - 4*quinA^2*quinB*quinC^2 + 12*quinA^2*quinC^4*quinN*mm2c*quinMul^2 - 12*quinA^2*quinC^4*quinN*quinMul^2 + 6*quinA^2*quinC^2*quinQ*mm1 - 6*quinA^2*quinC^2*quinQ + quinA^2*quinC^2 - 6*quinA*quinB^2*quinC^2*mm1 + 2*quinA*quinB^2*quinC^2*mm2c*quinMul^2 - 4*quinA*quinB^2*quinC^2*quinMul^2 + 12*quinA*quinB^2*quinC^2 + 4*quinA*quinB*quinC^2*quinN*mm1 - 4*quinA*quinB*quinC^2*quinN - 28*quinA*quinB*quinC^2*quinQ*mm1 + 28*quinA*quinB*quinC^2*quinQ - 4*quinA*quinB*quinC^2 - 6*quinA*quinC^2*quinN*mm1 + 2*quinA*quinC^2*quinN*mm2c*quinMul^2 - 4*quinA*quinC^2*quinN*quinMul^2 + 12*quinA*quinC^2*quinN + 4*quinA*quinC^2*quinQ*mm1 + 4*quinA*quinC^2*quinQ*mm2c*quinMul^2 - 8*quinA*quinC^2*quinQ*quinMul^2 - 8*quinA*quinC^2*quinQ + 6*quinB^2*quinC^2*quinN*mm1 - 6*quinB^2*quinC^2*quinN + 9*quinB^2*quinC^2 - 6*quinB^2*quinMul^2 + 20*quinB*quinC^2*quinN*mm1 + 4*quinB*quinC^2*quinN*mm2c*quinMul^2 - 8*quinB*quinC^2*quinN*quinMul^2 - 40*quinB*quinC^2*quinN - 30*quinB*quinC^2*quinQ*mm1 + 2*quinB*quinC^2*quinQ*mm2c*quinMul^2 - 4*quinB*quinC^2*quinQ*quinMul^2 + 60*quinB*quinC^2*quinQ + 6*quinC^4*quinN^2*mm2c*quinMul^2 - 6*quinC^4*quinN^2*quinMul^2 - 9*quinC^2*quinN^2*mm1 + 9*quinC^2*quinN^2 + 28*quinC^2*quinN*quinQ*mm1 - 28*quinC^2*quinN*quinQ - 6*quinC^2*quinN - 25*quinC^2*quinQ^2*mm1 + 25*quinC^2*quinQ^2 + 10*quinC^2*quinQ - 4*quinQ*quinMul^2 = 0 := by
  simp only [quinA_rep, quinN_rep, quinB_rep, quinQ_rep, quinMul_rep, mm1_rep, mm2c_rep]
  linear_combination (-(58724415014906010986328125*quinC^21 - 9827450447836339946728515625*quinC^20 + 699278638673024083053320312500*quinC^19 - 27439328990352861146722148437500*quinC^18 + 643562436151832387385302171875000*quinC^17 - 9145172744999948033258080843750000*quinC^16 + 76645072223079911954945163332812500*quinC^15 - 363593376606668605657595147878437500*quinC^14 + 1015329939554647684705234442678906250*quinC^13 - 1708253871828557869572795529221156250*quinC^12 + 1689519182859984990330785016874437500*quinC^11 - 864092956489967924496538760134012500*quinC^10 + 106728887313423601597875882439130000*quinC^9 + 76661865588696172466486584744865000*quinC^8 - 20878111082713724805041552406818500*quinC^7 + 512138723564081937382894826898700*quinC^6 + 197038434459383739790827039226225*quinC^5 - 4581418468894167711156655206965*quinC^4 - 834571173346790184048957062080*quinC^3 - 656647451542621748249526464*quinC^2 + 19347663171533561502105600*quinC + 124472094164596113408000)/83696762136559616) * quinC_minpoly
lemma quin_hc7 : 4*quinA^3*quinC^4*mm2c*quinMul^2 - 4*quinA^3*quinC^4*quinMul^2 + 2*quinA^2*quinB*quinC^2*mm1 - 2*quinA^2*quinB*quinC^2 - quinA^2*quinC^2*mm1 + quinA^2*quinC^2*mm2c*quinMul^2 - 2*quinA^2*quinC^2*quinMul^2 + 2*quinA^2*quinC^2 - 6*quinA*quinB^2*quinC^2*mm1 + 6*quinA*quinB^2*quinC^2 + 4*quinA*quinB*quinC^2*mm1 + 4*quinA*quinB*quinC^2*mm2c*quinMul^2 - 8*quinA*quinB*quinC^2*quinMul^2 - 8*quinA*quinB*quinC^2 + 12*quinA*quinC^4*quinN*mm2c*quinMul^2 - 12*quinA*quinC^4*quinN*quinMul^2 - 6*quinA*quinC^2*quinN*mm1 + 6*quinA*quinC^2*quinN + 4*quinA*quinC^2*quinQ*mm1 - 4*quinA*quinC^2*quinQ - 2*quinA*quinC^2 - 9*quinB^2*quinC^2*mm1 + quinB^2*quinC^2*mm2c*quinMul^2 - 2*quinB^2*quinC^2*quinMul^2 + 18*quinB^2*quinC^2 + 20*quinB*quinC^2*quinN*mm1 - 20*quinB*quinC^2*quinN - 30*quinB*quinC^2*quinQ*mm1 + 30*quinB*quinC^2*quinQ + 6*quinB*quinC^2 - 4*quinB*quinMul^2 + 6*quinC^2*quinN*mm1 + 2*quinC^2*quinN*mm2c*quinMul^2 - 4*quinC^2*quinN*quinMul^2 - 12*quinC^2*quinN - 10*quinC^2*quinQ*mm1 + 2*quinC^2*quinQ*mm2c*quinMul^2 - 4*quinC^2*quinQ*quinMul^2 + 20*quinC^2*quinQ = 0 := by
  simp only [quinA_rep, quinN_rep, quinB_rep, quinQ_rep, quinMul_rep, mm1_rep, mm2c_rep]
  linear_combination (-(651227225005888671875*quinC^18 - 90752135785246468750000*quinC^17 + 5186507190281749974609375*quinC^16 - 155233295876808699103125000*quinC^15 + 2569878028837660009510859375*quinC^14 - 22834262298147573517311562500*quinC^13 + 100399839277930452662091609375*quinC^12 - 234369859244314026144116812500*quinC^11 + 293753284727310950446438053125*quinC^10 - 174827603467617498692876375000*quinC^9 + 18388598937466421585183473125*quinC^8 + 20454487253312992948666906000*quinC^7 - 2902743935211557567089219875*quinC^6 - 242666047822759673115432500*quinC^5 + 28400497107818346125698845*quinC^4 + 531523042484079214234380*quinC^3 + 58146589358848997628204*quinC^2 - 95425610300596224000*quinC - 584024615873740800)/237774892433408) * quinC_minpoly
lemma quin_hc8 : 6*quinA^2*quinC^4*mm2c*quinMul^2 - 6*quinA^2*quinC^4*quinMul^2 - quinA^2*quinC^2*mm1 + quinA^2*quinC^2 + 4*quinA*quinB*quinC^2*mm1 - 4*quinA*quinB*quinC^2 + 2*quinA*quinC^2*mm1 + 2*quinA*quinC^2*mm2c*quinMul^2 - 4*quinA*quinC^2*quinMul^2 - 4*quinA*quinC^2 - 9*quinB^2*quinC^2*mm1 + 9*quinB^2*quinC^2 - 6*quinB*quinC^2*mm1 + 2*quinB*quinC^2*mm2c*quinMul^2 - 4*quinB*quinC^2*quinMul^2 + 12*quinB*quinC^2 + 4*quinC^4*quinN*mm2c*quinMul^2 - 4*quinC^4*quinN*quinMul^2 + 6*quinC^2*quinN*mm1 - 6*quinC^2*quinN - 10*quinC^2*quinQ*mm1 + 10*quinC^2*quinQ + quinC^2 - quinMul^2 = 0 := by
  simp only [quinA_rep, quinN_rep, quinB_rep, quinQ_rep, quinMul_rep, mm1_rep, mm2c_rep]
  linear_combination (-(21665446908984375*quinC^15 - 2412718174211953125*quinC^14 + 104085601104449765625*quinC^13 - 2147813499576526421875*quinC^12 + 20924844071791419493750*quinC^11 - 81845593172949986781250*quinC^10 + 145995208752874978261250*quinC^9 - 110776709334862614213750*quinC^8 + 11766808219094083671875*quinC^7 + 17310486078182413436375*quinC^6 - 235917908707366651275*quinC^5 - 201971019368857607335*quinC^4 - 25097067988910855520*quinC^3 + 1716898401964344544*quinC^2 + 1414376054784000*quinC + 8252898508800)/5403974828032) * quinC_minpoly
lemma quin_hc9 : 4*quinA*quinC^4*mm2c*quinMul^2 - 4*quinA*quinC^4*quinMul^2 + 2*quinA*quinC^2*mm1 - 2*quinA*quinC^2 - 6*quinB*quinC^2*mm1 + 6*quinB*quinC^2 - quinC^2*mm1 + quinC^2*mm2c*quinMul^2 - 2*quinC^2*quinMul^2 + 2*quinC^2 = 0 := by
  simp only [quinA_rep, quinN_rep, quinB_rep, quinQ_rep, quinMul_rep, mm1_rep, mm2c_rep]
  linear_combination (-quinC^2*(80086671875*quinC^10 - 6676779681250*quinC^9 + 194438375893750*quinC^8 - 2211603944216250*quinC^7 + 7119693537587500*quinC^6 - 7979499923881000*quinC^5 + 1193731762023500*quinC^4 + 1787296457634950*quinC^3 + 207894725224125*quinC^2 + 5147198428350*quinC + 3990376006738)/30704402432) * quinC_minpoly
lemma quin_hc10 : quinC^4*mm2c*quinMul^2 - quinC^4*quinMul^2 - quinC^2*mm1 + quinC^2 = 0 := by
  simp only [quinA_rep, quinN_rep, quinB_rep, quinQ_rep, quinMul_rep, mm1_rep, mm2c_rep]
  linear_combination (-quinC^2*(888125*quinC^7 - 49181125*quinC^6 + 741663750*quinC^5 - 1664131350*quinC^4 + 510124925*quinC^3 + 623816475*quinC^2 + 145587200*quinC + 21187584)/1395654656) * quinC_minpoly

set_option maxRecDepth 10000 in
set_option maxHeartbeats 30000000 in
lemma quin_radicand_identity (t : ℝ) :
    quinD t ^ 2 * ((1+t^2)*(1+(1-mm1)*t^2)) =
      quinMul^2 * ((1+(quinS t)^2)*(1+(1-mm2c)*(quinS t)^2)) := by
  have hpoly :
      quinC^2 * (t^8+(3*quinB-quinA)*t^6+
        (quinA*quinB-3*quinN+5*quinQ)*t^4+
        (3*quinA*quinQ-quinB*quinN)*t^2+quinN*quinQ)^2 *
          (1+t^2)*(1+(1-mm1)*t^2) =
        quinMul^2 * (((t^4+quinB*t^2+quinQ)^2+
          quinC^2*t^2*(t^4+quinA*t^2+quinN)^2) *
          ((t^4+quinB*t^2+quinQ)^2+(1-mm2c)*quinC^2*t^2*
            (t^4+quinA*t^2+quinN)^2)) := by
    linear_combination quin_hc0 + quin_hc1*t^2 + quin_hc2*t^4 + quin_hc3*t^6 + quin_hc4*t^8 +
      quin_hc5*t^10 + quin_hc6*t^12 + quin_hc7*t^14 + quin_hc8*t^16 + quin_hc9*t^18 + quin_hc10*t^20
  have hd : t^4+quinB*t^2+quinQ ≠ 0 := by
    rcases quin_constants_pos with ⟨hc,ha,hn,hb,hq,hs1,hs2,hs3⟩
    have : 0 < t^4+quinB*t^2+quinQ := by positivity
    exact this.ne'
  have fraction_pullback (C P R M q x N a : ℝ) (hq : q ≠ 0)
      (h : C^2*P^2*R = M^2*((q^2+C^2*x^2*N^2) *
        (q^2+a*C^2*x^2*N^2))) :
      (C*P/q^2)^2*R = M^2*((1+(C*x*N/q)^2) *
        (1+a*(C*x*N/q)^2)) := by
    field_simp [hq]
    linear_combination h
  let P := t^8+(3*quinB-quinA)*t^6+
    (quinA*quinB-3*quinN+5*quinQ)*t^4+
    (3*quinA*quinQ-quinB*quinN)*t^2+quinN*quinQ
  let q := t^4+quinB*t^2+quinQ
  let N := t^4+quinA*t^2+quinN
  have hh : quinC^2*P^2*((1+t^2)*(1+(1-mm1)*t^2)) =
      quinMul^2*((q^2+quinC^2*t^2*N^2) *
        (q^2+(1-mm2c)*quinC^2*t^2*N^2)) := by
    simpa only [P, q, N, mul_assoc] using hpoly
  have hf := fraction_pullback quinC P
    ((1+t^2)*(1+(1-mm1)*t^2)) quinMul q t N (1-mm2c)
    (by simpa only [q] using hd) hh
  simpa only [quinD, quinS, P, q, N] using hf


lemma mm2c_bounds : 0 ≤ mm2c ∧ mm2c < 1 := by
  rcases radical_bounds with ⟨h3l,h3u,h5l,h5u,h15l,h15u⟩
  have hm := mm_bounds
  unfold mm2c
  constructor
  · linarith
  · dsimp [mm2]
    linarith

lemma quin_pullback (t : ℝ) :
    (Real.sqrt ((1+(quinS t)^2)*(1+(1-mm2c)*(quinS t)^2)))⁻¹ * quinD t =
      quinMul * (Real.sqrt ((1+t^2)*(1+(1-mm1)*t^2)))⁻¹ := by
  have hm1 := mm_bounds.2.1
  have hm2 := mm2c_bounds.2
  have hr1 : 0 < (1+t^2)*(1+(1-mm1)*t^2) := by
    apply mul_pos <;> nlinarith [sq_nonneg t,
      mul_nonneg (sub_pos.mpr hm1).le (sq_nonneg t)]
  have hr2 : 0 < (1+(quinS t)^2)*(1+(1-mm2c)*(quinS t)^2) := by
    apply mul_pos <;> nlinarith [sq_nonneg (quinS t),
      mul_nonneg (sub_pos.mpr hm2).le (sq_nonneg (quinS t))]
  let s1 := Real.sqrt ((1+t^2)*(1+(1-mm1)*t^2))
  let s2 := Real.sqrt ((1+(quinS t)^2)*(1+(1-mm2c)*(quinS t)^2))
  have hs1 : 0 < s1 := Real.sqrt_pos.2 hr1
  have hs2 : 0 < s2 := Real.sqrt_pos.2 hr2
  have hs1sq : s1^2 = (1+t^2)*(1+(1-mm1)*t^2) := Real.sq_sqrt hr1.le
  have hs2sq : s2^2 = (1+(quinS t)^2)*(1+(1-mm2c)*(quinS t)^2) :=
    Real.sq_sqrt hr2.le
  have heq : quinD t * s1 = quinMul * s2 := by
    have hsq : (quinD t*s1)^2 = (quinMul*s2)^2 := by
      rw [mul_pow, mul_pow, hs1sq, hs2sq]
      exact quin_radicand_identity t
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsq with h | h
    · exact h
    · have hp1 : 0 < quinD t*s1 := mul_pos (quinD_pos t) hs1
      have hp2 : 0 < quinMul*s2 := mul_pos quinMul_pos hs2
      nlinarith
  change s2⁻¹ * quinD t = quinMul * s1⁻¹
  field_simp [hs1.ne', hs2.ne']
  simpa [mul_comm] using heq

lemma quinS_unbounded_bound {x : ℝ} (hx : 1 ≤ x) :
    quinC / (1+quinB+quinQ) * x ≤ quinS x := by
  rcases quin_constants_pos with ⟨hc,ha,hn,hb,hq,hs1,hs2,hs3⟩
  have hx0 : 0 ≤ x := le_trans (by norm_num) hx
  have hx2 : 1 ≤ x^2 := by nlinarith
  have hx4 : 0 < x^4 := by positivity
  have hnume : x^4 ≤ x^4+quinA*x^2+quinN := by
    nlinarith [mul_nonneg ha.le (sq_nonneg x)]
  have hden : 0 < x^4+quinB*x^2+quinQ := by positivity
  have hdenle : x^4+quinB*x^2+quinQ ≤ (1+quinB+quinQ)*x^4 := by
    nlinarith [mul_le_mul_of_nonneg_left hx2 hb.le,
      mul_le_mul_of_nonneg_left (show 1 ≤ x^4 by nlinarith [sq_nonneg (x^2-1)]) hq.le]
  have hcden : 0 < 1+quinB+quinQ := by positivity
  unfold quinS
  apply (le_div_iff₀ hden).2
  have hleft : quinC / (1+quinB+quinQ) * x *
      (x^4+quinB*x^2+quinQ) ≤ quinC*x*x^4 := by
    calc
      _ ≤ quinC/(1+quinB+quinQ)*x*((1+quinB+quinQ)*x^4) := by
        gcongr
      _ = quinC*x*x^4 := by field_simp [hcden.ne'] <;> ring
  exact hleft.trans (mul_le_mul_of_nonneg_left hnume (mul_nonneg hc.le hx0))

lemma quinS_tendsto : Tendsto quinS atTop atTop := by
  apply Monotone.tendsto_atTop_atTop quinS_strictMono.monotone
  intro b
  have hc := quin_constants_pos.1
  have hd : 0 < 1+quinB+quinQ := by
    rcases quin_constants_pos with ⟨hc,ha,hn,hb,hq,hs1,hs2,hs3⟩
    positivity
  let x := 1 + max b 0 * (1+quinB+quinQ) / quinC
  have hx : 1 ≤ x := by
    dsimp [x]
    exact le_add_of_nonneg_right (div_nonneg
      (mul_nonneg (le_max_right b 0) hd.le) hc.le)
  refine ⟨x, ?_⟩
  apply (le_trans (le_max_left b 0) ?_).trans (quinS_unbounded_bound hx)
  dsimp [x]
  have hcalc : quinC/(1+quinB+quinQ) *
      (max b 0*(1+quinB+quinQ)/quinC) = max b 0 := by
    field_simp [hc.ne', hd.ne'] <;> ring
  rw [mul_add, hcalc]
  have hnonneg : 0 ≤ quinC/(1+quinB+quinQ) := div_nonneg hc.le hd.le
  linarith

lemma quinS_continuous : Continuous quinS := by
  unfold quinS
  apply Continuous.div₀
  · fun_prop
  · fun_prop
  · intro x
    rcases quin_constants_pos with ⟨hc,ha,hn,hb,hq,hs1,hs2,hs3⟩
    have : 0 < x^4+quinB*x^2+quinQ := by positivity
    exact this.ne'

lemma Ki_quintic_isogeny : Ki mm2c = quinMul * Ki mm1 := by
  let g : ℝ → ℝ := fun u =>
    (Real.sqrt ((1+u^2)*(1+(1-mm2c)*u^2)))⁻¹
  have hsub := MeasureTheory.integral_comp_mul_deriv_Ioi
    (f := quinS) (f' := quinD) (g := g) (a := 0)
    quinS_continuous.continuousOn quinS_tendsto
    (by intro x hx; simpa [quinD] using (quinS_deriv x).hasDerivWithinAt)
    (tangent_K_integrand_continuous mm2c_bounds.2).continuousOn
    (by
      have hi : IntegrableOn g (Ici 0) :=
        (integrableOn_Ici_iff_integrableOn_Ioi).2 (by
          simpa [g] using integrableOn_Ki mm2c_bounds.1 mm2c_bounds.2)
      apply hi.mono_set
      rintro y ⟨x,hx,rfl⟩
      have hs0 : quinS 0 = 0 := by simp [quinS]
      calc 0 = quinS 0 := hs0.symm
           _ ≤ quinS x := quinS_strictMono.monotone hx)
    (by
      rw [integrableOn_Ici_iff_integrableOn_Ioi]
      have hi := (integrableOn_Ki mm_bounds.1 mm_bounds.2.1).const_mul quinMul
      exact (integrableOn_congr_fun (fun x hx => by
        simpa [g, Function.comp_def, mul_comm] using quin_pullback x)
        measurableSet_Ioi).2 hi)
  have hs0 : quinS 0 = 0 := by simp [quinS]
  rw [hs0] at hsub
  have hleft : (∫ x in Ioi (0:ℝ), (g ∘ quinS) x * quinD x) =
      quinMul * Ki mm1 := by
    calc
      _ = ∫ x in Ioi (0:ℝ), quinMul *
          (Real.sqrt ((1+x^2)*(1+(1-mm1)*x^2)))⁻¹ := by
            apply integral_congr_ae
            filter_upwards [] with x
            simpa [g, Function.comp_def, mul_comm] using quin_pullback x
      _ = quinMul * Ki mm1 := by
        rw [MeasureTheory.integral_const_mul]
        rfl
  rw [hleft] at hsub
  simpa [Ki, g] using hsub.symm

lemma H_quintic_isogeny : H mm2c = quinMul * H mm1 := by
  rw [H, H, K_eq_Ki mm2c_bounds.1 mm2c_bounds.2,
    K_eq_Ki mm_bounds.1 mm_bounds.2.1, Ki_quintic_isogeny]
  ring

end Elliptic
