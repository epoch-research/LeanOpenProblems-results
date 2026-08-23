import Submission.Quintic
import Submission.Second

open Set Filter MeasureTheory
set_option maxRecDepth 10000
set_option maxHeartbeats 30000000

namespace Elliptic
local notation "r3" => Real.sqrt 3
local notation "r5" => Real.sqrt 5
local notation "r15" => Real.sqrt 15

noncomputable def quinAlpha : ℝ := (r3/10-1/4)*r5+r3/2-1/4
noncomputable def quinBeta : ℝ := (r5+3)/2
noncomputable def quinRConst : ℝ := -4*r5/5-12/5
noncomputable def quinX0 : ℝ := r15/16-7*r3/16+1/2
noncomputable def quinR1 : ℝ := -r15/8+7*r3/8-1
noncomputable def quinR0 : ℝ := (r3/16-19/160)*r5-7*r3/16+25/32
noncomputable def quinSourceX (t : ℝ) : ℝ := mm1*t^2/(1+t^2)
noncomputable def quinTargetX (t : ℝ) : ℝ := mm2c*(quinS t)^2/(1+(quinS t)^2)
noncomputable def quinRfun (x : ℝ) : ℝ :=
  quinRConst*(x-quinX0)/(x^2+quinR1*x+quinR0)
noncomputable def quinQR (t : ℝ) : ℝ := quinMul/2 * quinRfun (quinSourceX t) *
  (mm1*t*(1+(1-mm1)*t^2)/(1+t^2))
noncomputable def quinExact (t : ℝ) : ℝ := quinQR t *
  (Real.sqrt ((1+t^2)*(1+(1-mm1)*t^2)))⁻¹

lemma quin_R_constants_pos : quinX0 < 0 ∧ 0 < quinR1 ∧ 0 < quinR0 := by
  rcases radical_bounds with ⟨h3l,h3u,h5l,h5u,h15l,h15u⟩
  dsimp [quinX0, quinR1, quinR0]
  constructor
  · linarith
  constructor
  · linarith
  · nlinarith

lemma quinR_den_pos (x : ℝ) (hx : 0 ≤ x) : 0 < x^2+quinR1*x+quinR0 := by
  rcases quin_R_constants_pos with ⟨hx0,h1,h0⟩
  nlinarith [sq_nonneg x, mul_nonneg h1.le hx]

lemma quinSourceX_nonneg (t : ℝ) : 0 ≤ quinSourceX t := by
  unfold quinSourceX
  exact div_nonneg (mul_nonneg mm_bounds.1 (sq_nonneg t)) (by positivity)

lemma quinSourceX_lt_one (t : ℝ) : quinSourceX t < 1 := by
  unfold quinSourceX
  have hm := mm_bounds.2.1
  have hd : 0 < 1+t^2 := by positivity
  apply (div_lt_one hd).2
  nlinarith [mul_le_mul_of_nonneg_right hm.le (sq_nonneg t)]

lemma quinRfun_deriv (x : ℝ) (hx : 0 ≤ x) : HasDerivAt quinRfun
    (quinRConst*((x^2+quinR1*x+quinR0) -
      (x-quinX0)*(2*x+quinR1))/(x^2+quinR1*x+quinR0)^2) x := by
  have hd := (quinR_den_pos x hx).ne'
  unfold quinRfun
  convert (((hasDerivAt_id x).sub_const quinX0).const_mul quinRConst).div
    ((((hasDerivAt_id x).pow 2).add
      ((hasDerivAt_id x).const_mul quinR1)).add_const quinR0) hd using 1 <;>
    simp only [id_eq, Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Pi.pow_apply] <;>
    field_simp [hd] <;> ring

lemma quinSourceX_deriv (t : ℝ) : HasDerivAt quinSourceX
    (2*mm1*t/(1+t^2)^2) t := by
  have hd : 1+t^2 ≠ 0 := by positivity
  unfold quinSourceX
  convert ((hasDerivAt_const t mm1).mul ((hasDerivAt_id t).pow 2)).div
    (((hasDerivAt_id t).pow 2).const_add 1) hd using 1 <;>
    simp only [id_eq, Pi.add_apply, Pi.mul_apply, Pi.pow_apply] <;>
    field_simp [hd] <;> ring

noncomputable def quinQRD (t : ℝ) : ℝ :=
  let x := quinSourceX t
  let den := x^2+quinR1*x+quinR0
  let rp := quinRConst*(den-(x-quinX0)*(2*x+quinR1))/den^2
  let xp := 2*mm1*t/(1+t^2)^2
  let base := mm1*t*(1+(1-mm1)*t^2)/(1+t^2)
  let basep := mm1*((1+3*(1-mm1)*t^2)*(1+t^2)-
    t*(1+(1-mm1)*t^2)*(2*t))/(1+t^2)^2
  quinMul/2*(rp*xp*base+quinRfun x*basep)

lemma quinQR_deriv (t : ℝ) : HasDerivAt quinQR (quinQRD t) t := by
  have hx := quinSourceX_nonneg t
  have hr := (quinRfun_deriv (quinSourceX t) hx).comp t (quinSourceX_deriv t)
  have hd : 1+t^2 ≠ 0 := by positivity
  have hb : HasDerivAt (fun z : ℝ => mm1*z*(1+(1-mm1)*z^2)/(1+z^2))
      (mm1*((1+3*(1-mm1)*t^2)*(1+t^2)-
        t*(1+(1-mm1)*t^2)*(2*t))/(1+t^2)^2) t := by
    convert ((((hasDerivAt_const t mm1).mul (hasDerivAt_id t)).mul
      (((hasDerivAt_const t (1-mm1)).mul ((hasDerivAt_id t).pow 2)).const_add 1)).div
      (((hasDerivAt_id t).pow 2).const_add 1) hd) using 1 <;>
      simp only [id_eq, Pi.add_apply, Pi.mul_apply, Pi.pow_apply] <;>
      field_simp [hd] <;> ring
  have hh := ((hr.mul hb).const_mul (quinMul/2))
  convert hh using 1
  funext y
  simp only [quinQR, Function.comp_apply, Pi.mul_apply]
  ring

lemma quinAlpha_rep : quinAlpha = 65/176*quinC^3-3645/352*quinC^2+1427/88*quinC-769/352 := by
  rcases radical_relations with ⟨h3,h5,h15⟩
  dsimp [quinAlpha, quinC]; rw [h15]; ring_nf
  simp only [rp33, rp32, rp53, rp52]; ring
lemma quinBeta_rep : quinBeta = -175/352*quinC^3+4875/352*quinC^2-6825/352*quinC+973/352 := by
  rcases radical_relations with ⟨h3,h5,h15⟩
  dsimp [quinBeta, quinC]; rw [h15]; ring_nf
  simp only [rp33, rp32, rp53, rp52]; ring
lemma quinRConst_rep : quinRConst = 35/44*quinC^3-975/44*quinC^2+1365/44*quinC-973/220 := by
  rcases radical_relations with ⟨h3,h5,h15⟩
  dsimp [quinRConst, quinC]; rw [h15]; ring_nf
  simp only [rp33, rp32, rp53, rp52]; ring
lemma quinX0_rep : quinX0 = 725/5632*quinC^3-20055/5632*quinC^2+24095/5632*quinC+5539/5632 := by
  rcases radical_relations with ⟨h3,h5,h15⟩
  dsimp [quinX0, quinC]; rw [h15]; ring_nf
  simp only [rp33, rp32, rp53, rp52]; ring
lemma quinR1_rep : quinR1 = -725/2816*quinC^3+20055/2816*quinC^2-24095/2816*quinC-5539/2816 := by
  rcases radical_relations with ⟨h3,h5,h15⟩
  dsimp [quinR1, quinC]; rw [h15]; ring_nf
  simp only [rp33, rp32, rp53, rp52]; ring
lemma quinR0_rep : quinR0 = 695/2816*quinC^3-9645/1408*quinC^2+25015/2816*quinC+679/704 := by
  rcases radical_relations with ⟨h3,h5,h15⟩
  dsimp [quinR0, quinC]; rw [h15]; ring_nf
  simp only [rp33, rp32, rp53, rp52]; ring

set_option maxHeartbeats 30000000 in
lemma quin_exact_poly (t : ℝ) : 5*(-4*t^2*(quinC^2*t^2*(-2882800*quinC^3 + 80696600*quinC^2 - 122773600*quinC + 88*t^4 + 5*t^2*(18035*quinC^3 - 504855*quinC^2 + 768397*quinC - 95593) + 15215160)^2 + (-15800*quinC^3 + 442280*quinC^2 - 672872*quinC + 88*t^4 + t^2*(6625*quinC^3 - 185465*quinC^2 + 282575*quinC - 35383) + 83448)^2)*(-75*quinC^3 + 2149*quinC^2 - 4553*quinC + 2287)*(175*quinC^3 - 4875*quinC^2 + 6825*quinC - 973)*(375*quinC^3 - 10745*quinC^2 + 22765*quinC + 2*t^2*(375*quinC^3 - 10745*quinC^2 + 22765*quinC - 171) + 11093)*(-1450*quinC^3*(t^2 + 1) + 40110*quinC^2*(t^2 + 1) - 48190*quinC*(t^2 + 1) + 5*t^2*(-75*quinC^3 + 2149*quinC^2 - 4553*quinC + 2287) - 11078*t^2 - 11078)*(31313920*quinC^3*(t^2 + 1)^2 - 869130240*quinC^2*(t^2 + 1)^2 + 1127075840*quinC*(t^2 + 1)^2 + 25*t^4*(-75*quinC^3 + 2149*quinC^2 - 4553*quinC + 2287)^2 + 20*t^2*(t^2 + 1)*(-725*quinC^3 + 20055*quinC^2 - 24095*quinC - 5539)*(-75*quinC^3 + 2149*quinC^2 - 4553*quinC + 2287) + 122372096*(t^2 + 1)^2) + 4*(quinC^2*t^2*(-2882800*quinC^3 + 80696600*quinC^2 - 122773600*quinC + 88*t^4 + 5*t^2*(18035*quinC^3 - 504855*quinC^2 + 768397*quinC - 95593) + 15215160)^2 + (-15800*quinC^3 + 442280*quinC^2 - 672872*quinC + 88*t^4 + t^2*(6625*quinC^3 - 185465*quinC^2 + 282575*quinC - 35383) + 83448)^2)*(10*t^2*(t^2*(375*quinC^3 - 10745*quinC^2 + 22765*quinC - 171) + 11264)*(-75*quinC^3 + 2149*quinC^2 - 4553*quinC + 2287)*(31313920*quinC^3*(t^2 + 1)^2 - 869130240*quinC^2*(t^2 + 1)^2 + 1127075840*quinC*(t^2 + 1)^2 + 25*t^4*(-75*quinC^3 + 2149*quinC^2 - 4553*quinC + 2287)^2 + 20*t^2*(t^2 + 1)*(-725*quinC^3 + 20055*quinC^2 - 24095*quinC - 5539)*(-75*quinC^3 + 2149*quinC^2 - 4553*quinC + 2287) + 122372096*(t^2 + 1)^2 - 2*(-1450*quinC^3*(t^2 + 1) + 40110*quinC^2*(t^2 + 1) - 48190*quinC*(t^2 + 1) + 5*t^2*(-75*quinC^3 + 2149*quinC^2 - 4553*quinC + 2287) - 11078*t^2 - 11078)^2) + (-2*t^2*(t^2*(375*quinC^3 - 10745*quinC^2 + 22765*quinC - 171) + 11264) + (t^2 + 1)*(3*t^2*(375*quinC^3 - 10745*quinC^2 + 22765*quinC - 171) + 11264))*(-1450*quinC^3*(t^2 + 1) + 40110*quinC^2*(t^2 + 1) - 48190*quinC*(t^2 + 1) + 5*t^2*(-75*quinC^3 + 2149*quinC^2 - 4553*quinC + 2287) - 11078*t^2 - 11078)*(31313920*quinC^3*(t^2 + 1)^2 - 869130240*quinC^2*(t^2 + 1)^2 + 1127075840*quinC*(t^2 + 1)^2 + 25*t^4*(-75*quinC^3 + 2149*quinC^2 - 4553*quinC + 2287)^2 + 20*t^2*(t^2 + 1)*(-725*quinC^3 + 20055*quinC^2 - 24095*quinC - 5539)*(-75*quinC^3 + 2149*quinC^2 - 4553*quinC + 2287) + 122372096*(t^2 + 1)^2))*(-75*quinC^3 + 2149*quinC^2 - 4553*quinC + 2287)*(175*quinC^3 - 4875*quinC^2 + 6825*quinC - 973) - (31313920*quinC^3*(t^2 + 1)^2 - 869130240*quinC^2*(t^2 + 1)^2 + 1127075840*quinC*(t^2 + 1)^2 + 25*t^4*(-75*quinC^3 + 2149*quinC^2 - 4553*quinC + 2287)^2 + 20*t^2*(t^2 + 1)*(-725*quinC^3 + 20055*quinC^2 - 24095*quinC - 5539)*(-75*quinC^3 + 2149*quinC^2 - 4553*quinC + 2287) + 122372096*(t^2 + 1)^2)^2*(-1464320*quinC^3*(t^2 + 1)*(quinC^2*t^2*(-2882800*quinC^3 + 80696600*quinC^2 - 122773600*quinC + 88*t^4 + 5*t^2*(18035*quinC^3 - 504855*quinC^2 + 768397*quinC - 95593) + 15215160)^2 + (-15800*quinC^3 + 442280*quinC^2 - 672872*quinC + 88*t^4 + t^2*(6625*quinC^3 - 185465*quinC^2 + 282575*quinC - 35383) + 83448)^2) + 352*quinC^2*t^2*(t^2 + 1)*(-725*quinC^3 + 20055*quinC^2 - 24095*quinC + 2909)*(-2882800*quinC^3 + 80696600*quinC^2 - 122773600*quinC + 88*t^4 + 5*t^2*(18035*quinC^3 - 504855*quinC^2 + 768397*quinC - 95593) + 15215160)^2 + 41057280*quinC^2*(t^2 + 1)*(quinC^2*t^2*(-2882800*quinC^3 + 80696600*quinC^2 - 122773600*quinC + 88*t^4 + 5*t^2*(18035*quinC^3 - 504855*quinC^2 + 768397*quinC - 95593) + 15215160)^2 + (-15800*quinC^3 + 442280*quinC^2 - 672872*quinC + 88*t^4 + t^2*(6625*quinC^3 - 185465*quinC^2 + 282575*quinC - 35383) + 83448)^2) - 64294912*quinC*(t^2 + 1)*(quinC^2*t^2*(-2882800*quinC^3 + 80696600*quinC^2 - 122773600*quinC + 88*t^4 + 5*t^2*(18035*quinC^3 - 504855*quinC^2 + 768397*quinC - 95593) + 15215160)^2 + (-15800*quinC^3 + 442280*quinC^2 - 672872*quinC + 88*t^4 + t^2*(6625*quinC^3 - 185465*quinC^2 + 282575*quinC - 35383) + 83448)^2) - 5*t^2*(quinC^2*t^2*(-2882800*quinC^3 + 80696600*quinC^2 - 122773600*quinC + 88*t^4 + 5*t^2*(18035*quinC^3 - 504855*quinC^2 + 768397*quinC - 95593) + 15215160)^2 + (-15800*quinC^3 + 442280*quinC^2 - 672872*quinC + 88*t^4 + t^2*(6625*quinC^3 - 185465*quinC^2 + 282575*quinC - 35383) + 83448)^2)*(-175*quinC^3 + 4875*quinC^2 - 6825*quinC + 973)*(-75*quinC^3 + 2149*quinC^2 - 4553*quinC + 2287) + 8662016*(t^2 + 1)*(quinC^2*t^2*(-2882800*quinC^3 + 80696600*quinC^2 - 122773600*quinC + 88*t^4 + 5*t^2*(18035*quinC^3 - 504855*quinC^2 + 768397*quinC - 95593) + 15215160)^2 + (-15800*quinC^3 + 442280*quinC^2 - 672872*quinC + 88*t^4 + t^2*(6625*quinC^3 - 185465*quinC^2 + 282575*quinC - 35383) + 83448)^2)))*(35*quinC^3 - 975*quinC^2 + 1365*quinC + 87) = 0 := by
  linear_combination (3122411426376079559326171875*quinC^25*t^16 - 193425149868513793945312500000*quinC^25*t^14 + 2796863318282088500976562500000*quinC^25*t^12 + 6153400575778886718750000000000*quinC^25*t^10 + 3176048194772906250000000000000*quinC^25*t^8 - 702976669183005579986572265625*quinC^24*t^16 + 43547477978781409899902343750000*quinC^24*t^14 - 629682734405352516020507812500000*quinC^24*t^12 - 1385309245911312807421875000000000*quinC^24*t^10 - 715020787900564740000000000000000*quinC^24*t^8 + 70405536387706889595501708984375*quinC^23*t^16 - 4361421046847568373716339111328125*quinC^23*t^14 + 63064854447228583334709082031250000*quinC^23*t^12 + 138735803611312335300225585937500000*quinC^23*t^10 + 71607834337120563917503125000000000*quinC^23*t^8 + 95405240601562500000000000*quinC^23*t^6 + 6094199179841308593750000*quinC^22*t^18 - 4126410638620173403808641845703125*quinC^22*t^16 + 255618985636578958850755843505859375*quinC^22*t^14 - 3696198570894086891478958910156250000*quinC^22*t^12 - 8130292535096152138811277773437500000*quinC^22*t^10 - 4195821357411218947662538875000000000*quinC^22*t^8 + 464984042666277434737500000000000*quinC^22*t^6 + 49757656608288921600000000000000*quinC^22*t^4 - 1201446732925035351562500000*quinC^21*t^18 + 156625838274510984779351399658203125*quinC^21*t^16 - 9702531808885755918521923865478515625*quinC^21*t^14 + 140299701241962008332909893003906250000*quinC^21*t^12 + 308521010645405593390966162148437500000*quinC^21*t^10 + 159125425663468356889004105125000000000*quinC^21*t^8 - 91406524660288286691379500000000000*quinC^21*t^6 - 9778625456185298786304000000000000*quinC^21*t^4 + 103522912455182770687500000000*quinC^20*t^18 - 4025161215151992777014343248974609375*quinC^20*t^16 + 249350455207161669672520663417294921875*quinC^20*t^14 - 3605850741651839828282160392484531250000*quinC^20*t^12 - 7923937781793015879141733666788437500000*quinC^20*t^10 - 4079921251026729995890036765595000000000*quinC^20*t^8 + 7847108350942634959815355020000000000*quinC^20*t^6 + 839205403624056564419287040000000000*quinC^20*t^4 + 1494669132633600000000000000*quinC^20*t^2 + 2973604257421875000000*quinC^19*t^20 - 5104619758594585567500937500000*quinC^19*t^18 + 71191548744728432094951219936291015625*quinC^19*t^16 - 4410327326102371165335928387456529296875*quinC^19*t^14 + 63787037774497919864575368827547468750000*quinC^19*t^12 + 139952267586874985288102258503217062500000*quinC^19*t^10 + 71745796289860581909701270728347000000000*quinC^19*t^8 - 385059884016651431095746342564000000000*quinC^19*t^6 - 41151808994279824171963123712000000000*quinC^19*t^4 + 1561718569379488704307200000000000*quinC^19*t^2 - 502993749507046875000000*quinC^18*t^20 + 158385021620154982641915781250000*quinC^18*t^18 - 865885394981591929959143777918466796875*quinC^18*t^16 + 53646654443707662375238287746169416015625*quinC^18*t^14 - 776168495112083212099814970042753343750000*quinC^18*t^12 - 1696782602094290928127006260260932562500000*quinC^18*t^10 - 860682273268044198635312572346325000000000*quinC^18*t^8 + 11868329058072529433611682612740000000000*quinC^18*t^6 + 1266150984485937041942242490368000000000*quinC^18*t^4 - 262033533019113405939400704000000000*quinC^18*t^2 + 36305950186173442500000000*quinC^17*t^20 - 3204426007998000829114952375000000*quinC^17*t^18 + 7166598123502995152764689599313974218750*quinC^17*t^16 - 444111898319076281254956294523913796484375*quinC^17*t^14 + 6430723377589165640253250747460593806250000*quinC^17*t^12 + 13941168356416480706793611135880288262500000*quinC^17*t^10 + 6892804515188629326078072692134495800000000*quinC^17*t^8 - 237834197369830444882002551764218400000000*quinC^17*t^6 - 25256821446778433768052415351603200000000*quinC^17*t^4 + 18708251180862494420454019891200000000*quinC^17*t^2 + 46921252777702195200000000000*quinC^17 - 1452987541036197404700000000*quinC^16*t^20 + 42471638822076071667837789385000000*quinC^16*t^18 - 39977608351559436522299358088948538906250*quinC^16*t^16 + 2478698467774428378367831150751393391328125*quinC^16*t^14 - 35958255713860654929840683313443226631250000*quinC^16*t^12 - 76480521223329646649729114228007429222500000*quinC^16*t^10 - 35512465482245698731577247740016452680000000*quinC^16*t^8 + 3106891276475406763294143128922530080000000*quinC^16*t^6 + 326016663137766540972385087076925440000000*quinC^16*t^4 - 737459649709428884665014766632960000000*quinC^16*t^2 - 7871973596565302411264000000000*quinC^16 + 35059312899982418515600000000*quinC^15*t^20 - 363713054840629618470084871770000000*quinC^15*t^18 + 151016396146470754660191887008727152343750*quinC^15*t^16 - 9373982185770569506959484547435278373281250*quinC^15*t^14 + 136526594495550846135416484466119873232500000*quinC^15*t^12 + 278597391431298002291174759840007601855000000*quinC^15*t^10 + 110504369245911698777339304736651022160000000*quinC^15*t^8 - 25996092205419771213962128105682740160000000*quinC^15*t^6 - 2641961299598847786398962009562480640000000*quinC^15*t^4 + 17406152651603475637782121777725440000000*quinC^15*t^2 + 562013303319018942234624000000000*quinC^15 - 520052022728404334245000000000*quinC^14*t^20 + 1979321392028836959442291694901500000*quinC^14*t^18 - 388594648889302247408659045092404930531250*quinC^14*t^16 + 24174586813553256485542198077977390002593750*quinC^14*t^14 - 354778046836456314024756054610561532882500000*quinC^14*t^12 - 665610526274301422330525129064910642071000000*quinC^14*t^10 - 167252008655878654077440570358121695664000000*quinC^14*t^8 + 136178395433923441016796274665542539712000000*quinC^14*t^6 + 12650076445879659029824466069842493440000000*quinC^14*t^4 - 249553748022579562860237159944683520000000*quinC^14*t^2 - 22154070203220536356042178560000000*quinC^14 + 4664331403089548298480688800000*quinC^13*t^20 - 6895477132001483661003653770084600000*quinC^13*t^18 + 677520971556110922586699924840591233106250*quinC^13*t^16 - 42322971195464174945521969335924128944656250*quinC^13*t^14 + 629826139149473456123085948987711034666500000*quinC^13*t^12 + 994273894573943375948424061584813891600600000*quinC^13*t^10 - 81101977398928942019523868788361415446400000*quinC^13*t^8 - 446947336383462314944317008678436389568000000*quinC^13*t^6 - 31772904739979554576330245112149298380800000*quinC^13*t^4 + 2116601567450227010172066793605614796800000*quinC^13*t^2 + 522944820698134567074211561472000000*quinC^13 - 24558171714901972134776527200000*quinC^12*t^20 + 15442062331087805671075907310029600000*quinC^12*t^18 - 777807209285544112823591015658188005718750*quinC^12*t^16 + 48972645133787243541191742330326577066518750*quinC^12*t^14 - 747923466162528490017884948462767771530900000*quinC^12*t^12 - 774016648649737793465630908078868088279000000*quinC^12*t^10 + 885785692120253962797730091574259769372800000*quinC^12*t^8 + 911726149588621871284254237736892110630400000*quinC^12*t^6 + 19733872661208843923398296537138521702400000*quinC^12*t^4 - 10147987726231040270025126943077341593600000*quinC^12*t^2 - 7500053089930398144542122862182400000*quinC^12 + 76847794337024789772607208240000*quinC^11*t^20 - 21775956885423358704422399908709480000*quinC^11*t^18 + 542896730598224216148426440901782403351250*quinC^11*t^16 - 34779984233636213578813795194325271793013750*quinC^11*t^14 + 560617489451026172170196338940580323933980000*quinC^11*t^12 - 31976679513219671897567502423875223448120000*quinC^11*t^10 - 1771362131902318400262953083485281347835520000*quinC^11*t^8 - 1092454953896833177920966560973107970736640000*quinC^11*t^6 + 107190377344113591146639254844835937648640000*quinC^11*t^4 + 27810218207984388707017107343829101445120000*quinC^11*t^2 + 63685414646996158643108113809408000000*quinC^11 - 142333453109808229845352647024000*quinC^10*t^20 + 17899471340428708367602818032586788000*quinC^10*t^18 - 176452206582508449181846021977340064961750*quinC^10*t^16 + 11983891180293295240183427639287933836059250*quinC^10*t^14 - 226006488797833402459849248970906458906508000*quinC^10*t^12 + 664516977607256648739024328759951321404280000*quinC^10*t^10 + 1754688974613096611096464980244379625959808000*quinC^10*t^8 + 601790033310813270448167708093111463014912000*quinC^10*t^6 - 324322446239970160136121006652777368911872000*quinC^10*t^4 - 42651964082340966942332086707301036064768000*quinC^10*t^2 - 306533553051939203803624945007722496000*quinC^10 + 146138634583295584388725511648000*quinC^9*t^20 - 6472078281744571738224629181139616000*quinC^9*t^18 - 19446603032657641090473173771022026504625*quinC^9*t^16 + 646984767408166948866857548833414488027250*quinC^9*t^14 + 18414279912489229370131626703631224656920000*quinC^9*t^12 - 579377771972383270638252129077631679690040000*quinC^9*t^10 - 821835448811608883117126539644984808967808000*quinC^9*t^8 + 125880100527651737641490048824010743899648000*quinC^9*t^6 + 408212550379715064718398020231713723777024000*quinC^9*t^4 + 30912749382679635269281566037851249836032000*quinC^9*t^2 + 850191853625731983982987205777817600000*quinC^9 - 62997133737759619420165072160000*quinC^8*t^20 - 935030790334901983197809532410256000*quinC^8*t^18 + 29196428934990181302842594574822081375875*quinC^8*t^16 - 1676137457843425438141603785769836681281750*quinC^8*t^14 + 17746106328368715516516942214088329698120000*quinC^8*t^12 + 190430506702731398524583318582207816590584000*quinC^8*t^10 + 54053520742238045911997419936127706858880000*quinC^8*t^8 - 344962352231241540029185908925450771953152000*quinC^8*t^6 - 244178726064319350378656932660393528000512000*quinC^8*t^4 + 1039440823912001169036192032208890363904000*quinC^8*t^2 - 1344255304616468265827182947482992640000*quinC^8 - 10287193289033915614789598400000*quinC^7*t^20 + 1171308282153988443886049103954160000*quinC^7*t^18 - 4741422413943654187135123205373902606125*quinC^7*t^16 + 294991587754946382291941515293384395283375*quinC^7*t^14 - 4381031859572728798649896847267867803046000*quinC^7*t^12 - 10323929146047301741995378482106820015412000*quinC^7*t^10 + 77335899991068949118569178674464274398272000*quinC^7*t^8 + 136432548496307301173561323972573536431360000*quinC^7*t^6 + 45490076590391543670959175249069782597632000*quinC^7*t^4 - 16155521093981241651597499153149094526976000*quinC^7*t^2 + 1071182039110557478393563761004773376000*quinC^7 + 12593974326455911754772002534400*quinC^6*t^20 - 75438038084628019632676629923314000*quinC^6*t^18 + 27685917918064566907445697347393188375*quinC^6*t^16 - 4455620964670084903664315711772932811125*quinC^6*t^14 + 205908575625380352868934056969815533886000*quinC^6*t^12 - 2406036531414379761860265287959800481887200*quinC^6*t^10 - 10489194768303091061970368398670317352896000*quinC^6*t^8 - 1871105919624716042136957690210963330304000*quinC^6*t^6 + 10952747031131817830312003524164961435648000*quinC^6*t^4 + 7739678451169516260813246992435101302784000*quinC^6*t^2 - 145166154802851201340724564549278105600*quinC^6 + 698385568018157488859777094400*quinC^5*t^20 - 8188424679325678982745993785648800*quinC^5*t^18 + 24036653154511400989138607195007815025*quinC^5*t^16 - 1468587127391862191178307073187936947725*quinC^5*t^14 + 19240552266579867740008524136578677138000*quinC^5*t^12 + 116496567861031178016920874818337653612000*quinC^5*t^10 - 719985179275547952717183285532761533171200*quinC^5*t^8 - 2357141031188338365722599427556681671219200*quinC^5*t^6 - 1168425437638943089800065533354715906048000*quinC^5*t^4 - 260713382268660090159099249934173051289600*quinC^5*t^2 - 373830069066078001977531813270965452800*quinC^5 - 7092356124424552422081527040*quinC^4*t^20 + 81083112564270107667814289364480*quinC^4*t^18 - 185542626880322275542172121073129555*quinC^4*t^16 + 28358744471998327158651671965389777055*quinC^4*t^14 - 1191907018365990314677584958057005153680*quinC^4*t^12 + 12742538039836266601580708664053544135200*quinC^4*t^10 + 72590379312753239960794879479323012282880*quinC^4*t^8 - 45753908268542564378727978821964980398080*quinC^4*t^6 - 336569562984273562981834333739424462929920*quinC^4*t^4 - 148818172123228596190053477864453785518080*quinC^4*t^2 + 207150962875050897810688454792199536640*quinC^4 - 77382080179870688001637440*quinC^3*t^20 + 1366990367876743037257631329440*quinC^3*t^18 - 3155171230127340890605693106001515*quinC^3*t^16 + 592948703353953439374773504440285585*quinC^3*t^14 - 18250848866142802555067841992855626000*quinC^3*t^12 + 2569886287166797798978605295404528160*quinC^3*t^10 + 4453699912739814913714456016967715141120*quinC^3*t^8 + 16372533184919418183257583611689690183680*quinC^3*t^6 + 19821274686679163235459053672968240496640*quinC^3*t^4 + 4130182535601247414551458719525471518720*quinC^3*t^2 - 11199803726010190845218737084925214720*quinC^3 + 647622943722870021318720*quinC^2*t^20 - 16858485192420066489552390000*quinC^2*t^18 + 28189685128941631726907903264145*quinC^2*t^16 - 5680602569211789647360483878123275*quinC^2*t^14 + 346799269839514753633651208630252880*quinC^2*t^12 - 7973629928439461221703081959708741920*quinC^2*t^10 + 40435206184097081466722181560190850560*quinC^2*t^8 + 837865829214963639861047706326428354560*quinC^2*t^6 + 1929887111987301473973058234346829250560*quinC^2*t^4 + 814999291881516599817919635744589086720*quinC^2*t^2 - 3678509452433268419173302599449313280*quinC^2 - 65582902472721912781208640*quinC*t^18 + 66670562632588571374250380320*quinC*t^16 - 20159991493479986267833334689035*quinC*t^14 + 1569422661872225434813846038456720*quinC*t^12 + 10435562230206051896971784807792160*quinC*t^10 - 170450093320881259629875705652042240*quinC*t^8 + 2997383165067133703532000160899717120*quinC*t^6 - 12104554100690155267431506689272053760*quinC*t^4 + 13603072551030366494935503025597317120*quinC*t^2 + 177084379313282849205194832016834560*quinC + 818448659968213227032640*t^18 - 735143646826781076543861840*t^16 + 199255147275748524255514904025*t^14 - 16000580095131658147347197119440*t^12 + 617482475951550050264816467031520*t^10 - 508169012105840189710436022336000*t^8 + 18328755702944768609221472760883200*t^6 - 105582471837034234951674413596016640*t^4 + 127794724984792703183446713670041600*t^2 + 18794145722037589734282635803361280) * quinC_minpoly

lemma quin_exact_raw_poly (t : ℝ) : quinMul*(-quinRConst*mm1*t^2*(-quinX0*(t^2 + 1) + mm1*t^2)*(quinC^2*t^2*(quinA*t^2 + quinN + t^4)^2 + (quinB*t^2 + quinQ + t^4)^2)*(-mm1 + 2*t^2*(1 - mm1) + 2)*(quinR0*(t^2 + 1)^2 + quinR1*mm1*t^2*(t^2 + 1) + mm1^2*t^4) + quinRConst*mm1*(quinC^2*t^2*(quinA*t^2 + quinN + t^4)^2 + (quinB*t^2 + quinQ + t^4)^2)*(2*mm1*t^2*(t^2*(1 - mm1) + 1)*(quinR0*(t^2 + 1)^2 + quinR1*mm1*t^2*(t^2 + 1) + mm1^2*t^4 - (quinR1*(t^2 + 1) + 2*mm1*t^2)*(-quinX0*(t^2 + 1) + mm1*t^2)) + (-quinX0*(t^2 + 1) + mm1*t^2)*(-2*t^2*(t^2*(1 - mm1) + 1) + (t^2 + 1)*(3*t^2*(1 - mm1) + 1))*(quinR0*(t^2 + 1)^2 + quinR1*mm1*t^2*(t^2 + 1) + mm1^2*t^4)) - 2*(quinR0*(t^2 + 1)^2 + quinR1*mm1*t^2*(t^2 + 1) + mm1^2*t^4)^2*(quinC^2*mm2c*t^2*(t^2 + 1)*(quinA*t^2 + quinN + t^4)^2 - quinAlpha*(t^2 + 1)*(quinC^2*t^2*(quinA*t^2 + quinN + t^4)^2 + (quinB*t^2 + quinQ + t^4)^2) - quinBeta*mm1*t^2*(quinC^2*t^2*(quinA*t^2 + quinN + t^4)^2 + (quinB*t^2 + quinQ + t^4)^2))) = 0 := by
  simp only [quinAlpha_rep, quinBeta_rep, quinRConst_rep, quinX0_rep,
    quinR1_rep, quinR0_rep, quinA_rep, quinN_rep, quinB_rep, quinQ_rep,
    quinMul_rep, mm1_rep, mm2c_rep]
  linear_combination (1/86992915190142742075185037312 : ℝ) * quin_exact_poly t

set_option maxRecDepth 10000 in
set_option maxHeartbeats 30000000 in

lemma quin_clear_abstract
    (M RC m z X W K RD L R1 C A mc alpha beta : ℝ)
    (h : M *
      (-RC*m*z*X*W*K*RD +
       RC*m*W*(2*m*z*(z*(1-m)+1)*(RD-(R1*L+2*m*z)*X) +
         X*(-2*z*(z*(1-m)+1)+L*(3*z*(1-m)+1))*RD) -
       2*RD^2*(C^2*mc*z*L*A^2-alpha*L*W-beta*m*z*W)) = 0) :
    M*RC*m*
      (m*2*z*(RD-X*(m*2*z+L*R1))*(1+z*(1-m)) +
       RD*X*(L*(1+z*(1-m)*3)-2*z*(1+z*(1-m))) -
       z*RD*X*K)*W =
    M*2*RD^2*(L*(z*C^2*A^2*mc-W*alpha)-m*z*W*beta) := by
  linear_combination h

lemma quin_exact_rational_identity (t : ℝ) :
    quinQRD t - quinQR t * (t*(2-mm1+2*(1-mm1)*t^2) /
      ((1+t^2)*(1+(1-mm1)*t^2))) =
    quinMul*(quinTargetX t-quinAlpha-quinBeta*quinSourceX t) := by
  have h1 : 1+t^2 ≠ 0 := by positivity
  have hL : 1+(1-mm1)*t^2 ≠ 0 := by
    have hm := mm_bounds.2.1
    nlinarith [sq_nonneg t, mul_nonneg (sub_pos.mpr hm).le (sq_nonneg t)]
  have hs : 1+(quinS t)^2 ≠ 0 := by positivity
  have hrd : quinSourceX t ^ 2 + quinR1 * quinSourceX t + quinR0 ≠ 0 :=
    (quinR_den_pos _ (quinSourceX_nonneg t)).ne'
  have hqd : t^4+quinB*t^2+quinQ ≠ 0 := by
    rcases quin_constants_pos with ⟨hc,ha,hn,hb,hq,hs1,hs2,hs3⟩
    have : 0 < t^4+quinB*t^2+quinQ := by positivity
    exact this.ne'
  have hL' : 1+t^2*(1-mm1) ≠ 0 := by
    have hm := mm_bounds.2.1
    nlinarith [sq_nonneg t, mul_nonneg (sub_pos.mpr hm).le (sq_nonneg t)]
  have hqd' : t^2*(t^2+quinB)+quinQ ≠ 0 := by
    rcases quin_constants_pos with ⟨hc,ha,hn,hb,hq,hs1,hs2,hs3⟩
    have : 0 < t^2*(t^2+quinB)+quinQ := by positivity
    exact this.ne'
  have hRD : mm1*t^2*(mm1*t^2+(1+t^2)*quinR1)+(1+t^2)^2*quinR0 ≠ 0 := by
    have hp := quinR_den_pos (quinSourceX t) (quinSourceX_nonneg t)
    have heq : mm1*t^2*(mm1*t^2+(1+t^2)*quinR1)+(1+t^2)^2*quinR0 =
        (1+t^2)^2 * (quinSourceX t ^ 2 + quinR1*quinSourceX t + quinR0) := by
      unfold quinSourceX
      field_simp [h1] <;> ring
    rw [heq]
    positivity
  unfold quinQRD quinQR quinRfun quinSourceX quinTargetX
  dsimp only
  field_simp [h1, hL, hs, hrd]
  unfold quinS
  field_simp [hqd, hqd', hL', hRD]
  have hp := quin_exact_raw_poly t
  rw [show t^2+1=1+t^2 by ring] at hp
  let z := t^2
  let L := 1+t^2
  let A := quinA*t^2+quinN+t^4
  let Q := quinB*t^2+quinQ+t^4
  let W := quinC^2*t^2*A^2+Q^2
  let RD := quinR0*L^2+quinR1*mm1*t^2*L+mm1^2*t^4
  let X := -quinX0*L+mm1*t^2
  let K := -mm1+2*t^2*(1-mm1)+2
  change quinMul *
      (-quinRConst*mm1*z*X*W*K*RD +
       quinRConst*mm1*W*(2*mm1*z*(z*(1-mm1)+1)*(RD-(quinR1*L+2*mm1*z)*X) +
         X*(-2*z*(z*(1-mm1)+1)+L*(3*z*(1-mm1)+1))*RD) -
       2*RD^2*(quinC^2*mm2c*z*L*A^2-quinAlpha*L*W-quinBeta*mm1*z*W)) = 0 at hp
  have hAg : t^2*(t^2+quinA)+quinN = A := by dsimp [A]; ring
  have hQg : t^2*(t^2+quinB)+quinQ = Q := by dsimp [Q]; ring
  have hWg : Q^2+t^2*quinC^2*A^2 = W := by
    dsimp [W, z]
    ring
  have hRDg : mm1*t^2*(mm1*t^2+(1+t^2)*quinR1)+(1+t^2)^2*quinR0 = RD := by
    dsimp [RD, L]
    ring
  have hXg : mm1*t^2-(1+t^2)*quinX0 = X := by dsimp [X, L]; ring
  have hKg : 2-mm1+2*t^2*(1-mm1) = K := by dsimp [K]; ring
  rw [hAg, hQg, hWg, hRDg, hXg, hKg]
  change quinMul*quinRConst*mm1*
      (mm1*2*z*(RD-X*(mm1*2*z+L*quinR1))*(1+z*(1-mm1)) +
       RD*X*(L*(1+z*(1-mm1)*3)-2*z*(1+z*(1-mm1))) - z*RD*X*K)*W =
    quinMul*2*RD^2*(L*(z*quinC^2*A^2*mm2c-W*quinAlpha)-mm1*z*W*quinBeta)
  exact quin_clear_abstract quinMul quinRConst mm1 z X W K RD L quinR1
    quinC A mm2c quinAlpha quinBeta hp

lemma quinExact_deriv (t : ℝ) : HasDerivAt quinExact
    (quinMul*(quinTargetX t-quinAlpha-quinBeta*quinSourceX t) *
      (Real.sqrt ((1+t^2)*(1+(1-mm1)*t^2)))⁻¹) t := by
  have hh := (quinQR_deriv t).mul (sourceG_deriv t)
  convert hh using 1
  have hi := quin_exact_rational_identity t
  linear_combination -(Real.sqrt ((1+t^2)*(1+(1-mm1)*t^2)))⁻¹ * hi

noncomputable def quinExactNorm (u : ℝ) : ℝ :=
  quinMul/2 * quinRfun (mm1/(u^2+1)) *
    (mm1*u*(u^2+(1-mm1))/((u^2+1) *
      Real.sqrt ((u^2+1)*(u^2+(1-mm1)))))

lemma quinExact_eq_norm {t : ℝ} (ht : 0 < t) : quinExact t = quinExactNorm t⁻¹ := by
  have ht0 := ht.ne'
  have h1 : 1+t^2 = t^2*((t⁻¹)^2+1) := by field_simp [ht0]
  have hL : 1+(1-mm1)*t^2 = t^2*((t⁻¹)^2+(1-mm1)) := by
    field_simp [ht0]
  have hx : quinSourceX t = mm1/((t⁻¹)^2+1) := by
    unfold quinSourceX
    rw [h1]
    field_simp [ht0]
  have hs : Real.sqrt ((1+t^2)*(1+(1-mm1)*t^2)) =
      t^2 * Real.sqrt (((t⁻¹)^2+1)*((t⁻¹)^2+(1-mm1))) := by
    rw [h1, hL]
    rw [show t^2*(t⁻¹^2+1)*(t^2*(t⁻¹^2+(1-mm1))) =
      t^4*((t⁻¹)^2+1)*((t⁻¹)^2+(1-mm1)) by ring]
    rw [show t^4*((t⁻¹)^2+1)*((t⁻¹)^2+(1-mm1)) =
      t^4*(((t⁻¹)^2+1)*((t⁻¹)^2+(1-mm1))) by ring,
      Real.sqrt_mul (by positivity : (0:ℝ) ≤ t^4)]
    rw [show t^4=(t^2)^2 by ring, Real.sqrt_sq_eq_abs,
      abs_of_nonneg (sq_nonneg t)]
  unfold quinExact quinQR quinExactNorm
  rw [hx, hs, hL, h1]
  have hs0 : Real.sqrt (((t⁻¹)^2+1)*((t⁻¹)^2+(1-mm1))) ≠ 0 := by
    apply (Real.sqrt_pos.2 ?_).ne'
    have hm := mm_bounds.2.1
    apply mul_pos <;> nlinarith [sq_nonneg t⁻¹]
  field_simp [ht0, hs0]

lemma quinExactNorm_continuous : Continuous quinExactNorm := by
  unfold quinExactNorm
  have hx : Continuous (fun u : ℝ => mm1/(u^2+1)) := by
    apply continuous_const.div₀ (continuous_id.pow 2 |>.add continuous_const)
    intro u; positivity
  apply Continuous.mul
  · apply Continuous.mul continuous_const
    unfold quinRfun
    apply Continuous.div₀
    · exact continuous_const.mul (hx.sub continuous_const)
    · exact (hx.pow 2).add (continuous_const.mul hx) |>.add continuous_const
    · intro u
      apply (quinR_den_pos _ ?_).ne'
      exact div_nonneg mm_bounds.1 (by positivity)
  · apply Continuous.div₀
    · fun_prop
    · fun_prop
    · intro u
      have hm := mm_bounds.2.1
      have hr : 0 < (u^2+1)*(u^2+(1-mm1)) := by
        apply mul_pos <;> nlinarith [sq_nonneg u]
      exact (mul_pos (by positivity) (Real.sqrt_pos.2 hr)).ne'

lemma quinExact_tendsto_zero : Tendsto quinExact atTop (nhds 0) := by
  have heq : quinExact =ᶠ[atTop] fun t => quinExactNorm t⁻¹ := by
    filter_upwards [eventually_gt_atTop (0:ℝ)] with t ht
    exact quinExact_eq_norm ht
  have hc : Tendsto (fun t : ℝ => quinExactNorm t⁻¹) atTop (nhds (quinExactNorm 0)) :=
    quinExactNorm_continuous.continuousAt.tendsto.comp tendsto_inv_atTop_zero
  have hz : quinExactNorm 0 = 0 := by simp [quinExactNorm]
  rw [hz] at hc
  exact hc.congr' heq.symm

noncomputable def quinDerivFun (t : ℝ) : ℝ :=
  quinMul*(quinTargetX t-quinAlpha-quinBeta*quinSourceX t) *
    (Real.sqrt ((1+t^2)*(1+(1-mm1)*t^2)))⁻¹

lemma quinTargetX_bounds (t : ℝ) : 0 ≤ quinTargetX t ∧ quinTargetX t ≤ 1 := by
  unfold quinTargetX
  have hm0 := mm2c_bounds.1
  have hm1 := mm2c_bounds.2
  have hd : 0 < 1+(quinS t)^2 := by positivity
  constructor
  · positivity
  apply (div_le_one hd).2
  nlinarith [mul_le_mul_of_nonneg_right hm1.le (sq_nonneg (quinS t))]

lemma quinTarget_integrand_continuous : Continuous (fun t => quinTargetX t *
    (Real.sqrt ((1+t^2)*(1+(1-mm1)*t^2)))⁻¹) := by
  apply Continuous.mul
  · unfold quinTargetX
    apply Continuous.div₀
    · exact continuous_const.mul (quinS_continuous.pow 2)
    · exact continuous_const.add (quinS_continuous.pow 2)
    · intro t; positivity
  · exact tangent_K_integrand_continuous mm_bounds.2.1


lemma integrableOn_quinTarget : IntegrableOn (fun t => quinTargetX t *
    (Real.sqrt ((1+t^2)*(1+(1-mm1)*t^2)))⁻¹) (Ioi 0) := by
  apply (integrableOn_Ki mm_bounds.1 mm_bounds.2.1).mono'
    quinTarget_integrand_continuous.aestronglyMeasurable
  filter_upwards [] with t
  rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (quinTargetX_bounds t).1]
  let z : ℝ := (Real.sqrt ((1+t^2)*(1+(1-mm1)*t^2)))⁻¹
  calc
    quinTargetX t * ‖z‖ ≤ ‖z‖ := by
      simpa using mul_le_mul_of_nonneg_right (quinTargetX_bounds t).2 (norm_nonneg z)
    _ = z := by rw [Real.norm_eq_abs, abs_of_nonneg] <;> positivity

lemma integrableOn_quinDeriv : IntegrableOn quinDerivFun (Ioi 0) := by
  have ht := integrableOn_quinTarget
  have hg := (integrableOn_Ki mm_bounds.1 mm_bounds.2.1).const_mul quinAlpha
  have hj := (integrableOn_Jfun mm_bounds.1 mm_bounds.2.1).const_mul quinBeta
  have hi := (ht.sub hg).sub hj |>.const_mul quinMul
  exact (integrableOn_congr_fun (fun x hx => by
    unfold quinDerivFun quinSourceX Jfun
    simp only [Pi.sub_apply]
    ring) measurableSet_Ioi).2 hi

lemma integral_quinDeriv_zero : ∫ t in Ioi (0:ℝ), quinDerivFun t = 0 := by
  have h := MeasureTheory.integral_Ioi_of_hasDerivAt_of_tendsto'
    (f := quinExact) (f' := quinDerivFun) (a := 0) (m := 0)
    (by intro x hx; simpa [quinDerivFun] using quinExact_deriv x)
    integrableOn_quinDeriv quinExact_tendsto_zero
  simpa [quinExact, quinQR] using h

lemma Ji_quintic_isogeny :
    Ji mm2c = quinMul*(quinAlpha*Ki mm1+quinBeta*Ji mm1) := by
  let jt : ℝ → ℝ := Jfun mm2c
  have hsub := MeasureTheory.integral_comp_mul_deriv_Ioi
    (f := quinS) (f' := quinD) (g := jt) (a := 0)
    quinS_continuous.continuousOn quinS_tendsto
    (by intro x hx; simpa [quinD] using (quinS_deriv x).hasDerivWithinAt)
    (by exact (Jfun_continuous mm2c_bounds.2).continuousOn)
    (by
      have hi : IntegrableOn jt (Ici 0) :=
        (integrableOn_Ici_iff_integrableOn_Ioi).2 (by
          simpa [jt] using integrableOn_Jfun mm2c_bounds.1 mm2c_bounds.2)
      apply hi.mono_set
      rintro y ⟨x,hx,rfl⟩
      have hs0 : quinS 0 = 0 := by simp [quinS]
      calc 0 = quinS 0 := hs0.symm
           _ ≤ quinS x := quinS_strictMono.monotone hx)
    (by
      rw [integrableOn_Ici_iff_integrableOn_Ioi]
      have hi := integrableOn_quinTarget.const_mul quinMul
      exact (integrableOn_congr_fun (fun x hx => by
        change jt (quinS x) * quinD x = _
        rw [show jt (quinS x) = quinTargetX x *
          (Real.sqrt ((1+(quinS x)^2)*(1+(1-mm2c)*(quinS x)^2)))⁻¹ by
            rfl]
        rw [mul_assoc, quin_pullback]
        ring) measurableSet_Ioi).2 hi)
  have hs0 : quinS 0 = 0 := by simp [quinS]
  rw [hs0] at hsub
  have hpull : (∫ x in Ioi (0:ℝ), (jt ∘ quinS) x * quinD x) =
      quinMul * ∫ x in Ioi (0:ℝ), quinTargetX x *
        (Real.sqrt ((1+x^2)*(1+(1-mm1)*x^2)))⁻¹ := by
    calc
      _ = ∫ x in Ioi (0:ℝ), quinMul * (quinTargetX x *
          (Real.sqrt ((1+x^2)*(1+(1-mm1)*x^2)))⁻¹) := by
            apply integral_congr_ae
            filter_upwards [] with x
            change jt (quinS x) * quinD x = _
            rw [show jt (quinS x) = quinTargetX x *
              (Real.sqrt ((1+(quinS x)^2)*(1+(1-mm2c)*(quinS x)^2)))⁻¹ by
                rfl]
            rw [mul_assoc, quin_pullback]
            ring
      _ = _ := by rw [MeasureTheory.integral_const_mul]
  rw [hpull] at hsub
  have hzero := integral_quinDeriv_zero
  unfold quinDerivFun at hzero
  rw [show (fun t : ℝ => quinMul *
      (quinTargetX t - quinAlpha - quinBeta * quinSourceX t) *
        (Real.sqrt ((1+t^2)*(1+(1-mm1)*t^2)))⁻¹) =
      (fun t => quinMul * ((quinTargetX t - quinAlpha - quinBeta * quinSourceX t) *
        (Real.sqrt ((1+t^2)*(1+(1-mm1)*t^2)))⁻¹)) by
      funext t; ring] at hzero
  have hint : (∫ x in Ioi (0:ℝ), quinTargetX x *
      (Real.sqrt ((1+x^2)*(1+(1-mm1)*x^2)))⁻¹) =
      quinAlpha*Ki mm1+quinBeta*Ji mm1 := by
    rw [MeasureTheory.integral_const_mul] at hzero
    have hc := quinMul_pos
    have hinner : ∫ x in Ioi (0:ℝ),
        (quinTargetX x-quinAlpha-quinBeta*quinSourceX x) *
          (Real.sqrt ((1+x^2)*(1+(1-mm1)*x^2)))⁻¹ = 0 := by
      nlinarith
    have heq : (∫ x in Ioi (0:ℝ),
        (quinTargetX x-quinAlpha-quinBeta*quinSourceX x) *
          (Real.sqrt ((1+x^2)*(1+(1-mm1)*x^2)))⁻¹) =
        (∫ x in Ioi (0:ℝ), quinTargetX x *
          (Real.sqrt ((1+x^2)*(1+(1-mm1)*x^2)))⁻¹) -
        (∫ x in Ioi (0:ℝ), quinAlpha *
          (Real.sqrt ((1+x^2)*(1+(1-mm1)*x^2)))⁻¹) -
        (∫ x in Ioi (0:ℝ), quinBeta * Jfun mm1 x) := by
      calc
        _ = ∫ x in Ioi (0:ℝ),
            (quinTargetX x * (Real.sqrt ((1+x^2)*(1+(1-mm1)*x^2)))⁻¹ -
              quinAlpha * (Real.sqrt ((1+x^2)*(1+(1-mm1)*x^2)))⁻¹) -
              quinBeta * Jfun mm1 x := by
                apply integral_congr_ae
                filter_upwards [] with x
                unfold quinSourceX Jfun
                ring
        _ = (∫ x in Ioi (0:ℝ),
              quinTargetX x * (Real.sqrt ((1+x^2)*(1+(1-mm1)*x^2)))⁻¹ -
              quinAlpha * (Real.sqrt ((1+x^2)*(1+(1-mm1)*x^2)))⁻¹) -
              (∫ x in Ioi (0:ℝ), quinBeta * Jfun mm1 x) := by
                simpa only [Pi.sub_apply] using
                  (MeasureTheory.integral_sub
                    (integrableOn_quinTarget.sub
                      ((integrableOn_Ki mm_bounds.1 mm_bounds.2.1).const_mul quinAlpha))
                    ((integrableOn_Jfun mm_bounds.1 mm_bounds.2.1).const_mul quinBeta))
        _ = _ := by
          congr 1
          simpa only [Pi.sub_apply] using
            (MeasureTheory.integral_sub integrableOn_quinTarget
              ((integrableOn_Ki mm_bounds.1 mm_bounds.2.1).const_mul quinAlpha))
    rw [heq, MeasureTheory.integral_const_mul,
      MeasureTheory.integral_const_mul] at hinner
    simpa [Ki, Ji] using (show
      (∫ x in Ioi (0:ℝ), quinTargetX x *
        (Real.sqrt ((1+x^2)*(1+(1-mm1)*x^2)))⁻¹) =
        quinAlpha*(∫ x in Ioi (0:ℝ),
          (Real.sqrt ((1+x^2)*(1+(1-mm1)*x^2)))⁻¹) +
        quinBeta*(∫ x in Ioi (0:ℝ), Jfun mm1 x) by linarith)
  rw [hint] at hsub
  simpa [Ji, jt] using hsub.symm






lemma HE_quintic_isogeny :
    H mm2c - En mm2c = quinMul *
      (quinAlpha * H mm1 + quinBeta * (H mm1 - En mm1)) := by
  unfold H En
  rw [K_eq_Ki mm2c_bounds.1 mm2c_bounds.2,
    E_eq_Ei mm2c_bounds.1 mm2c_bounds.2.le,
    K_eq_Ki mm_bounds.1 mm_bounds.2.1,
    E_eq_Ei mm_bounds.1 mm_bounds.2.1.le]
  have h2 := Ki_sub_Ei_eq_Ji mm2c_bounds.1 mm2c_bounds.2
  have h1 := Ki_sub_Ei_eq_Ji mm_bounds.1 mm_bounds.2.1
  have hj := Ji_quintic_isogeny
  rw [show (2 / Real.pi) * Ki mm2c - (2 / Real.pi) * Ei mm2c =
      (2 / Real.pi) * (Ki mm2c - Ei mm2c) by ring,
    h2,
    show (2 / Real.pi) * Ki mm1 - (2 / Real.pi) * Ei mm1 =
      (2 / Real.pi) * (Ki mm1 - Ei mm1) by ring,
    h1, hj]
  ring


end Elliptic
