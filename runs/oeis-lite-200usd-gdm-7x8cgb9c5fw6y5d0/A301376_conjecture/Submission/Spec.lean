/-
Copyright 2026 The Formal Conjectures Authors.
-/
import FormalConjectures.Util.ProblemImports

set_option linter.style.namespace false

open Nat Finset Int
set_option maxRecDepth 10000

def a (n : ℕ) : ℕ :=
  let R := Finset.range (n + 1)
  let domain : Finset ((ℕ × ℕ) × (ℕ × ℕ)) := (R.product R).product (R.product R)

  Finset.card $ domain.filter (λ p : (ℕ × ℕ) × (ℕ × ℕ) =>
    let x := p.fst.fst; let y := p.fst.snd;
    let z := p.snd.fst; let w := p.snd.snd;

    x^2 + y^2 + z^2 + w^2 = n^2 ∧
    z ≤ w ∧
    (∃ k ∈ Finset.range (n + 1), (x^2 : ℤ) - (3 * y : ℤ)^2 = (4^k : ℤ))
  )

lemma not_sq_add_sq (m : ℕ) (p : ℕ) [hp : Fact p.Prime] (hp3 : p % 4 = 3) (h1 : p ∣ m) (h2 : ¬ p^2 ∣ m) :
    ¬ ∃ z w : ℕ, z^2 + w^2 = m := by
  intro ⟨z, w, hzw⟩
  have hm0 : m ≠ 0 := by
    rintro rfl
    apply h2
    exact dvd_zero (p^2)
  have h_padic : padicValNat p m = 1 := by
    have h_le : 1 ≤ padicValNat p m := one_le_padicValNat_of_dvd hm0 h1
    have h_lt : padicValNat p m < 2 := by
      by_contra h_ge
      push_neg at h_ge
      have h_pow_dvd : p^2 ∣ m := (padicValNat_dvd_iff_le hm0).mpr h_ge
      contradiction
    omega
  have h_eq : (∃ x y, m = x ^ 2 + y ^ 2) := ⟨z, w, hzw.symm⟩
  rw [Nat.eq_sq_add_sq_iff] at h_eq
  have hp_mem : p ∈ m.primeFactors := Nat.mem_primeFactors.mpr ⟨hp.out, h1, hm0⟩
  have h_even : Even (padicValNat p m) := h_eq p hp_mem hp3
  rw [h_padic] at h_even
  contradiction

lemma classification_step (x y k : ℕ) (h_eq : (x^2 : ℤ) - (3 * y : ℤ)^2 = (4^k : ℤ)) :
    ∃ u v : ℕ, u + v = 2 * k ∧ u ≤ v ∧ 36 * (x^2 + y^2) = 10 * 2^(2*v) + 16 * 2^(2*k) + 10 * 2^(2*u) := by
  have h_4k : (4^k : ℤ) ≥ 0 := by positivity
  have h_ge_int : (x^2 : ℤ) ≥ (3 * y : ℤ)^2 := by
    omega
  have h_ge_nat : (3 * y)^2 ≤ x^2 := by
    exact_mod_cast h_ge_int
  have h_ge : 3 * y ≤ x := by
    rwa [Nat.pow_le_pow_iff_left (by decide : 2 ≠ 0)] at h_ge_nat
  have h_sub_cast : ((x - 3 * y : ℕ) : ℤ) = (x : ℤ) - (3 * y : ℤ) := Int.ofNat_sub h_ge
  have h_add_cast : ((x + 3 * y : ℕ) : ℤ) = (x : ℤ) + (3 * y : ℤ) := by push_cast; rfl
  have h_ge' : (x^2 : ℕ) ≥ (3 * y)^2 := h_ge_nat
  have h_prod_int : ((x - 3 * y : ℕ) : ℤ) * ((x + 3 * y : ℕ) : ℤ) = (x^2 : ℤ) - (3 * y : ℤ)^2 := by
    rw [h_sub_cast, h_add_cast]
    ring
  have h_4k_eq : 4^k = 2^(2 * k) := by
    rw [show 4 = 2^2 by rfl, ← Nat.pow_mul]
  have h_prod_nat : (x - 3 * y) * (x + 3 * y) = 2^(2 * k) := by
    have h_prod_cast : (((x - 3 * y) * (x + 3 * y) : ℕ) : ℤ) = ((2^(2 * k) : ℕ) : ℤ) := by
      rw [Nat.cast_mul]
      rw [h_prod_int, h_eq]
      rw [show (4^k : ℤ) = ((4^k : ℕ) : ℤ) by rfl]
      rw [show ((4^k : ℕ) : ℤ) = ((2^(2 * k) : ℕ) : ℤ) by rw [h_4k_eq]]
    exact_mod_cast h_prod_cast
  have h_dvd_left : (x - 3 * y) ∣ 2^(2 * k) := ⟨x + 3 * y, h_prod_nat.symm⟩
  have h_dvd_right : (x + 3 * y) ∣ 2^(2 * k) := by
    use (x - 3 * y)
    rw [mul_comm (x + 3 * y)]
    exact h_prod_nat.symm
  obtain ⟨u, hu_le, hu_eq⟩ := (dvd_prime_pow Nat.prime_two).mp h_dvd_left
  obtain ⟨v, hv_le, hv_eq⟩ := (dvd_prime_pow Nat.prime_two).mp h_dvd_right
  have h_pow_sum : 2^(u + v) = 2^(2 * k) := by
    rw [pow_add, ← hu_eq, ← hv_eq, h_prod_nat]
  have h_uv : u + v = 2 * k := Nat.pow_right_injective (by decide) h_pow_sum
  have h_uv_le : u ≤ v := by
    have h_pow_le : 2^u ≤ 2^v := by
      rw [← hu_eq, ← hv_eq]
      omega
    rwa [Nat.pow_le_pow_iff_right (by decide : 1 < 2)] at h_pow_le
  use u, v
  refine ⟨h_uv, h_uv_le, ?_⟩
  have h_id_int : (36 * (x^2 + y^2) : ℤ) = 10 * 2^(2*v) + 16 * 2^(2*k) + 10 * 2^(2*u) := by
    have hA : (2^u : ℤ) = (x : ℤ) - (3 * y : ℤ) := by
      exact_mod_cast hu_eq.symm
    have hB : (2^v : ℤ) = (x : ℤ) + (3 * y : ℤ) := by
      exact_mod_cast hv_eq.symm
    have h_v2 : (2^(2*v) : ℤ) = (2^v : ℤ)^2 := by
      rw [← pow_mul, mul_comm]
    have h_u2 : (2^(2*u) : ℤ) = (2^u : ℤ)^2 := by
      rw [← pow_mul, mul_comm]
    have h_2k : (2^(2*k) : ℤ) = (2^u : ℤ) * (2^v : ℤ) := by
      rw [← pow_add, ← h_uv]
    rw [h_v2, h_u2, h_2k, hA, hB]
    ring
  exact_mod_cast h_id_int

def N : ℕ := 7331706316454593874069996080097306921208616634944143816098998208807824939833954577737272991598005272475093539278848943489030926912487104950650377651542326204192837994914604151928768986683255388816620643876213197737094085641729382831770786319338585074137992528083158518043187731188093291379997099716146157488497448841134548455771555964992749062561788668926504310300776975912776250943507830866907062296946659611930169955104593080639372855463333784117147982120766401388650000265201004275337532408874691726603368087927874262415912037478964663872029475001870346945625997439806171207063508382081409495019150092969327401713967440159805115654419226134991990077467362282123330759412142539676280132326741049655273102208608851928866416517403855632240349295282198918657459729800847157097270679909948674151401757970669647330977719276763664583468080231084981196441839327920635141421260679353907653495561106570767118119871966007022598915686889065967486482286088073027751514599642468907815845758090854205944526800347387410472527448711119224093174251550193618613971191871942437640870636836724060926074682330930555764015783219472666821721010135107379083698839793716053329918754636409646402834405784019788401625054680268936770111268308664319212394145252457347059203173673867668299631914025676543533111748985459059604026332855781584150450110138483491690350358715652685762425734664047783954872681495588508368865093505270215554787372772896246200605071974857362695000963402273380333550166223102125941696213104430869669618933892507580302001274295604475968835916996041423743390390759981389819135143591757525505567903198379016514590769830571267174006759957795009323555210057969950477440510492466355651003761399865192018237363670945033998444392820858795820365341331084794404179306504939515391921900663047217420801110000495097111414321893166035111475103881062839910529052514520289559316438297623144998832983434616929247234875020843130406469850988783419482347829385277292416799940681609977258271569546487279145771677657474585699229127406887422442607832879511890643114475471895687835852288337116753291019186353988338899506603428090747625980578795143251877493167959068429642243240047429325758229674300170168482537923899527829332580942525873463029876636893964406740286763370494724436788579552049488283266988132068200604512610866142401469133587778380903835582238500085063187108825959216741438918150413937567153131172042986342057409076601160343934996803806059770500916169318597500048676547090579359838258386004458842250143372769501777863269539128243670917788148429949193098681217890972406722500628849287905470090098627626668849164820971886154524865863073520027557751988251094512213722635595492172202718074806266835367577865899436410000705923501397648883899944608398622771993250787655687069204978188205054226419451721111245115125418772828810328331362428973992449286492307481678869292868582198275597543394129666881369952237645168723877803299012900801360932715080588825263346558064626277141470692281909939937114109874725720506385813976377434791428640010860677998683624406792943087642484943256626209643428059580508319386057111775899201603918091719872156719525888620694865534693001285920968510014605253970115643989037306972088646072193106705093924165271687245884284209222584577507263487783844210566343277989547036986521693436162156456620742110612562538587024418422899581011661555446196143393517560767417182792676338247283235028612270646774391674248950583858526636882624350148800940631665697049739028646078075251829671305786527733009488316779204573468085986729785571090396855674383249788524045239197766216119637711684386595074820648591398590994587172041909737117477810754037938587193190283439960447968187350880522527911020433969855587818558290264737074140941588235961227973147391863342321353548880512816682312923688929848915402332692545510658738329382562377275664312398859608832011317736557452764894512089873383583598142296169225506132100563613572294531652393093494471815573641539153889404617227862576740364057371278650444270617877863970593524419773432817565309429447422228933454245646529026498014177199627593263166000204229894901582821749453847184118422343872722146368147657557916828878207671482220183400159591999266586925048008763110240860896456887035932562172310498039065508622110060269314148184830533807201622954083325400088852526495699411730174737464323321821919019893800472510979160226475972935253744718555835580065325041230580189512216790026082433428112039813017382962653899076259376256932853266293285906801621723564500193526105109503828695814411254144480175180534585100876287970263498780941199764024673498145855585270474648656606995937237815155939264551791271781145886822830178523003981707165325653324471063179333684076146777169955433534425293331650854822495291240367118132975188318020579648130560972372918348522633017440087595516298256996625941589842800661097172282303114198239702228111626018312605869634039077771224165039563008813533698910805820747334792593427091812986462736598933054786772659345135598302652165303933034789763678046636971985457950425095202082392543124476811432265409513783839369513022604067765972158774824905411461392101191145573

lemma getD_mem {α : Type} (l : List α) (idx : ℕ) (d : α) : l.getD idx d ∈ d :: l := by
  induction l generalizing idx with
  | nil =>
    simp [List.getD]
  | cons x xs ih =>
    rcases idx with _ | idx
    · simp [List.getD]
    · simp only [List.getD]
      have h := ih idx
      rw [List.mem_cons] at h
      rw [List.mem_cons]
      rcases h with h_eq | h_mem
      · left; exact h_eq
      · right
        rw [List.mem_cons]
        right; exact h_mem

lemma prime_3 : Nat.Prime 3 := by norm_num
lemma mod4_3 : 3 % 4 = 3 := by decide
lemma prime_7 : Nat.Prime 7 := by norm_num
lemma mod4_7 : 7 % 4 = 3 := by decide
lemma prime_11 : Nat.Prime 11 := by norm_num
lemma mod4_11 : 11 % 4 = 3 := by decide
lemma prime_19 : Nat.Prime 19 := by norm_num
lemma mod4_19 : 19 % 4 = 3 := by decide
lemma prime_23 : Nat.Prime 23 := by norm_num
lemma mod4_23 : 23 % 4 = 3 := by decide
lemma prime_31 : Nat.Prime 31 := by norm_num
lemma mod4_31 : 31 % 4 = 3 := by decide
lemma prime_43 : Nat.Prime 43 := by norm_num
lemma mod4_43 : 43 % 4 = 3 := by decide
lemma prime_47 : Nat.Prime 47 := by norm_num
lemma mod4_47 : 47 % 4 = 3 := by decide
lemma prime_59 : Nat.Prime 59 := by norm_num
lemma mod4_59 : 59 % 4 = 3 := by decide
lemma prime_67 : Nat.Prime 67 := by norm_num
lemma mod4_67 : 67 % 4 = 3 := by decide
lemma prime_71 : Nat.Prime 71 := by norm_num
lemma mod4_71 : 71 % 4 = 3 := by decide
lemma prime_79 : Nat.Prime 79 := by norm_num
lemma mod4_79 : 79 % 4 = 3 := by decide
lemma prime_83 : Nat.Prime 83 := by norm_num
lemma mod4_83 : 83 % 4 = 3 := by decide
lemma prime_103 : Nat.Prime 103 := by norm_num
lemma mod4_103 : 103 % 4 = 3 := by decide
lemma prime_107 : Nat.Prime 107 := by norm_num
lemma mod4_107 : 107 % 4 = 3 := by decide
lemma prime_127 : Nat.Prime 127 := by norm_num
lemma mod4_127 : 127 % 4 = 3 := by decide
lemma prime_131 : Nat.Prime 131 := by norm_num
lemma mod4_131 : 131 % 4 = 3 := by decide
lemma prime_139 : Nat.Prime 139 := by norm_num
lemma mod4_139 : 139 % 4 = 3 := by decide
lemma prime_151 : Nat.Prime 151 := by norm_num
lemma mod4_151 : 151 % 4 = 3 := by decide
lemma prime_163 : Nat.Prime 163 := by norm_num
lemma mod4_163 : 163 % 4 = 3 := by decide
lemma prime_167 : Nat.Prime 167 := by norm_num
lemma mod4_167 : 167 % 4 = 3 := by decide
lemma prime_179 : Nat.Prime 179 := by norm_num
lemma mod4_179 : 179 % 4 = 3 := by decide
lemma prime_191 : Nat.Prime 191 := by norm_num
lemma mod4_191 : 191 % 4 = 3 := by decide
lemma prime_199 : Nat.Prime 199 := by norm_num
lemma mod4_199 : 199 % 4 = 3 := by decide
lemma prime_211 : Nat.Prime 211 := by norm_num
lemma mod4_211 : 211 % 4 = 3 := by decide
lemma prime_223 : Nat.Prime 223 := by norm_num
lemma mod4_223 : 223 % 4 = 3 := by decide
lemma prime_227 : Nat.Prime 227 := by norm_num
lemma mod4_227 : 227 % 4 = 3 := by decide
lemma prime_239 : Nat.Prime 239 := by norm_num
lemma mod4_239 : 239 % 4 = 3 := by decide
lemma prime_251 : Nat.Prime 251 := by norm_num
lemma mod4_251 : 251 % 4 = 3 := by decide
lemma prime_263 : Nat.Prime 263 := by norm_num
lemma mod4_263 : 263 % 4 = 3 := by decide
lemma prime_271 : Nat.Prime 271 := by norm_num
lemma mod4_271 : 271 % 4 = 3 := by decide
lemma prime_283 : Nat.Prime 283 := by norm_num
lemma mod4_283 : 283 % 4 = 3 := by decide
lemma prime_307 : Nat.Prime 307 := by norm_num
lemma mod4_307 : 307 % 4 = 3 := by decide
lemma prime_311 : Nat.Prime 311 := by norm_num
lemma mod4_311 : 311 % 4 = 3 := by decide
lemma prime_331 : Nat.Prime 331 := by norm_num
lemma mod4_331 : 331 % 4 = 3 := by decide
lemma prime_347 : Nat.Prime 347 := by norm_num
lemma mod4_347 : 347 % 4 = 3 := by decide
lemma prime_359 : Nat.Prime 359 := by norm_num
lemma mod4_359 : 359 % 4 = 3 := by decide
lemma prime_367 : Nat.Prime 367 := by norm_num
lemma mod4_367 : 367 % 4 = 3 := by decide
lemma prime_379 : Nat.Prime 379 := by norm_num
lemma mod4_379 : 379 % 4 = 3 := by decide
lemma prime_383 : Nat.Prime 383 := by norm_num
lemma mod4_383 : 383 % 4 = 3 := by decide
lemma prime_419 : Nat.Prime 419 := by norm_num
lemma mod4_419 : 419 % 4 = 3 := by decide
lemma prime_431 : Nat.Prime 431 := by norm_num
lemma mod4_431 : 431 % 4 = 3 := by decide
lemma prime_439 : Nat.Prime 439 := by norm_num
lemma mod4_439 : 439 % 4 = 3 := by decide
lemma prime_443 : Nat.Prime 443 := by norm_num
lemma mod4_443 : 443 % 4 = 3 := by decide
lemma prime_463 : Nat.Prime 463 := by norm_num
lemma mod4_463 : 463 % 4 = 3 := by decide
lemma prime_467 : Nat.Prime 467 := by norm_num
lemma mod4_467 : 467 % 4 = 3 := by decide
lemma prime_479 : Nat.Prime 479 := by norm_num
lemma mod4_479 : 479 % 4 = 3 := by decide
lemma prime_487 : Nat.Prime 487 := by norm_num
lemma mod4_487 : 487 % 4 = 3 := by decide
lemma prime_491 : Nat.Prime 491 := by norm_num
lemma mod4_491 : 491 % 4 = 3 := by decide
lemma prime_499 : Nat.Prime 499 := by norm_num
lemma mod4_499 : 499 % 4 = 3 := by decide
lemma prime_503 : Nat.Prime 503 := by norm_num
lemma mod4_503 : 503 % 4 = 3 := by decide
lemma prime_523 : Nat.Prime 523 := by norm_num
lemma mod4_523 : 523 % 4 = 3 := by decide
lemma prime_547 : Nat.Prime 547 := by norm_num
lemma mod4_547 : 547 % 4 = 3 := by decide
lemma prime_563 : Nat.Prime 563 := by norm_num
lemma mod4_563 : 563 % 4 = 3 := by decide
lemma prime_571 : Nat.Prime 571 := by norm_num
lemma mod4_571 : 571 % 4 = 3 := by decide
lemma prime_587 : Nat.Prime 587 := by norm_num
lemma mod4_587 : 587 % 4 = 3 := by decide
lemma prime_599 : Nat.Prime 599 := by norm_num
lemma mod4_599 : 599 % 4 = 3 := by decide
lemma prime_607 : Nat.Prime 607 := by norm_num
lemma mod4_607 : 607 % 4 = 3 := by decide
lemma prime_619 : Nat.Prime 619 := by norm_num
lemma mod4_619 : 619 % 4 = 3 := by decide
lemma prime_631 : Nat.Prime 631 := by norm_num
lemma mod4_631 : 631 % 4 = 3 := by decide
lemma prime_643 : Nat.Prime 643 := by norm_num
lemma mod4_643 : 643 % 4 = 3 := by decide
lemma prime_647 : Nat.Prime 647 := by norm_num
lemma mod4_647 : 647 % 4 = 3 := by decide
lemma prime_659 : Nat.Prime 659 := by norm_num
lemma mod4_659 : 659 % 4 = 3 := by decide
lemma prime_683 : Nat.Prime 683 := by norm_num
lemma mod4_683 : 683 % 4 = 3 := by decide
lemma prime_691 : Nat.Prime 691 := by norm_num
lemma mod4_691 : 691 % 4 = 3 := by decide
lemma prime_719 : Nat.Prime 719 := by norm_num
lemma mod4_719 : 719 % 4 = 3 := by decide
lemma prime_727 : Nat.Prime 727 := by norm_num
lemma mod4_727 : 727 % 4 = 3 := by decide
lemma prime_739 : Nat.Prime 739 := by norm_num
lemma mod4_739 : 739 % 4 = 3 := by decide
lemma prime_743 : Nat.Prime 743 := by norm_num
lemma mod4_743 : 743 % 4 = 3 := by decide
lemma prime_751 : Nat.Prime 751 := by norm_num
lemma mod4_751 : 751 % 4 = 3 := by decide
lemma prime_787 : Nat.Prime 787 := by norm_num
lemma mod4_787 : 787 % 4 = 3 := by decide
lemma prime_811 : Nat.Prime 811 := by norm_num
lemma mod4_811 : 811 % 4 = 3 := by decide
lemma prime_823 : Nat.Prime 823 := by norm_num
lemma mod4_823 : 823 % 4 = 3 := by decide
lemma prime_827 : Nat.Prime 827 := by norm_num
lemma mod4_827 : 827 % 4 = 3 := by decide
lemma prime_839 : Nat.Prime 839 := by norm_num
lemma mod4_839 : 839 % 4 = 3 := by decide
lemma prime_859 : Nat.Prime 859 := by norm_num
lemma mod4_859 : 859 % 4 = 3 := by decide
lemma prime_863 : Nat.Prime 863 := by norm_num
lemma mod4_863 : 863 % 4 = 3 := by decide
lemma prime_883 : Nat.Prime 883 := by norm_num
lemma mod4_883 : 883 % 4 = 3 := by decide
lemma prime_887 : Nat.Prime 887 := by norm_num
lemma mod4_887 : 887 % 4 = 3 := by decide
lemma prime_907 : Nat.Prime 907 := by norm_num
lemma mod4_907 : 907 % 4 = 3 := by decide
lemma prime_911 : Nat.Prime 911 := by norm_num
lemma mod4_911 : 911 % 4 = 3 := by decide
lemma prime_919 : Nat.Prime 919 := by norm_num
lemma mod4_919 : 919 % 4 = 3 := by decide
lemma prime_947 : Nat.Prime 947 := by norm_num
lemma mod4_947 : 947 % 4 = 3 := by decide
lemma prime_967 : Nat.Prime 967 := by norm_num
lemma mod4_967 : 967 % 4 = 3 := by decide
lemma prime_971 : Nat.Prime 971 := by norm_num
lemma mod4_971 : 971 % 4 = 3 := by decide
lemma prime_983 : Nat.Prime 983 := by norm_num
lemma mod4_983 : 983 % 4 = 3 := by decide
lemma prime_991 : Nat.Prime 991 := by norm_num
lemma mod4_991 : 991 % 4 = 3 := by decide
lemma prime_1019 : Nat.Prime 1019 := by norm_num
lemma mod4_1019 : 1019 % 4 = 3 := by decide
lemma prime_1031 : Nat.Prime 1031 := by norm_num
lemma mod4_1031 : 1031 % 4 = 3 := by decide
lemma prime_1039 : Nat.Prime 1039 := by norm_num
lemma mod4_1039 : 1039 % 4 = 3 := by decide
lemma prime_1051 : Nat.Prime 1051 := by norm_num
lemma mod4_1051 : 1051 % 4 = 3 := by decide
lemma prime_1063 : Nat.Prime 1063 := by norm_num
lemma mod4_1063 : 1063 % 4 = 3 := by decide
lemma prime_1087 : Nat.Prime 1087 := by norm_num
lemma mod4_1087 : 1087 % 4 = 3 := by decide
lemma prime_1091 : Nat.Prime 1091 := by norm_num
lemma mod4_1091 : 1091 % 4 = 3 := by decide
lemma prime_1103 : Nat.Prime 1103 := by norm_num
lemma mod4_1103 : 1103 % 4 = 3 := by decide
lemma prime_1123 : Nat.Prime 1123 := by norm_num
lemma mod4_1123 : 1123 % 4 = 3 := by decide
lemma prime_1151 : Nat.Prime 1151 := by norm_num
lemma mod4_1151 : 1151 % 4 = 3 := by decide
lemma prime_1163 : Nat.Prime 1163 := by norm_num
lemma mod4_1163 : 1163 % 4 = 3 := by decide
lemma prime_1171 : Nat.Prime 1171 := by norm_num
lemma mod4_1171 : 1171 % 4 = 3 := by decide
lemma prime_1187 : Nat.Prime 1187 := by norm_num
lemma mod4_1187 : 1187 % 4 = 3 := by decide
lemma prime_1223 : Nat.Prime 1223 := by norm_num
lemma mod4_1223 : 1223 % 4 = 3 := by decide
lemma prime_1231 : Nat.Prime 1231 := by norm_num
lemma mod4_1231 : 1231 % 4 = 3 := by decide
lemma prime_1259 : Nat.Prime 1259 := by norm_num
lemma mod4_1259 : 1259 % 4 = 3 := by decide
lemma prime_1279 : Nat.Prime 1279 := by norm_num
lemma mod4_1279 : 1279 % 4 = 3 := by decide
lemma prime_1283 : Nat.Prime 1283 := by norm_num
lemma mod4_1283 : 1283 % 4 = 3 := by decide
lemma prime_1291 : Nat.Prime 1291 := by norm_num
lemma mod4_1291 : 1291 % 4 = 3 := by decide
lemma prime_1303 : Nat.Prime 1303 := by norm_num
lemma mod4_1303 : 1303 % 4 = 3 := by decide
lemma prime_1307 : Nat.Prime 1307 := by norm_num
lemma mod4_1307 : 1307 % 4 = 3 := by decide
lemma prime_1319 : Nat.Prime 1319 := by norm_num
lemma mod4_1319 : 1319 % 4 = 3 := by decide
lemma prime_1327 : Nat.Prime 1327 := by norm_num
lemma mod4_1327 : 1327 % 4 = 3 := by decide
lemma prime_1367 : Nat.Prime 1367 := by norm_num
lemma mod4_1367 : 1367 % 4 = 3 := by decide
lemma prime_1399 : Nat.Prime 1399 := by norm_num
lemma mod4_1399 : 1399 % 4 = 3 := by decide
lemma prime_1423 : Nat.Prime 1423 := by norm_num
lemma mod4_1423 : 1423 % 4 = 3 := by decide
lemma prime_1427 : Nat.Prime 1427 := by norm_num
lemma mod4_1427 : 1427 % 4 = 3 := by decide
lemma prime_1439 : Nat.Prime 1439 := by norm_num
lemma mod4_1439 : 1439 % 4 = 3 := by decide
lemma prime_1447 : Nat.Prime 1447 := by norm_num
lemma mod4_1447 : 1447 % 4 = 3 := by decide
lemma prime_1451 : Nat.Prime 1451 := by norm_num
lemma mod4_1451 : 1451 % 4 = 3 := by decide
lemma prime_1459 : Nat.Prime 1459 := by norm_num
lemma mod4_1459 : 1459 % 4 = 3 := by decide
lemma prime_1471 : Nat.Prime 1471 := by norm_num
lemma mod4_1471 : 1471 % 4 = 3 := by decide
lemma prime_1483 : Nat.Prime 1483 := by norm_num
lemma mod4_1483 : 1483 % 4 = 3 := by decide
lemma prime_1487 : Nat.Prime 1487 := by norm_num
lemma mod4_1487 : 1487 % 4 = 3 := by decide
lemma prime_1499 : Nat.Prime 1499 := by norm_num
lemma mod4_1499 : 1499 % 4 = 3 := by decide
lemma prime_1511 : Nat.Prime 1511 := by norm_num
lemma mod4_1511 : 1511 % 4 = 3 := by decide
lemma prime_1523 : Nat.Prime 1523 := by norm_num
lemma mod4_1523 : 1523 % 4 = 3 := by decide
lemma prime_1531 : Nat.Prime 1531 := by norm_num
lemma mod4_1531 : 1531 % 4 = 3 := by decide
lemma prime_1543 : Nat.Prime 1543 := by norm_num
lemma mod4_1543 : 1543 % 4 = 3 := by decide
lemma prime_1559 : Nat.Prime 1559 := by norm_num
lemma mod4_1559 : 1559 % 4 = 3 := by decide
lemma prime_1567 : Nat.Prime 1567 := by norm_num
lemma mod4_1567 : 1567 % 4 = 3 := by decide
lemma prime_1571 : Nat.Prime 1571 := by norm_num
lemma mod4_1571 : 1571 % 4 = 3 := by decide
lemma prime_1579 : Nat.Prime 1579 := by norm_num
lemma mod4_1579 : 1579 % 4 = 3 := by decide
lemma prime_1583 : Nat.Prime 1583 := by norm_num
lemma mod4_1583 : 1583 % 4 = 3 := by decide
lemma prime_1607 : Nat.Prime 1607 := by norm_num
lemma mod4_1607 : 1607 % 4 = 3 := by decide
lemma prime_1619 : Nat.Prime 1619 := by norm_num
lemma mod4_1619 : 1619 % 4 = 3 := by decide
lemma prime_1627 : Nat.Prime 1627 := by norm_num
lemma mod4_1627 : 1627 % 4 = 3 := by decide
lemma prime_1663 : Nat.Prime 1663 := by norm_num
lemma mod4_1663 : 1663 % 4 = 3 := by decide
lemma prime_1667 : Nat.Prime 1667 := by norm_num
lemma mod4_1667 : 1667 % 4 = 3 := by decide
lemma prime_1699 : Nat.Prime 1699 := by norm_num
lemma mod4_1699 : 1699 % 4 = 3 := by decide
lemma prime_1723 : Nat.Prime 1723 := by norm_num
lemma mod4_1723 : 1723 % 4 = 3 := by decide
lemma prime_1747 : Nat.Prime 1747 := by norm_num
lemma mod4_1747 : 1747 % 4 = 3 := by decide
lemma prime_1759 : Nat.Prime 1759 := by norm_num
lemma mod4_1759 : 1759 % 4 = 3 := by decide
lemma prime_1783 : Nat.Prime 1783 := by norm_num
lemma mod4_1783 : 1783 % 4 = 3 := by decide
lemma prime_1787 : Nat.Prime 1787 := by norm_num
lemma mod4_1787 : 1787 % 4 = 3 := by decide
lemma prime_1811 : Nat.Prime 1811 := by norm_num
lemma mod4_1811 : 1811 % 4 = 3 := by decide
lemma prime_1823 : Nat.Prime 1823 := by norm_num
lemma mod4_1823 : 1823 % 4 = 3 := by decide
lemma prime_1831 : Nat.Prime 1831 := by norm_num
lemma mod4_1831 : 1831 % 4 = 3 := by decide
lemma prime_1847 : Nat.Prime 1847 := by norm_num
lemma mod4_1847 : 1847 % 4 = 3 := by decide
lemma prime_1867 : Nat.Prime 1867 := by norm_num
lemma mod4_1867 : 1867 % 4 = 3 := by decide
lemma prime_1871 : Nat.Prime 1871 := by norm_num
lemma mod4_1871 : 1871 % 4 = 3 := by decide
lemma prime_1879 : Nat.Prime 1879 := by norm_num
lemma mod4_1879 : 1879 % 4 = 3 := by decide
lemma prime_1907 : Nat.Prime 1907 := by norm_num
lemma mod4_1907 : 1907 % 4 = 3 := by decide
lemma prime_1931 : Nat.Prime 1931 := by norm_num
lemma mod4_1931 : 1931 % 4 = 3 := by decide
lemma prime_1951 : Nat.Prime 1951 := by norm_num
lemma mod4_1951 : 1951 % 4 = 3 := by decide
lemma prime_1979 : Nat.Prime 1979 := by norm_num
lemma mod4_1979 : 1979 % 4 = 3 := by decide
lemma prime_1987 : Nat.Prime 1987 := by norm_num
lemma mod4_1987 : 1987 % 4 = 3 := by decide
lemma prime_1999 : Nat.Prime 1999 := by norm_num
lemma mod4_1999 : 1999 % 4 = 3 := by decide
lemma prime_2003 : Nat.Prime 2003 := by norm_num
lemma mod4_2003 : 2003 % 4 = 3 := by decide
lemma prime_2011 : Nat.Prime 2011 := by norm_num
lemma mod4_2011 : 2011 % 4 = 3 := by decide
lemma prime_2027 : Nat.Prime 2027 := by norm_num
lemma mod4_2027 : 2027 % 4 = 3 := by decide
lemma prime_2039 : Nat.Prime 2039 := by norm_num
lemma mod4_2039 : 2039 % 4 = 3 := by decide
lemma prime_2063 : Nat.Prime 2063 := by norm_num
lemma mod4_2063 : 2063 % 4 = 3 := by decide
lemma prime_2083 : Nat.Prime 2083 := by norm_num
lemma mod4_2083 : 2083 % 4 = 3 := by decide
lemma prime_2087 : Nat.Prime 2087 := by norm_num
lemma mod4_2087 : 2087 % 4 = 3 := by decide
lemma prime_2099 : Nat.Prime 2099 := by norm_num
lemma mod4_2099 : 2099 % 4 = 3 := by decide
lemma prime_2111 : Nat.Prime 2111 := by norm_num
lemma mod4_2111 : 2111 % 4 = 3 := by decide
lemma prime_2131 : Nat.Prime 2131 := by norm_num
lemma mod4_2131 : 2131 % 4 = 3 := by decide
lemma prime_2143 : Nat.Prime 2143 := by norm_num
lemma mod4_2143 : 2143 % 4 = 3 := by decide
lemma prime_2179 : Nat.Prime 2179 := by norm_num
lemma mod4_2179 : 2179 % 4 = 3 := by decide
lemma prime_2203 : Nat.Prime 2203 := by norm_num
lemma mod4_2203 : 2203 % 4 = 3 := by decide
lemma prime_2207 : Nat.Prime 2207 := by norm_num
lemma mod4_2207 : 2207 % 4 = 3 := by decide
lemma prime_2239 : Nat.Prime 2239 := by norm_num
lemma mod4_2239 : 2239 % 4 = 3 := by decide
lemma prime_2243 : Nat.Prime 2243 := by norm_num
lemma mod4_2243 : 2243 % 4 = 3 := by decide
lemma prime_2251 : Nat.Prime 2251 := by norm_num
lemma mod4_2251 : 2251 % 4 = 3 := by decide
lemma prime_2267 : Nat.Prime 2267 := by norm_num
lemma mod4_2267 : 2267 % 4 = 3 := by decide
lemma prime_2287 : Nat.Prime 2287 := by norm_num
lemma mod4_2287 : 2287 % 4 = 3 := by decide
lemma prime_2311 : Nat.Prime 2311 := by norm_num
lemma mod4_2311 : 2311 % 4 = 3 := by decide
lemma prime_2339 : Nat.Prime 2339 := by norm_num
lemma mod4_2339 : 2339 % 4 = 3 := by decide
lemma prime_2347 : Nat.Prime 2347 := by norm_num
lemma mod4_2347 : 2347 % 4 = 3 := by decide
lemma prime_2351 : Nat.Prime 2351 := by norm_num
lemma mod4_2351 : 2351 % 4 = 3 := by decide
lemma prime_2371 : Nat.Prime 2371 := by norm_num
lemma mod4_2371 : 2371 % 4 = 3 := by decide
lemma prime_2383 : Nat.Prime 2383 := by norm_num
lemma mod4_2383 : 2383 % 4 = 3 := by decide
lemma prime_2399 : Nat.Prime 2399 := by norm_num
lemma mod4_2399 : 2399 % 4 = 3 := by decide
lemma prime_2411 : Nat.Prime 2411 := by norm_num
lemma mod4_2411 : 2411 % 4 = 3 := by decide
lemma prime_2423 : Nat.Prime 2423 := by norm_num
lemma mod4_2423 : 2423 % 4 = 3 := by decide
lemma prime_2447 : Nat.Prime 2447 := by norm_num
lemma mod4_2447 : 2447 % 4 = 3 := by decide
lemma prime_2459 : Nat.Prime 2459 := by norm_num
lemma mod4_2459 : 2459 % 4 = 3 := by decide
lemma prime_2467 : Nat.Prime 2467 := by norm_num
lemma mod4_2467 : 2467 % 4 = 3 := by decide
lemma prime_2503 : Nat.Prime 2503 := by norm_num
lemma mod4_2503 : 2503 % 4 = 3 := by decide
lemma prime_2531 : Nat.Prime 2531 := by norm_num
lemma mod4_2531 : 2531 % 4 = 3 := by decide
lemma prime_2539 : Nat.Prime 2539 := by norm_num
lemma mod4_2539 : 2539 % 4 = 3 := by decide
lemma prime_2543 : Nat.Prime 2543 := by norm_num
lemma mod4_2543 : 2543 % 4 = 3 := by decide
lemma prime_2551 : Nat.Prime 2551 := by norm_num
lemma mod4_2551 : 2551 % 4 = 3 := by decide
lemma prime_2579 : Nat.Prime 2579 := by norm_num
lemma mod4_2579 : 2579 % 4 = 3 := by decide
lemma prime_2591 : Nat.Prime 2591 := by norm_num
lemma mod4_2591 : 2591 % 4 = 3 := by decide
lemma prime_2647 : Nat.Prime 2647 := by norm_num
lemma mod4_2647 : 2647 % 4 = 3 := by decide
lemma prime_2659 : Nat.Prime 2659 := by norm_num
lemma mod4_2659 : 2659 % 4 = 3 := by decide
lemma prime_2663 : Nat.Prime 2663 := by norm_num
lemma mod4_2663 : 2663 % 4 = 3 := by decide
lemma prime_2671 : Nat.Prime 2671 := by norm_num
lemma mod4_2671 : 2671 % 4 = 3 := by decide
lemma prime_2683 : Nat.Prime 2683 := by norm_num
lemma mod4_2683 : 2683 % 4 = 3 := by decide
lemma prime_2687 : Nat.Prime 2687 := by norm_num
lemma mod4_2687 : 2687 % 4 = 3 := by decide
lemma prime_2699 : Nat.Prime 2699 := by norm_num
lemma mod4_2699 : 2699 % 4 = 3 := by decide
lemma prime_2707 : Nat.Prime 2707 := by norm_num
lemma mod4_2707 : 2707 % 4 = 3 := by decide
lemma prime_2711 : Nat.Prime 2711 := by norm_num
lemma mod4_2711 : 2711 % 4 = 3 := by decide
lemma prime_2719 : Nat.Prime 2719 := by norm_num
lemma mod4_2719 : 2719 % 4 = 3 := by decide
lemma prime_2731 : Nat.Prime 2731 := by norm_num
lemma mod4_2731 : 2731 % 4 = 3 := by decide
lemma prime_2767 : Nat.Prime 2767 := by norm_num
lemma mod4_2767 : 2767 % 4 = 3 := by decide
lemma prime_2791 : Nat.Prime 2791 := by norm_num
lemma mod4_2791 : 2791 % 4 = 3 := by decide
lemma prime_2803 : Nat.Prime 2803 := by norm_num
lemma mod4_2803 : 2803 % 4 = 3 := by decide
lemma prime_2819 : Nat.Prime 2819 := by norm_num
lemma mod4_2819 : 2819 % 4 = 3 := by decide
lemma prime_2843 : Nat.Prime 2843 := by norm_num
lemma mod4_2843 : 2843 % 4 = 3 := by decide
lemma prime_2851 : Nat.Prime 2851 := by norm_num
lemma mod4_2851 : 2851 % 4 = 3 := by decide
lemma prime_2879 : Nat.Prime 2879 := by norm_num
lemma mod4_2879 : 2879 % 4 = 3 := by decide
lemma prime_2887 : Nat.Prime 2887 := by norm_num
lemma mod4_2887 : 2887 % 4 = 3 := by decide
lemma prime_2903 : Nat.Prime 2903 := by norm_num
lemma mod4_2903 : 2903 % 4 = 3 := by decide
lemma prime_2927 : Nat.Prime 2927 := by norm_num
lemma mod4_2927 : 2927 % 4 = 3 := by decide
lemma prime_2939 : Nat.Prime 2939 := by norm_num
lemma mod4_2939 : 2939 % 4 = 3 := by decide
lemma prime_2963 : Nat.Prime 2963 := by norm_num
lemma mod4_2963 : 2963 % 4 = 3 := by decide
lemma prime_2971 : Nat.Prime 2971 := by norm_num
lemma mod4_2971 : 2971 % 4 = 3 := by decide
lemma prime_2999 : Nat.Prime 2999 := by norm_num
lemma mod4_2999 : 2999 % 4 = 3 := by decide
lemma prime_3011 : Nat.Prime 3011 := by norm_num
lemma mod4_3011 : 3011 % 4 = 3 := by decide
lemma prime_3019 : Nat.Prime 3019 := by norm_num
lemma mod4_3019 : 3019 % 4 = 3 := by decide
lemma prime_3023 : Nat.Prime 3023 := by norm_num
lemma mod4_3023 : 3023 % 4 = 3 := by decide
lemma prime_3067 : Nat.Prime 3067 := by norm_num
lemma mod4_3067 : 3067 % 4 = 3 := by decide
lemma prime_3079 : Nat.Prime 3079 := by norm_num
lemma mod4_3079 : 3079 % 4 = 3 := by decide
lemma prime_3083 : Nat.Prime 3083 := by norm_num
lemma mod4_3083 : 3083 % 4 = 3 := by decide
lemma prime_3119 : Nat.Prime 3119 := by norm_num
lemma mod4_3119 : 3119 % 4 = 3 := by decide
lemma prime_3163 : Nat.Prime 3163 := by norm_num
lemma mod4_3163 : 3163 % 4 = 3 := by decide
lemma prime_3167 : Nat.Prime 3167 := by norm_num
lemma mod4_3167 : 3167 % 4 = 3 := by decide
lemma prime_3187 : Nat.Prime 3187 := by norm_num
lemma mod4_3187 : 3187 % 4 = 3 := by decide
lemma prime_3191 : Nat.Prime 3191 := by norm_num
lemma mod4_3191 : 3191 % 4 = 3 := by decide
lemma prime_3203 : Nat.Prime 3203 := by norm_num
lemma mod4_3203 : 3203 % 4 = 3 := by decide
lemma prime_3251 : Nat.Prime 3251 := by norm_num
lemma mod4_3251 : 3251 % 4 = 3 := by decide
lemma prime_3259 : Nat.Prime 3259 := by norm_num
lemma mod4_3259 : 3259 % 4 = 3 := by decide
lemma prime_3271 : Nat.Prime 3271 := by norm_num
lemma mod4_3271 : 3271 % 4 = 3 := by decide
lemma prime_3299 : Nat.Prime 3299 := by norm_num
lemma mod4_3299 : 3299 % 4 = 3 := by decide
lemma prime_3307 : Nat.Prime 3307 := by norm_num
lemma mod4_3307 : 3307 % 4 = 3 := by decide
lemma prime_3319 : Nat.Prime 3319 := by norm_num
lemma mod4_3319 : 3319 % 4 = 3 := by decide
lemma prime_3323 : Nat.Prime 3323 := by norm_num
lemma mod4_3323 : 3323 % 4 = 3 := by decide
lemma prime_3331 : Nat.Prime 3331 := by norm_num
lemma mod4_3331 : 3331 % 4 = 3 := by decide
lemma prime_3343 : Nat.Prime 3343 := by norm_num
lemma mod4_3343 : 3343 % 4 = 3 := by decide
lemma prime_3347 : Nat.Prime 3347 := by norm_num
lemma mod4_3347 : 3347 % 4 = 3 := by decide
lemma prime_3359 : Nat.Prime 3359 := by norm_num
lemma mod4_3359 : 3359 % 4 = 3 := by decide
lemma prime_3371 : Nat.Prime 3371 := by norm_num
lemma mod4_3371 : 3371 % 4 = 3 := by decide
lemma prime_3391 : Nat.Prime 3391 := by norm_num
lemma mod4_3391 : 3391 % 4 = 3 := by decide
lemma prime_3407 : Nat.Prime 3407 := by norm_num
lemma mod4_3407 : 3407 % 4 = 3 := by decide
lemma prime_3463 : Nat.Prime 3463 := by norm_num
lemma mod4_3463 : 3463 % 4 = 3 := by decide
lemma prime_3467 : Nat.Prime 3467 := by norm_num
lemma mod4_3467 : 3467 % 4 = 3 := by decide
lemma prime_3491 : Nat.Prime 3491 := by norm_num
lemma mod4_3491 : 3491 % 4 = 3 := by decide
lemma prime_3499 : Nat.Prime 3499 := by norm_num
lemma mod4_3499 : 3499 % 4 = 3 := by decide
lemma prime_3511 : Nat.Prime 3511 := by norm_num
lemma mod4_3511 : 3511 % 4 = 3 := by decide
lemma prime_3527 : Nat.Prime 3527 := by norm_num
lemma mod4_3527 : 3527 % 4 = 3 := by decide
lemma prime_3539 : Nat.Prime 3539 := by norm_num
lemma mod4_3539 : 3539 % 4 = 3 := by decide
lemma prime_3547 : Nat.Prime 3547 := by norm_num
lemma mod4_3547 : 3547 % 4 = 3 := by decide
lemma prime_3559 : Nat.Prime 3559 := by norm_num
lemma mod4_3559 : 3559 % 4 = 3 := by decide
lemma prime_3571 : Nat.Prime 3571 := by norm_num
lemma mod4_3571 : 3571 % 4 = 3 := by decide
lemma prime_3583 : Nat.Prime 3583 := by norm_num
lemma mod4_3583 : 3583 % 4 = 3 := by decide
lemma prime_3607 : Nat.Prime 3607 := by norm_num
lemma mod4_3607 : 3607 % 4 = 3 := by decide
lemma prime_3623 : Nat.Prime 3623 := by norm_num
lemma mod4_3623 : 3623 % 4 = 3 := by decide
lemma prime_3631 : Nat.Prime 3631 := by norm_num
lemma mod4_3631 : 3631 % 4 = 3 := by decide
lemma prime_3643 : Nat.Prime 3643 := by norm_num
lemma mod4_3643 : 3643 % 4 = 3 := by decide
lemma prime_3659 : Nat.Prime 3659 := by norm_num
lemma mod4_3659 : 3659 % 4 = 3 := by decide
lemma prime_3671 : Nat.Prime 3671 := by norm_num
lemma mod4_3671 : 3671 % 4 = 3 := by decide
lemma prime_3691 : Nat.Prime 3691 := by norm_num
lemma mod4_3691 : 3691 % 4 = 3 := by decide
lemma prime_3719 : Nat.Prime 3719 := by norm_num
lemma mod4_3719 : 3719 % 4 = 3 := by decide
lemma prime_3727 : Nat.Prime 3727 := by norm_num
lemma mod4_3727 : 3727 % 4 = 3 := by decide
lemma prime_3739 : Nat.Prime 3739 := by norm_num
lemma mod4_3739 : 3739 % 4 = 3 := by decide
lemma prime_3767 : Nat.Prime 3767 := by norm_num
lemma mod4_3767 : 3767 % 4 = 3 := by decide
lemma prime_3779 : Nat.Prime 3779 := by norm_num
lemma mod4_3779 : 3779 % 4 = 3 := by decide
lemma prime_3803 : Nat.Prime 3803 := by norm_num
lemma mod4_3803 : 3803 % 4 = 3 := by decide
lemma prime_3823 : Nat.Prime 3823 := by norm_num
lemma mod4_3823 : 3823 % 4 = 3 := by decide
lemma prime_3847 : Nat.Prime 3847 := by norm_num
lemma mod4_3847 : 3847 % 4 = 3 := by decide
lemma prime_3851 : Nat.Prime 3851 := by norm_num
lemma mod4_3851 : 3851 % 4 = 3 := by decide
lemma prime_3863 : Nat.Prime 3863 := by norm_num
lemma mod4_3863 : 3863 % 4 = 3 := by decide
lemma prime_3907 : Nat.Prime 3907 := by norm_num
lemma mod4_3907 : 3907 % 4 = 3 := by decide
lemma prime_3911 : Nat.Prime 3911 := by norm_num
lemma mod4_3911 : 3911 % 4 = 3 := by decide
lemma prime_3919 : Nat.Prime 3919 := by norm_num
lemma mod4_3919 : 3919 % 4 = 3 := by decide
lemma prime_3923 : Nat.Prime 3923 := by norm_num
lemma mod4_3923 : 3923 % 4 = 3 := by decide
lemma prime_3931 : Nat.Prime 3931 := by norm_num
lemma mod4_3931 : 3931 % 4 = 3 := by decide
lemma prime_3943 : Nat.Prime 3943 := by norm_num
lemma mod4_3943 : 3943 % 4 = 3 := by decide
lemma prime_3947 : Nat.Prime 3947 := by norm_num
lemma mod4_3947 : 3947 % 4 = 3 := by decide
lemma prime_3967 : Nat.Prime 3967 := by norm_num
lemma mod4_3967 : 3967 % 4 = 3 := by decide
lemma prime_4003 : Nat.Prime 4003 := by norm_num
lemma mod4_4003 : 4003 % 4 = 3 := by decide
lemma prime_4007 : Nat.Prime 4007 := by norm_num
lemma mod4_4007 : 4007 % 4 = 3 := by decide
lemma prime_4019 : Nat.Prime 4019 := by norm_num
lemma mod4_4019 : 4019 % 4 = 3 := by decide
lemma prime_4027 : Nat.Prime 4027 := by norm_num
lemma mod4_4027 : 4027 % 4 = 3 := by decide
lemma prime_4051 : Nat.Prime 4051 := by norm_num
lemma mod4_4051 : 4051 % 4 = 3 := by decide
lemma prime_4079 : Nat.Prime 4079 := by norm_num
lemma mod4_4079 : 4079 % 4 = 3 := by decide
lemma prime_4091 : Nat.Prime 4091 := by norm_num
lemma mod4_4091 : 4091 % 4 = 3 := by decide
lemma prime_4099 : Nat.Prime 4099 := by norm_num
lemma mod4_4099 : 4099 % 4 = 3 := by decide
lemma prime_4111 : Nat.Prime 4111 := by norm_num
lemma mod4_4111 : 4111 % 4 = 3 := by decide
lemma prime_4127 : Nat.Prime 4127 := by norm_num
lemma mod4_4127 : 4127 % 4 = 3 := by decide
lemma prime_4139 : Nat.Prime 4139 := by norm_num
lemma mod4_4139 : 4139 % 4 = 3 := by decide
lemma prime_4159 : Nat.Prime 4159 := by norm_num
lemma mod4_4159 : 4159 % 4 = 3 := by decide
lemma prime_4211 : Nat.Prime 4211 := by norm_num
lemma mod4_4211 : 4211 % 4 = 3 := by decide
lemma prime_4219 : Nat.Prime 4219 := by norm_num
lemma mod4_4219 : 4219 % 4 = 3 := by decide
lemma prime_4231 : Nat.Prime 4231 := by norm_num
lemma mod4_4231 : 4231 % 4 = 3 := by decide
lemma prime_4243 : Nat.Prime 4243 := by norm_num
lemma mod4_4243 : 4243 % 4 = 3 := by decide
lemma prime_4259 : Nat.Prime 4259 := by norm_num
lemma mod4_4259 : 4259 % 4 = 3 := by decide
lemma prime_4271 : Nat.Prime 4271 := by norm_num
lemma mod4_4271 : 4271 % 4 = 3 := by decide
lemma prime_4283 : Nat.Prime 4283 := by norm_num
lemma mod4_4283 : 4283 % 4 = 3 := by decide
lemma prime_4327 : Nat.Prime 4327 := by norm_num
lemma mod4_4327 : 4327 % 4 = 3 := by decide
lemma prime_4339 : Nat.Prime 4339 := by norm_num
lemma mod4_4339 : 4339 % 4 = 3 := by decide
lemma prime_4363 : Nat.Prime 4363 := by norm_num
lemma mod4_4363 : 4363 % 4 = 3 := by decide
lemma prime_4391 : Nat.Prime 4391 := by norm_num
lemma mod4_4391 : 4391 % 4 = 3 := by decide
lemma prime_4423 : Nat.Prime 4423 := by norm_num
lemma mod4_4423 : 4423 % 4 = 3 := by decide
lemma prime_4447 : Nat.Prime 4447 := by norm_num
lemma mod4_4447 : 4447 % 4 = 3 := by decide
lemma prime_4451 : Nat.Prime 4451 := by norm_num
lemma mod4_4451 : 4451 % 4 = 3 := by decide
lemma prime_4463 : Nat.Prime 4463 := by norm_num
lemma mod4_4463 : 4463 % 4 = 3 := by decide
lemma prime_4483 : Nat.Prime 4483 := by norm_num
lemma mod4_4483 : 4483 % 4 = 3 := by decide
lemma prime_4507 : Nat.Prime 4507 := by norm_num
lemma mod4_4507 : 4507 % 4 = 3 := by decide
lemma prime_4519 : Nat.Prime 4519 := by norm_num
lemma mod4_4519 : 4519 % 4 = 3 := by decide
lemma prime_4523 : Nat.Prime 4523 := by norm_num
lemma mod4_4523 : 4523 % 4 = 3 := by decide
lemma prime_4547 : Nat.Prime 4547 := by norm_num
lemma mod4_4547 : 4547 % 4 = 3 := by decide
lemma prime_4567 : Nat.Prime 4567 := by norm_num
lemma mod4_4567 : 4567 % 4 = 3 := by decide
lemma prime_4583 : Nat.Prime 4583 := by norm_num
lemma mod4_4583 : 4583 % 4 = 3 := by decide
lemma prime_4591 : Nat.Prime 4591 := by norm_num
lemma mod4_4591 : 4591 % 4 = 3 := by decide
lemma prime_4603 : Nat.Prime 4603 := by norm_num
lemma mod4_4603 : 4603 % 4 = 3 := by decide
lemma prime_4639 : Nat.Prime 4639 := by norm_num
lemma mod4_4639 : 4639 % 4 = 3 := by decide
lemma prime_4643 : Nat.Prime 4643 := by norm_num
lemma mod4_4643 : 4643 % 4 = 3 := by decide
lemma prime_4651 : Nat.Prime 4651 := by norm_num
lemma mod4_4651 : 4651 % 4 = 3 := by decide
lemma prime_4663 : Nat.Prime 4663 := by norm_num
lemma mod4_4663 : 4663 % 4 = 3 := by decide
lemma prime_4679 : Nat.Prime 4679 := by norm_num
lemma mod4_4679 : 4679 % 4 = 3 := by decide
lemma prime_4691 : Nat.Prime 4691 := by norm_num
lemma mod4_4691 : 4691 % 4 = 3 := by decide
lemma prime_4703 : Nat.Prime 4703 := by norm_num
lemma mod4_4703 : 4703 % 4 = 3 := by decide
lemma prime_4723 : Nat.Prime 4723 := by norm_num
lemma mod4_4723 : 4723 % 4 = 3 := by decide
lemma prime_4751 : Nat.Prime 4751 := by norm_num
lemma mod4_4751 : 4751 % 4 = 3 := by decide
lemma prime_4759 : Nat.Prime 4759 := by norm_num
lemma mod4_4759 : 4759 % 4 = 3 := by decide
lemma prime_4783 : Nat.Prime 4783 := by norm_num
lemma mod4_4783 : 4783 % 4 = 3 := by decide
lemma prime_4787 : Nat.Prime 4787 := by norm_num
lemma mod4_4787 : 4787 % 4 = 3 := by decide
lemma prime_4799 : Nat.Prime 4799 := by norm_num
lemma mod4_4799 : 4799 % 4 = 3 := by decide
lemma prime_4831 : Nat.Prime 4831 := by norm_num
lemma mod4_4831 : 4831 % 4 = 3 := by decide
lemma prime_4871 : Nat.Prime 4871 := by norm_num
lemma mod4_4871 : 4871 % 4 = 3 := by decide
lemma prime_4903 : Nat.Prime 4903 := by norm_num
lemma mod4_4903 : 4903 % 4 = 3 := by decide
lemma prime_4919 : Nat.Prime 4919 := by norm_num
lemma mod4_4919 : 4919 % 4 = 3 := by decide
lemma prime_4931 : Nat.Prime 4931 := by norm_num
lemma mod4_4931 : 4931 % 4 = 3 := by decide
lemma prime_4943 : Nat.Prime 4943 := by norm_num
lemma mod4_4943 : 4943 % 4 = 3 := by decide
lemma prime_4951 : Nat.Prime 4951 := by norm_num
lemma mod4_4951 : 4951 % 4 = 3 := by decide
lemma prime_4967 : Nat.Prime 4967 := by norm_num
lemma mod4_4967 : 4967 % 4 = 3 := by decide
lemma prime_4987 : Nat.Prime 4987 := by norm_num
lemma mod4_4987 : 4987 % 4 = 3 := by decide
lemma prime_4999 : Nat.Prime 4999 := by norm_num
lemma mod4_4999 : 4999 % 4 = 3 := by decide
lemma prime_5003 : Nat.Prime 5003 := by norm_num
lemma mod4_5003 : 5003 % 4 = 3 := by decide
lemma prime_5011 : Nat.Prime 5011 := by norm_num
lemma mod4_5011 : 5011 % 4 = 3 := by decide
lemma prime_5023 : Nat.Prime 5023 := by norm_num
lemma mod4_5023 : 5023 % 4 = 3 := by decide
lemma prime_5039 : Nat.Prime 5039 := by norm_num
lemma mod4_5039 : 5039 % 4 = 3 := by decide
lemma prime_5051 : Nat.Prime 5051 := by norm_num
lemma mod4_5051 : 5051 % 4 = 3 := by decide
lemma prime_5059 : Nat.Prime 5059 := by norm_num
lemma mod4_5059 : 5059 % 4 = 3 := by decide
lemma prime_5087 : Nat.Prime 5087 := by norm_num
lemma mod4_5087 : 5087 % 4 = 3 := by decide
lemma prime_5099 : Nat.Prime 5099 := by norm_num
lemma mod4_5099 : 5099 % 4 = 3 := by decide
lemma prime_5107 : Nat.Prime 5107 := by norm_num
lemma mod4_5107 : 5107 % 4 = 3 := by decide
lemma prime_5119 : Nat.Prime 5119 := by norm_num
lemma mod4_5119 : 5119 % 4 = 3 := by decide
lemma prime_5147 : Nat.Prime 5147 := by norm_num
lemma mod4_5147 : 5147 % 4 = 3 := by decide
lemma prime_5167 : Nat.Prime 5167 := by norm_num
lemma mod4_5167 : 5167 % 4 = 3 := by decide
lemma prime_5171 : Nat.Prime 5171 := by norm_num
lemma mod4_5171 : 5171 % 4 = 3 := by decide
lemma prime_5179 : Nat.Prime 5179 := by norm_num
lemma mod4_5179 : 5179 % 4 = 3 := by decide
lemma prime_5227 : Nat.Prime 5227 := by norm_num
lemma mod4_5227 : 5227 % 4 = 3 := by decide
lemma prime_5231 : Nat.Prime 5231 := by norm_num
lemma mod4_5231 : 5231 % 4 = 3 := by decide
lemma prime_5279 : Nat.Prime 5279 := by norm_num
lemma mod4_5279 : 5279 % 4 = 3 := by decide
lemma prime_5303 : Nat.Prime 5303 := by norm_num
lemma mod4_5303 : 5303 % 4 = 3 := by decide
lemma prime_5323 : Nat.Prime 5323 := by norm_num
lemma mod4_5323 : 5323 % 4 = 3 := by decide
lemma prime_5347 : Nat.Prime 5347 := by norm_num
lemma mod4_5347 : 5347 % 4 = 3 := by decide
lemma prime_5351 : Nat.Prime 5351 := by norm_num
lemma mod4_5351 : 5351 % 4 = 3 := by decide
lemma prime_5387 : Nat.Prime 5387 := by norm_num
lemma mod4_5387 : 5387 % 4 = 3 := by decide
lemma prime_5399 : Nat.Prime 5399 := by norm_num
lemma mod4_5399 : 5399 % 4 = 3 := by decide
lemma prime_5407 : Nat.Prime 5407 := by norm_num
lemma mod4_5407 : 5407 % 4 = 3 := by decide
lemma prime_5419 : Nat.Prime 5419 := by norm_num
lemma mod4_5419 : 5419 % 4 = 3 := by decide
lemma prime_5431 : Nat.Prime 5431 := by norm_num
lemma mod4_5431 : 5431 % 4 = 3 := by decide
lemma prime_5443 : Nat.Prime 5443 := by norm_num
lemma mod4_5443 : 5443 % 4 = 3 := by decide
lemma prime_5471 : Nat.Prime 5471 := by norm_num
lemma mod4_5471 : 5471 % 4 = 3 := by decide
lemma prime_5479 : Nat.Prime 5479 := by norm_num
lemma mod4_5479 : 5479 % 4 = 3 := by decide
lemma prime_5483 : Nat.Prime 5483 := by norm_num
lemma mod4_5483 : 5483 % 4 = 3 := by decide
lemma prime_5503 : Nat.Prime 5503 := by norm_num
lemma mod4_5503 : 5503 % 4 = 3 := by decide
lemma prime_5507 : Nat.Prime 5507 := by norm_num
lemma mod4_5507 : 5507 % 4 = 3 := by decide
lemma prime_5519 : Nat.Prime 5519 := by norm_num
lemma mod4_5519 : 5519 % 4 = 3 := by decide
lemma prime_5527 : Nat.Prime 5527 := by norm_num
lemma mod4_5527 : 5527 % 4 = 3 := by decide
lemma prime_5531 : Nat.Prime 5531 := by norm_num
lemma mod4_5531 : 5531 % 4 = 3 := by decide
lemma prime_5563 : Nat.Prime 5563 := by norm_num
lemma mod4_5563 : 5563 % 4 = 3 := by decide
lemma prime_5591 : Nat.Prime 5591 := by norm_num
lemma mod4_5591 : 5591 % 4 = 3 := by decide
lemma prime_5623 : Nat.Prime 5623 := by norm_num
lemma mod4_5623 : 5623 % 4 = 3 := by decide
lemma prime_5639 : Nat.Prime 5639 := by norm_num
lemma mod4_5639 : 5639 % 4 = 3 := by decide
lemma prime_5647 : Nat.Prime 5647 := by norm_num
lemma mod4_5647 : 5647 % 4 = 3 := by decide
lemma prime_5651 : Nat.Prime 5651 := by norm_num
lemma mod4_5651 : 5651 % 4 = 3 := by decide
lemma prime_5659 : Nat.Prime 5659 := by norm_num
lemma mod4_5659 : 5659 % 4 = 3 := by decide
lemma prime_5683 : Nat.Prime 5683 := by norm_num
lemma mod4_5683 : 5683 % 4 = 3 := by decide
lemma prime_5711 : Nat.Prime 5711 := by norm_num
lemma mod4_5711 : 5711 % 4 = 3 := by decide
lemma prime_5743 : Nat.Prime 5743 := by norm_num
lemma mod4_5743 : 5743 % 4 = 3 := by decide
lemma prime_5779 : Nat.Prime 5779 := by norm_num
lemma mod4_5779 : 5779 % 4 = 3 := by decide
lemma prime_5783 : Nat.Prime 5783 := by norm_num
lemma mod4_5783 : 5783 % 4 = 3 := by decide
lemma prime_5791 : Nat.Prime 5791 := by norm_num
lemma mod4_5791 : 5791 % 4 = 3 := by decide
lemma prime_5807 : Nat.Prime 5807 := by norm_num
lemma mod4_5807 : 5807 % 4 = 3 := by decide
lemma prime_5827 : Nat.Prime 5827 := by norm_num
lemma mod4_5827 : 5827 % 4 = 3 := by decide
lemma prime_5839 : Nat.Prime 5839 := by norm_num
lemma mod4_5839 : 5839 % 4 = 3 := by decide
lemma prime_5843 : Nat.Prime 5843 := by norm_num
lemma mod4_5843 : 5843 % 4 = 3 := by decide
lemma prime_5851 : Nat.Prime 5851 := by norm_num
lemma mod4_5851 : 5851 % 4 = 3 := by decide
lemma prime_5867 : Nat.Prime 5867 := by norm_num
lemma mod4_5867 : 5867 % 4 = 3 := by decide
lemma prime_5879 : Nat.Prime 5879 := by norm_num
lemma mod4_5879 : 5879 % 4 = 3 := by decide
lemma prime_5903 : Nat.Prime 5903 := by norm_num
lemma mod4_5903 : 5903 % 4 = 3 := by decide
lemma prime_5923 : Nat.Prime 5923 := by norm_num
lemma mod4_5923 : 5923 % 4 = 3 := by decide
lemma prime_5927 : Nat.Prime 5927 := by norm_num
lemma mod4_5927 : 5927 % 4 = 3 := by decide
lemma prime_5939 : Nat.Prime 5939 := by norm_num
lemma mod4_5939 : 5939 % 4 = 3 := by decide
lemma prime_5987 : Nat.Prime 5987 := by norm_num
lemma mod4_5987 : 5987 % 4 = 3 := by decide
lemma prime_6007 : Nat.Prime 6007 := by norm_num
lemma mod4_6007 : 6007 % 4 = 3 := by decide
lemma prime_6011 : Nat.Prime 6011 := by norm_num
lemma mod4_6011 : 6011 % 4 = 3 := by decide
lemma prime_6043 : Nat.Prime 6043 := by norm_num
lemma mod4_6043 : 6043 % 4 = 3 := by decide
lemma prime_6047 : Nat.Prime 6047 := by norm_num
lemma mod4_6047 : 6047 % 4 = 3 := by decide
lemma prime_6067 : Nat.Prime 6067 := by norm_num
lemma mod4_6067 : 6067 % 4 = 3 := by decide
lemma prime_6079 : Nat.Prime 6079 := by norm_num
lemma mod4_6079 : 6079 % 4 = 3 := by decide
lemma prime_6091 : Nat.Prime 6091 := by norm_num
lemma mod4_6091 : 6091 % 4 = 3 := by decide
lemma prime_6131 : Nat.Prime 6131 := by norm_num
lemma mod4_6131 : 6131 % 4 = 3 := by decide
lemma prime_6143 : Nat.Prime 6143 := by norm_num
lemma mod4_6143 : 6143 % 4 = 3 := by decide
lemma prime_6151 : Nat.Prime 6151 := by norm_num
lemma mod4_6151 : 6151 % 4 = 3 := by decide
lemma prime_6163 : Nat.Prime 6163 := by norm_num
lemma mod4_6163 : 6163 % 4 = 3 := by decide
lemma prime_6199 : Nat.Prime 6199 := by norm_num
lemma mod4_6199 : 6199 % 4 = 3 := by decide
lemma prime_6203 : Nat.Prime 6203 := by norm_num
lemma mod4_6203 : 6203 % 4 = 3 := by decide
lemma prime_6211 : Nat.Prime 6211 := by norm_num
lemma mod4_6211 : 6211 % 4 = 3 := by decide
lemma prime_6247 : Nat.Prime 6247 := by norm_num
lemma mod4_6247 : 6247 % 4 = 3 := by decide
lemma prime_6263 : Nat.Prime 6263 := by norm_num
lemma mod4_6263 : 6263 % 4 = 3 := by decide
lemma prime_6271 : Nat.Prime 6271 := by norm_num
lemma mod4_6271 : 6271 % 4 = 3 := by decide
lemma prime_6287 : Nat.Prime 6287 := by norm_num
lemma mod4_6287 : 6287 % 4 = 3 := by decide
lemma prime_6299 : Nat.Prime 6299 := by norm_num
lemma mod4_6299 : 6299 % 4 = 3 := by decide
lemma prime_6311 : Nat.Prime 6311 := by norm_num
lemma mod4_6311 : 6311 % 4 = 3 := by decide
lemma prime_6323 : Nat.Prime 6323 := by norm_num
lemma mod4_6323 : 6323 % 4 = 3 := by decide
lemma prime_6343 : Nat.Prime 6343 := by norm_num
lemma mod4_6343 : 6343 % 4 = 3 := by decide
lemma prime_6359 : Nat.Prime 6359 := by norm_num
lemma mod4_6359 : 6359 % 4 = 3 := by decide
lemma prime_6367 : Nat.Prime 6367 := by norm_num
lemma mod4_6367 : 6367 % 4 = 3 := by decide
lemma prime_6379 : Nat.Prime 6379 := by norm_num
lemma mod4_6379 : 6379 % 4 = 3 := by decide
lemma prime_6427 : Nat.Prime 6427 := by norm_num
lemma mod4_6427 : 6427 % 4 = 3 := by decide
lemma prime_6451 : Nat.Prime 6451 := by norm_num
lemma mod4_6451 : 6451 % 4 = 3 := by decide
lemma prime_6491 : Nat.Prime 6491 := by norm_num
lemma mod4_6491 : 6491 % 4 = 3 := by decide
lemma prime_6547 : Nat.Prime 6547 := by norm_num
lemma mod4_6547 : 6547 % 4 = 3 := by decide
lemma prime_6551 : Nat.Prime 6551 := by norm_num
lemma mod4_6551 : 6551 % 4 = 3 := by decide
lemma prime_6563 : Nat.Prime 6563 := by norm_num
lemma mod4_6563 : 6563 % 4 = 3 := by decide
lemma prime_6571 : Nat.Prime 6571 := by norm_num
lemma mod4_6571 : 6571 % 4 = 3 := by decide
lemma prime_6599 : Nat.Prime 6599 := by norm_num
lemma mod4_6599 : 6599 % 4 = 3 := by decide
lemma prime_6607 : Nat.Prime 6607 := by norm_num
lemma mod4_6607 : 6607 % 4 = 3 := by decide
lemma prime_6619 : Nat.Prime 6619 := by norm_num
lemma mod4_6619 : 6619 % 4 = 3 := by decide
lemma prime_6659 : Nat.Prime 6659 := by norm_num
lemma mod4_6659 : 6659 % 4 = 3 := by decide
lemma prime_6679 : Nat.Prime 6679 := by norm_num
lemma mod4_6679 : 6679 % 4 = 3 := by decide
lemma prime_6691 : Nat.Prime 6691 := by norm_num
lemma mod4_6691 : 6691 % 4 = 3 := by decide
lemma prime_6703 : Nat.Prime 6703 := by norm_num
lemma mod4_6703 : 6703 % 4 = 3 := by decide
lemma prime_6719 : Nat.Prime 6719 := by norm_num
lemma mod4_6719 : 6719 % 4 = 3 := by decide
lemma prime_6763 : Nat.Prime 6763 := by norm_num
lemma mod4_6763 : 6763 % 4 = 3 := by decide
lemma prime_6779 : Nat.Prime 6779 := by norm_num
lemma mod4_6779 : 6779 % 4 = 3 := by decide
lemma prime_6791 : Nat.Prime 6791 := by norm_num
lemma mod4_6791 : 6791 % 4 = 3 := by decide
lemma prime_6803 : Nat.Prime 6803 := by norm_num
lemma mod4_6803 : 6803 % 4 = 3 := by decide
lemma prime_6823 : Nat.Prime 6823 := by norm_num
lemma mod4_6823 : 6823 % 4 = 3 := by decide
lemma prime_6827 : Nat.Prime 6827 := by norm_num
lemma mod4_6827 : 6827 % 4 = 3 := by decide
lemma prime_6863 : Nat.Prime 6863 := by norm_num
lemma mod4_6863 : 6863 % 4 = 3 := by decide
lemma prime_6871 : Nat.Prime 6871 := by norm_num
lemma mod4_6871 : 6871 % 4 = 3 := by decide
lemma prime_6883 : Nat.Prime 6883 := by norm_num
lemma mod4_6883 : 6883 % 4 = 3 := by decide
lemma prime_6899 : Nat.Prime 6899 := by norm_num
lemma mod4_6899 : 6899 % 4 = 3 := by decide
lemma prime_6907 : Nat.Prime 6907 := by norm_num
lemma mod4_6907 : 6907 % 4 = 3 := by decide
lemma prime_6911 : Nat.Prime 6911 := by norm_num
lemma mod4_6911 : 6911 % 4 = 3 := by decide
lemma prime_6947 : Nat.Prime 6947 := by norm_num
lemma mod4_6947 : 6947 % 4 = 3 := by decide
lemma prime_6959 : Nat.Prime 6959 := by norm_num
lemma mod4_6959 : 6959 % 4 = 3 := by decide
lemma prime_6967 : Nat.Prime 6967 := by norm_num
lemma mod4_6967 : 6967 % 4 = 3 := by decide
lemma prime_6971 : Nat.Prime 6971 := by norm_num
lemma mod4_6971 : 6971 % 4 = 3 := by decide
lemma prime_6983 : Nat.Prime 6983 := by norm_num
lemma mod4_6983 : 6983 % 4 = 3 := by decide
lemma prime_6991 : Nat.Prime 6991 := by norm_num
lemma mod4_6991 : 6991 % 4 = 3 := by decide
lemma prime_7019 : Nat.Prime 7019 := by norm_num
lemma mod4_7019 : 7019 % 4 = 3 := by decide
lemma prime_7027 : Nat.Prime 7027 := by norm_num
lemma mod4_7027 : 7027 % 4 = 3 := by decide
lemma prime_7039 : Nat.Prime 7039 := by norm_num
lemma mod4_7039 : 7039 % 4 = 3 := by decide
lemma prime_7043 : Nat.Prime 7043 := by norm_num
lemma mod4_7043 : 7043 % 4 = 3 := by decide
lemma prime_7079 : Nat.Prime 7079 := by norm_num
lemma mod4_7079 : 7079 % 4 = 3 := by decide
lemma prime_7103 : Nat.Prime 7103 := by norm_num
lemma mod4_7103 : 7103 % 4 = 3 := by decide
lemma prime_7127 : Nat.Prime 7127 := by norm_num
lemma mod4_7127 : 7127 % 4 = 3 := by decide
lemma prime_7151 : Nat.Prime 7151 := by norm_num
lemma mod4_7151 : 7151 % 4 = 3 := by decide
lemma prime_7159 : Nat.Prime 7159 := by norm_num
lemma mod4_7159 : 7159 % 4 = 3 := by decide
lemma prime_7187 : Nat.Prime 7187 := by norm_num
lemma mod4_7187 : 7187 % 4 = 3 := by decide
lemma prime_7207 : Nat.Prime 7207 := by norm_num
lemma mod4_7207 : 7207 % 4 = 3 := by decide
lemma prime_7211 : Nat.Prime 7211 := by norm_num
lemma mod4_7211 : 7211 % 4 = 3 := by decide
lemma prime_7219 : Nat.Prime 7219 := by norm_num
lemma mod4_7219 : 7219 % 4 = 3 := by decide
lemma prime_7243 : Nat.Prime 7243 := by norm_num
lemma mod4_7243 : 7243 % 4 = 3 := by decide
lemma prime_7247 : Nat.Prime 7247 := by norm_num
lemma mod4_7247 : 7247 % 4 = 3 := by decide
lemma prime_7283 : Nat.Prime 7283 := by norm_num
lemma mod4_7283 : 7283 % 4 = 3 := by decide
lemma prime_7307 : Nat.Prime 7307 := by norm_num
lemma mod4_7307 : 7307 % 4 = 3 := by decide
lemma prime_7331 : Nat.Prime 7331 := by norm_num
lemma mod4_7331 : 7331 % 4 = 3 := by decide
lemma prime_7351 : Nat.Prime 7351 := by norm_num
lemma mod4_7351 : 7351 % 4 = 3 := by decide
lemma prime_7411 : Nat.Prime 7411 := by norm_num
lemma mod4_7411 : 7411 % 4 = 3 := by decide
lemma prime_7451 : Nat.Prime 7451 := by norm_num
lemma mod4_7451 : 7451 % 4 = 3 := by decide
lemma prime_7459 : Nat.Prime 7459 := by norm_num
lemma mod4_7459 : 7459 % 4 = 3 := by decide
lemma prime_7487 : Nat.Prime 7487 := by norm_num
lemma mod4_7487 : 7487 % 4 = 3 := by decide
lemma prime_7499 : Nat.Prime 7499 := by norm_num
lemma mod4_7499 : 7499 % 4 = 3 := by decide
lemma prime_7507 : Nat.Prime 7507 := by norm_num
lemma mod4_7507 : 7507 % 4 = 3 := by decide
lemma prime_7523 : Nat.Prime 7523 := by norm_num
lemma mod4_7523 : 7523 % 4 = 3 := by decide
lemma prime_7547 : Nat.Prime 7547 := by norm_num
lemma mod4_7547 : 7547 % 4 = 3 := by decide
lemma prime_7559 : Nat.Prime 7559 := by norm_num
lemma mod4_7559 : 7559 % 4 = 3 := by decide
lemma prime_7583 : Nat.Prime 7583 := by norm_num
lemma mod4_7583 : 7583 % 4 = 3 := by decide
lemma prime_7591 : Nat.Prime 7591 := by norm_num
lemma mod4_7591 : 7591 % 4 = 3 := by decide
lemma prime_7603 : Nat.Prime 7603 := by norm_num
lemma mod4_7603 : 7603 % 4 = 3 := by decide
lemma prime_7607 : Nat.Prime 7607 := by norm_num
lemma mod4_7607 : 7607 % 4 = 3 := by decide
lemma prime_7639 : Nat.Prime 7639 := by norm_num
lemma mod4_7639 : 7639 % 4 = 3 := by decide
lemma prime_7643 : Nat.Prime 7643 := by norm_num
lemma mod4_7643 : 7643 % 4 = 3 := by decide
lemma prime_7687 : Nat.Prime 7687 := by norm_num
lemma mod4_7687 : 7687 % 4 = 3 := by decide
lemma prime_7691 : Nat.Prime 7691 := by norm_num
lemma mod4_7691 : 7691 % 4 = 3 := by decide
lemma prime_7699 : Nat.Prime 7699 := by norm_num
lemma mod4_7699 : 7699 % 4 = 3 := by decide
lemma prime_7703 : Nat.Prime 7703 := by norm_num
lemma mod4_7703 : 7703 % 4 = 3 := by decide
lemma prime_7723 : Nat.Prime 7723 := by norm_num
lemma mod4_7723 : 7723 % 4 = 3 := by decide
lemma prime_7727 : Nat.Prime 7727 := by norm_num
lemma mod4_7727 : 7727 % 4 = 3 := by decide
lemma prime_7759 : Nat.Prime 7759 := by norm_num
lemma mod4_7759 : 7759 % 4 = 3 := by decide
lemma prime_7823 : Nat.Prime 7823 := by norm_num
lemma mod4_7823 : 7823 % 4 = 3 := by decide
lemma prime_7867 : Nat.Prime 7867 := by norm_num
lemma mod4_7867 : 7867 % 4 = 3 := by decide
lemma prime_7879 : Nat.Prime 7879 := by norm_num
lemma mod4_7879 : 7879 % 4 = 3 := by decide
lemma prime_7883 : Nat.Prime 7883 := by norm_num
lemma mod4_7883 : 7883 % 4 = 3 := by decide
lemma prime_7907 : Nat.Prime 7907 := by norm_num
lemma mod4_7907 : 7907 % 4 = 3 := by decide
lemma prime_7919 : Nat.Prime 7919 := by norm_num
lemma mod4_7919 : 7919 % 4 = 3 := by decide
lemma prime_7927 : Nat.Prime 7927 := by norm_num
lemma mod4_7927 : 7927 % 4 = 3 := by decide
lemma prime_7951 : Nat.Prime 7951 := by norm_num
lemma mod4_7951 : 7951 % 4 = 3 := by decide
lemma prime_7963 : Nat.Prime 7963 := by norm_num
lemma mod4_7963 : 7963 % 4 = 3 := by decide
lemma prime_8011 : Nat.Prime 8011 := by norm_num
lemma mod4_8011 : 8011 % 4 = 3 := by decide
lemma prime_8039 : Nat.Prime 8039 := by norm_num
lemma mod4_8039 : 8039 % 4 = 3 := by decide
lemma prime_8059 : Nat.Prime 8059 := by norm_num
lemma mod4_8059 : 8059 % 4 = 3 := by decide
lemma prime_8087 : Nat.Prime 8087 := by norm_num
lemma mod4_8087 : 8087 % 4 = 3 := by decide
lemma prime_8111 : Nat.Prime 8111 := by norm_num
lemma mod4_8111 : 8111 % 4 = 3 := by decide
lemma prime_8123 : Nat.Prime 8123 := by norm_num
lemma mod4_8123 : 8123 % 4 = 3 := by decide
lemma prime_8147 : Nat.Prime 8147 := by norm_num
lemma mod4_8147 : 8147 % 4 = 3 := by decide
lemma prime_8167 : Nat.Prime 8167 := by norm_num
lemma mod4_8167 : 8167 % 4 = 3 := by decide
lemma prime_8171 : Nat.Prime 8171 := by norm_num
lemma mod4_8171 : 8171 % 4 = 3 := by decide
lemma prime_8179 : Nat.Prime 8179 := by norm_num
lemma mod4_8179 : 8179 % 4 = 3 := by decide
lemma prime_8191 : Nat.Prime 8191 := by norm_num
lemma mod4_8191 : 8191 % 4 = 3 := by decide
lemma prime_8219 : Nat.Prime 8219 := by norm_num
lemma mod4_8219 : 8219 % 4 = 3 := by decide
lemma prime_8231 : Nat.Prime 8231 := by norm_num
lemma mod4_8231 : 8231 % 4 = 3 := by decide
lemma prime_8243 : Nat.Prime 8243 := by norm_num
lemma mod4_8243 : 8243 % 4 = 3 := by decide
lemma prime_8263 : Nat.Prime 8263 := by norm_num
lemma mod4_8263 : 8263 % 4 = 3 := by decide
lemma prime_8287 : Nat.Prime 8287 := by norm_num
lemma mod4_8287 : 8287 % 4 = 3 := by decide
lemma prime_8291 : Nat.Prime 8291 := by norm_num
lemma mod4_8291 : 8291 % 4 = 3 := by decide
lemma prime_8311 : Nat.Prime 8311 := by norm_num
lemma mod4_8311 : 8311 % 4 = 3 := by decide
lemma prime_8363 : Nat.Prime 8363 := by norm_num
lemma mod4_8363 : 8363 % 4 = 3 := by decide
lemma prime_8387 : Nat.Prime 8387 := by norm_num
lemma mod4_8387 : 8387 % 4 = 3 := by decide
lemma prime_8419 : Nat.Prime 8419 := by norm_num
lemma mod4_8419 : 8419 % 4 = 3 := by decide
lemma prime_8423 : Nat.Prime 8423 := by norm_num
lemma mod4_8423 : 8423 % 4 = 3 := by decide
lemma prime_8431 : Nat.Prime 8431 := by norm_num
lemma mod4_8431 : 8431 % 4 = 3 := by decide
lemma prime_8443 : Nat.Prime 8443 := by norm_num
lemma mod4_8443 : 8443 % 4 = 3 := by decide
lemma prime_8447 : Nat.Prime 8447 := by norm_num
lemma mod4_8447 : 8447 % 4 = 3 := by decide
lemma prime_8467 : Nat.Prime 8467 := by norm_num
lemma mod4_8467 : 8467 % 4 = 3 := by decide
lemma prime_8527 : Nat.Prime 8527 := by norm_num
lemma mod4_8527 : 8527 % 4 = 3 := by decide
lemma prime_8539 : Nat.Prime 8539 := by norm_num
lemma mod4_8539 : 8539 % 4 = 3 := by decide
lemma prime_8543 : Nat.Prime 8543 := by norm_num
lemma mod4_8543 : 8543 % 4 = 3 := by decide
lemma prime_8563 : Nat.Prime 8563 := by norm_num
lemma mod4_8563 : 8563 % 4 = 3 := by decide
lemma prime_8599 : Nat.Prime 8599 := by norm_num
lemma mod4_8599 : 8599 % 4 = 3 := by decide
lemma prime_8623 : Nat.Prime 8623 := by norm_num
lemma mod4_8623 : 8623 % 4 = 3 := by decide
lemma prime_8627 : Nat.Prime 8627 := by norm_num
lemma mod4_8627 : 8627 % 4 = 3 := by decide
lemma prime_8647 : Nat.Prime 8647 := by norm_num
lemma mod4_8647 : 8647 % 4 = 3 := by decide
lemma prime_8663 : Nat.Prime 8663 := by norm_num
lemma mod4_8663 : 8663 % 4 = 3 := by decide
lemma prime_8699 : Nat.Prime 8699 := by norm_num
lemma mod4_8699 : 8699 % 4 = 3 := by decide
lemma prime_8707 : Nat.Prime 8707 := by norm_num
lemma mod4_8707 : 8707 % 4 = 3 := by decide
lemma prime_8719 : Nat.Prime 8719 := by norm_num
lemma mod4_8719 : 8719 % 4 = 3 := by decide
lemma prime_8731 : Nat.Prime 8731 := by norm_num
lemma mod4_8731 : 8731 % 4 = 3 := by decide
lemma prime_8747 : Nat.Prime 8747 := by norm_num
lemma mod4_8747 : 8747 % 4 = 3 := by decide
lemma prime_8779 : Nat.Prime 8779 := by norm_num
lemma mod4_8779 : 8779 % 4 = 3 := by decide
lemma prime_8783 : Nat.Prime 8783 := by norm_num
lemma mod4_8783 : 8783 % 4 = 3 := by decide
lemma prime_8803 : Nat.Prime 8803 := by norm_num
lemma mod4_8803 : 8803 % 4 = 3 := by decide
lemma prime_8807 : Nat.Prime 8807 := by norm_num
lemma mod4_8807 : 8807 % 4 = 3 := by decide
lemma prime_8819 : Nat.Prime 8819 := by norm_num
lemma mod4_8819 : 8819 % 4 = 3 := by decide
lemma prime_8831 : Nat.Prime 8831 := by norm_num
lemma mod4_8831 : 8831 % 4 = 3 := by decide
lemma prime_8839 : Nat.Prime 8839 := by norm_num
lemma mod4_8839 : 8839 % 4 = 3 := by decide
lemma prime_8863 : Nat.Prime 8863 := by norm_num
lemma mod4_8863 : 8863 % 4 = 3 := by decide
lemma prime_8867 : Nat.Prime 8867 := by norm_num
lemma mod4_8867 : 8867 % 4 = 3 := by decide
lemma prime_8887 : Nat.Prime 8887 := by norm_num
lemma mod4_8887 : 8887 % 4 = 3 := by decide
lemma prime_8923 : Nat.Prime 8923 := by norm_num
lemma mod4_8923 : 8923 % 4 = 3 := by decide
lemma prime_8951 : Nat.Prime 8951 := by norm_num
lemma mod4_8951 : 8951 % 4 = 3 := by decide
lemma prime_8963 : Nat.Prime 8963 := by norm_num
lemma mod4_8963 : 8963 % 4 = 3 := by decide
lemma prime_8971 : Nat.Prime 8971 := by norm_num
lemma mod4_8971 : 8971 % 4 = 3 := by decide
lemma prime_8999 : Nat.Prime 8999 := by norm_num
lemma mod4_8999 : 8999 % 4 = 3 := by decide
lemma prime_9007 : Nat.Prime 9007 := by norm_num
lemma mod4_9007 : 9007 % 4 = 3 := by decide
lemma prime_9011 : Nat.Prime 9011 := by norm_num
lemma mod4_9011 : 9011 % 4 = 3 := by decide
lemma prime_9043 : Nat.Prime 9043 := by norm_num
lemma mod4_9043 : 9043 % 4 = 3 := by decide
lemma prime_9059 : Nat.Prime 9059 := by norm_num
lemma mod4_9059 : 9059 % 4 = 3 := by decide
lemma prime_9067 : Nat.Prime 9067 := by norm_num
lemma mod4_9067 : 9067 % 4 = 3 := by decide
lemma prime_9091 : Nat.Prime 9091 := by norm_num
lemma mod4_9091 : 9091 % 4 = 3 := by decide
lemma prime_9103 : Nat.Prime 9103 := by norm_num
lemma mod4_9103 : 9103 % 4 = 3 := by decide
lemma prime_9127 : Nat.Prime 9127 := by norm_num
lemma mod4_9127 : 9127 % 4 = 3 := by decide
lemma prime_9151 : Nat.Prime 9151 := by norm_num
lemma mod4_9151 : 9151 % 4 = 3 := by decide
lemma prime_9187 : Nat.Prime 9187 := by norm_num
lemma mod4_9187 : 9187 % 4 = 3 := by decide
lemma prime_9199 : Nat.Prime 9199 := by norm_num
lemma mod4_9199 : 9199 % 4 = 3 := by decide
lemma prime_9203 : Nat.Prime 9203 := by norm_num
lemma mod4_9203 : 9203 % 4 = 3 := by decide
lemma prime_9227 : Nat.Prime 9227 := by norm_num
lemma mod4_9227 : 9227 % 4 = 3 := by decide
lemma prime_9239 : Nat.Prime 9239 := by norm_num
lemma mod4_9239 : 9239 % 4 = 3 := by decide
lemma prime_9283 : Nat.Prime 9283 := by norm_num
lemma mod4_9283 : 9283 % 4 = 3 := by decide
lemma prime_9311 : Nat.Prime 9311 := by norm_num
lemma mod4_9311 : 9311 % 4 = 3 := by decide
lemma prime_9319 : Nat.Prime 9319 := by norm_num
lemma mod4_9319 : 9319 % 4 = 3 := by decide
lemma prime_9323 : Nat.Prime 9323 := by norm_num
lemma mod4_9323 : 9323 % 4 = 3 := by decide
lemma prime_9343 : Nat.Prime 9343 := by norm_num
lemma mod4_9343 : 9343 % 4 = 3 := by decide
lemma prime_9371 : Nat.Prime 9371 := by norm_num
lemma mod4_9371 : 9371 % 4 = 3 := by decide
lemma prime_9391 : Nat.Prime 9391 := by norm_num
lemma mod4_9391 : 9391 % 4 = 3 := by decide
lemma prime_9403 : Nat.Prime 9403 := by norm_num
lemma mod4_9403 : 9403 % 4 = 3 := by decide
lemma prime_9419 : Nat.Prime 9419 := by norm_num
lemma mod4_9419 : 9419 % 4 = 3 := by decide
lemma prime_9431 : Nat.Prime 9431 := by norm_num
lemma mod4_9431 : 9431 % 4 = 3 := by decide
lemma prime_9439 : Nat.Prime 9439 := by norm_num
lemma mod4_9439 : 9439 % 4 = 3 := by decide
lemma prime_9463 : Nat.Prime 9463 := by norm_num
lemma mod4_9463 : 9463 % 4 = 3 := by decide
lemma prime_9467 : Nat.Prime 9467 := by norm_num
lemma mod4_9467 : 9467 % 4 = 3 := by decide
lemma prime_9479 : Nat.Prime 9479 := by norm_num
lemma mod4_9479 : 9479 % 4 = 3 := by decide
lemma prime_9491 : Nat.Prime 9491 := by norm_num
lemma mod4_9491 : 9491 % 4 = 3 := by decide
lemma prime_9511 : Nat.Prime 9511 := by norm_num
lemma mod4_9511 : 9511 % 4 = 3 := by decide
lemma prime_9539 : Nat.Prime 9539 := by norm_num
lemma mod4_9539 : 9539 % 4 = 3 := by decide
lemma prime_9547 : Nat.Prime 9547 := by norm_num
lemma mod4_9547 : 9547 % 4 = 3 := by decide
lemma prime_9551 : Nat.Prime 9551 := by norm_num
lemma mod4_9551 : 9551 % 4 = 3 := by decide
lemma prime_9587 : Nat.Prime 9587 := by norm_num
lemma mod4_9587 : 9587 % 4 = 3 := by decide
lemma prime_9619 : Nat.Prime 9619 := by norm_num
lemma mod4_9619 : 9619 % 4 = 3 := by decide
lemma prime_9623 : Nat.Prime 9623 := by norm_num
lemma mod4_9623 : 9623 % 4 = 3 := by decide
lemma prime_9631 : Nat.Prime 9631 := by norm_num
lemma mod4_9631 : 9631 % 4 = 3 := by decide
lemma prime_9643 : Nat.Prime 9643 := by norm_num
lemma mod4_9643 : 9643 % 4 = 3 := by decide
lemma prime_9679 : Nat.Prime 9679 := by norm_num
lemma mod4_9679 : 9679 % 4 = 3 := by decide
lemma prime_9719 : Nat.Prime 9719 := by norm_num
lemma mod4_9719 : 9719 % 4 = 3 := by decide
lemma prime_9739 : Nat.Prime 9739 := by norm_num
lemma mod4_9739 : 9739 % 4 = 3 := by decide
lemma prime_9743 : Nat.Prime 9743 := by norm_num
lemma mod4_9743 : 9743 % 4 = 3 := by decide
lemma prime_9767 : Nat.Prime 9767 := by norm_num
lemma mod4_9767 : 9767 % 4 = 3 := by decide
lemma prime_9787 : Nat.Prime 9787 := by norm_num
lemma mod4_9787 : 9787 % 4 = 3 := by decide
lemma prime_9811 : Nat.Prime 9811 := by norm_num
lemma mod4_9811 : 9811 % 4 = 3 := by decide
lemma prime_9887 : Nat.Prime 9887 := by norm_num
lemma mod4_9887 : 9887 % 4 = 3 := by decide
lemma prime_9923 : Nat.Prime 9923 := by norm_num
lemma mod4_9923 : 9923 % 4 = 3 := by decide
lemma prime_9967 : Nat.Prime 9967 := by norm_num
lemma mod4_9967 : 9967 % 4 = 3 := by decide
lemma prime_10067 : Nat.Prime 10067 := by norm_num
lemma mod4_10067 : 10067 % 4 = 3 := by decide
lemma prime_10079 : Nat.Prime 10079 := by norm_num
lemma mod4_10079 : 10079 % 4 = 3 := by decide
lemma prime_10099 : Nat.Prime 10099 := by norm_num
lemma mod4_10099 : 10099 % 4 = 3 := by decide
lemma prime_10111 : Nat.Prime 10111 := by norm_num
lemma mod4_10111 : 10111 % 4 = 3 := by decide
lemma prime_10139 : Nat.Prime 10139 := by norm_num
lemma mod4_10139 : 10139 % 4 = 3 := by decide
lemma prime_10159 : Nat.Prime 10159 := by norm_num
lemma mod4_10159 : 10159 % 4 = 3 := by decide
lemma prime_10163 : Nat.Prime 10163 := by norm_num
lemma mod4_10163 : 10163 % 4 = 3 := by decide
lemma prime_10223 : Nat.Prime 10223 := by norm_num
lemma mod4_10223 : 10223 % 4 = 3 := by decide
lemma prime_10243 : Nat.Prime 10243 := by norm_num
lemma mod4_10243 : 10243 % 4 = 3 := by decide
lemma prime_10247 : Nat.Prime 10247 := by norm_num
lemma mod4_10247 : 10247 % 4 = 3 := by decide
lemma prime_10259 : Nat.Prime 10259 := by norm_num
lemma mod4_10259 : 10259 % 4 = 3 := by decide
lemma prime_10267 : Nat.Prime 10267 := by norm_num
lemma mod4_10267 : 10267 % 4 = 3 := by decide
lemma prime_10271 : Nat.Prime 10271 := by norm_num
lemma mod4_10271 : 10271 % 4 = 3 := by decide
lemma prime_10303 : Nat.Prime 10303 := by norm_num
lemma mod4_10303 : 10303 % 4 = 3 := by decide
lemma prime_10343 : Nat.Prime 10343 := by norm_num
lemma mod4_10343 : 10343 % 4 = 3 := by decide
lemma prime_10463 : Nat.Prime 10463 := by norm_num
lemma mod4_10463 : 10463 % 4 = 3 := by decide
lemma prime_10531 : Nat.Prime 10531 := by norm_num
lemma mod4_10531 : 10531 % 4 = 3 := by decide
lemma prime_10567 : Nat.Prime 10567 := by norm_num
lemma mod4_10567 : 10567 % 4 = 3 := by decide
lemma prime_10607 : Nat.Prime 10607 := by norm_num
lemma mod4_10607 : 10607 % 4 = 3 := by decide
lemma prime_10627 : Nat.Prime 10627 := by norm_num
lemma mod4_10627 : 10627 % 4 = 3 := by decide
lemma prime_10631 : Nat.Prime 10631 := by norm_num
lemma mod4_10631 : 10631 % 4 = 3 := by decide
lemma prime_10691 : Nat.Prime 10691 := by norm_num
lemma mod4_10691 : 10691 % 4 = 3 := by decide
lemma prime_10739 : Nat.Prime 10739 := by norm_num
lemma mod4_10739 : 10739 % 4 = 3 := by decide
lemma prime_10771 : Nat.Prime 10771 := by norm_num
lemma mod4_10771 : 10771 % 4 = 3 := by decide
lemma prime_10859 : Nat.Prime 10859 := by norm_num
lemma mod4_10859 : 10859 % 4 = 3 := by decide
lemma prime_11003 : Nat.Prime 11003 := by norm_num
lemma mod4_11003 : 11003 % 4 = 3 := by decide
lemma prime_11027 : Nat.Prime 11027 := by norm_num
lemma mod4_11027 : 11027 % 4 = 3 := by decide
lemma prime_11047 : Nat.Prime 11047 := by norm_num
lemma mod4_11047 : 11047 % 4 = 3 := by decide
lemma prime_11119 : Nat.Prime 11119 := by norm_num
lemma mod4_11119 : 11119 % 4 = 3 := by decide
lemma prime_11131 : Nat.Prime 11131 := by norm_num
lemma mod4_11131 : 11131 % 4 = 3 := by decide
lemma prime_11239 : Nat.Prime 11239 := by norm_num
lemma mod4_11239 : 11239 % 4 = 3 := by decide
lemma prime_11279 : Nat.Prime 11279 := by norm_num
lemma mod4_11279 : 11279 % 4 = 3 := by decide
lemma prime_11287 : Nat.Prime 11287 := by norm_num
lemma mod4_11287 : 11287 % 4 = 3 := by decide
lemma prime_11299 : Nat.Prime 11299 := by norm_num
lemma mod4_11299 : 11299 % 4 = 3 := by decide
lemma prime_11351 : Nat.Prime 11351 := by norm_num
lemma mod4_11351 : 11351 % 4 = 3 := by decide
lemma prime_11423 : Nat.Prime 11423 := by norm_num
lemma mod4_11423 : 11423 % 4 = 3 := by decide
lemma prime_11471 : Nat.Prime 11471 := by norm_num
lemma mod4_11471 : 11471 % 4 = 3 := by decide
lemma prime_11491 : Nat.Prime 11491 := by norm_num
lemma mod4_11491 : 11491 % 4 = 3 := by decide
lemma prime_11503 : Nat.Prime 11503 := by norm_num
lemma mod4_11503 : 11503 % 4 = 3 := by decide
lemma prime_11519 : Nat.Prime 11519 := by norm_num
lemma mod4_11519 : 11519 % 4 = 3 := by decide
lemma prime_11587 : Nat.Prime 11587 := by norm_num
lemma mod4_11587 : 11587 % 4 = 3 := by decide
lemma prime_11807 : Nat.Prime 11807 := by norm_num
lemma mod4_11807 : 11807 % 4 = 3 := by decide
lemma prime_11839 : Nat.Prime 11839 := by norm_num
lemma mod4_11839 : 11839 % 4 = 3 := by decide
lemma prime_11863 : Nat.Prime 11863 := by norm_num
lemma mod4_11863 : 11863 % 4 = 3 := by decide
lemma prime_11867 : Nat.Prime 11867 := by norm_num
lemma mod4_11867 : 11867 % 4 = 3 := by decide
lemma prime_12119 : Nat.Prime 12119 := by norm_num
lemma mod4_12119 : 12119 % 4 = 3 := by decide
lemma prime_12163 : Nat.Prime 12163 := by norm_num
lemma mod4_12163 : 12163 % 4 = 3 := by decide
lemma prime_12203 : Nat.Prime 12203 := by norm_num
lemma mod4_12203 : 12203 % 4 = 3 := by decide
lemma prime_12263 : Nat.Prime 12263 := by norm_num
lemma mod4_12263 : 12263 % 4 = 3 := by decide
lemma prime_12343 : Nat.Prime 12343 := by norm_num
lemma mod4_12343 : 12343 % 4 = 3 := by decide
lemma prime_12379 : Nat.Prime 12379 := by norm_num
lemma mod4_12379 : 12379 % 4 = 3 := by decide
lemma prime_12479 : Nat.Prime 12479 := by norm_num
lemma mod4_12479 : 12479 % 4 = 3 := by decide
lemma prime_12503 : Nat.Prime 12503 := by norm_num
lemma mod4_12503 : 12503 % 4 = 3 := by decide
lemma prime_12527 : Nat.Prime 12527 := by norm_num
lemma mod4_12527 : 12527 % 4 = 3 := by decide
lemma prime_12671 : Nat.Prime 12671 := by norm_num
lemma mod4_12671 : 12671 % 4 = 3 := by decide
lemma prime_12763 : Nat.Prime 12763 := by norm_num
lemma mod4_12763 : 12763 % 4 = 3 := by decide
lemma prime_12899 : Nat.Prime 12899 := by norm_num
lemma mod4_12899 : 12899 % 4 = 3 := by decide
lemma prime_12919 : Nat.Prime 12919 := by norm_num
lemma mod4_12919 : 12919 % 4 = 3 := by decide
lemma prime_12959 : Nat.Prime 12959 := by norm_num
lemma mod4_12959 : 12959 % 4 = 3 := by decide
lemma prime_13367 : Nat.Prime 13367 := by norm_num
lemma mod4_13367 : 13367 % 4 = 3 := by decide
lemma prime_13399 : Nat.Prime 13399 := by norm_num
lemma mod4_13399 : 13399 % 4 = 3 := by decide
lemma prime_13591 : Nat.Prime 13591 := by norm_num
lemma mod4_13591 : 13591 % 4 = 3 := by decide
lemma prime_13619 : Nat.Prime 13619 := by norm_num
lemma mod4_13619 : 13619 % 4 = 3 := by decide
lemma prime_13691 : Nat.Prime 13691 := by norm_num
lemma mod4_13691 : 13691 % 4 = 3 := by decide
lemma prime_13807 : Nat.Prime 13807 := by norm_num
lemma mod4_13807 : 13807 % 4 = 3 := by decide
lemma prime_14251 : Nat.Prime 14251 := by norm_num
lemma mod4_14251 : 14251 % 4 = 3 := by decide
lemma prime_14303 : Nat.Prime 14303 := by norm_num
lemma mod4_14303 : 14303 % 4 = 3 := by decide
lemma prime_14411 : Nat.Prime 14411 := by norm_num
lemma mod4_14411 : 14411 % 4 = 3 := by decide
lemma prime_14563 : Nat.Prime 14563 := by norm_num
lemma mod4_14563 : 14563 % 4 = 3 := by decide
lemma prime_14627 : Nat.Prime 14627 := by norm_num
lemma mod4_14627 : 14627 % 4 = 3 := by decide
lemma prime_14683 : Nat.Prime 14683 := by norm_num
lemma mod4_14683 : 14683 % 4 = 3 := by decide
lemma prime_14699 : Nat.Prime 14699 := by norm_num
lemma mod4_14699 : 14699 % 4 = 3 := by decide
lemma prime_14939 : Nat.Prime 14939 := by norm_num
lemma mod4_14939 : 14939 % 4 = 3 := by decide
lemma prime_14951 : Nat.Prime 14951 := by norm_num
lemma mod4_14951 : 14951 % 4 = 3 := by decide
lemma prime_15107 : Nat.Prime 15107 := by norm_num
lemma mod4_15107 : 15107 % 4 = 3 := by decide
lemma prime_15227 : Nat.Prime 15227 := by norm_num
lemma mod4_15227 : 15227 % 4 = 3 := by decide
lemma prime_15259 : Nat.Prime 15259 := by norm_num
lemma mod4_15259 : 15259 % 4 = 3 := by decide
lemma prime_15331 : Nat.Prime 15331 := by norm_num
lemma mod4_15331 : 15331 % 4 = 3 := by decide
lemma prime_15391 : Nat.Prime 15391 := by norm_num
lemma mod4_15391 : 15391 % 4 = 3 := by decide
lemma prime_15439 : Nat.Prime 15439 := by norm_num
lemma mod4_15439 : 15439 % 4 = 3 := by decide
lemma prime_15443 : Nat.Prime 15443 := by norm_num
lemma mod4_15443 : 15443 % 4 = 3 := by decide
lemma prime_15647 : Nat.Prime 15647 := by norm_num
lemma mod4_15647 : 15647 % 4 = 3 := by decide
lemma prime_15671 : Nat.Prime 15671 := by norm_num
lemma mod4_15671 : 15671 % 4 = 3 := by decide
lemma prime_15679 : Nat.Prime 15679 := by norm_num
lemma mod4_15679 : 15679 % 4 = 3 := by decide
lemma prime_15859 : Nat.Prime 15859 := by norm_num
lemma mod4_15859 : 15859 % 4 = 3 := by decide
lemma prime_15887 : Nat.Prime 15887 := by norm_num
lemma mod4_15887 : 15887 % 4 = 3 := by decide
lemma prime_15991 : Nat.Prime 15991 := by norm_num
lemma mod4_15991 : 15991 % 4 = 3 := by decide
lemma prime_16139 : Nat.Prime 16139 := by norm_num
lemma mod4_16139 : 16139 % 4 = 3 := by decide
lemma prime_16603 : Nat.Prime 16603 := by norm_num
lemma mod4_16603 : 16603 % 4 = 3 := by decide
lemma prime_16699 : Nat.Prime 16699 := by norm_num
lemma mod4_16699 : 16699 % 4 = 3 := by decide
lemma prime_16831 : Nat.Prime 16831 := by norm_num
lemma mod4_16831 : 16831 % 4 = 3 := by decide
lemma prime_17027 : Nat.Prime 17027 := by norm_num
lemma mod4_17027 : 17027 % 4 = 3 := by decide
lemma prime_17107 : Nat.Prime 17107 := by norm_num
lemma mod4_17107 : 17107 % 4 = 3 := by decide
lemma prime_17239 : Nat.Prime 17239 := by norm_num
lemma mod4_17239 : 17239 % 4 = 3 := by decide
lemma prime_17327 : Nat.Prime 17327 := by norm_num
lemma mod4_17327 : 17327 % 4 = 3 := by decide
lemma prime_17471 : Nat.Prime 17471 := by norm_num
lemma mod4_17471 : 17471 % 4 = 3 := by decide
lemma prime_17519 : Nat.Prime 17519 := by norm_num
lemma mod4_17519 : 17519 % 4 = 3 := by decide
lemma prime_17539 : Nat.Prime 17539 := by norm_num
lemma mod4_17539 : 17539 % 4 = 3 := by decide
lemma prime_17807 : Nat.Prime 17807 := by norm_num
lemma mod4_17807 : 17807 % 4 = 3 := by decide
lemma prime_18911 : Nat.Prime 18911 := by norm_num
lemma mod4_18911 : 18911 % 4 = 3 := by decide
lemma prime_19183 : Nat.Prime 19183 := by norm_num
lemma mod4_19183 : 19183 % 4 = 3 := by decide
lemma prime_19319 : Nat.Prime 19319 := by norm_num
lemma mod4_19319 : 19319 % 4 = 3 := by decide
lemma prime_19739 : Nat.Prime 19739 := by norm_num
lemma mod4_19739 : 19739 % 4 = 3 := by decide
lemma prime_19759 : Nat.Prime 19759 := by norm_num
lemma mod4_19759 : 19759 % 4 = 3 := by decide
lemma prime_19891 : Nat.Prime 19891 := by norm_num
lemma mod4_19891 : 19891 % 4 = 3 := by decide

def blocking_primes_0 : List ℕ := [3, 11, 31, 3, 83, 11, 3, 31, 7867, 3, 11, 11, 3, 8731, 1223, 3, 11, 31, 3, 1279, 11, 3, 31, 9719, 3, 11, 11, 3, 1303, 2687, 3, 11, 31, 3, 1867, 11, 3, 31, 863, 3, 3, 19, 43, 3, 127, 739, 3, 8191, 83, 3, 19, 127, 3, 367, 4339, 3, 43, 47, 3, 19, 8191, 3, 607, 43, 3, 127, 5023, 3, 19, 6367, 3, 331, 127, 3, 383, 10343, 3, 19, 239, 3, 7, 23, 47, 79, 11, 3347, 7, 751, 79, 7, 127, 443, 7, 3391, 11, 7, 5623, 127, 7, 11]
def blocking_prime_by_idx_0 (idx : ℕ) : ℕ := blocking_primes_0.getD (idx - 0) 3

lemma prime_of_mem_blocking_primes_0 {p : ℕ} (h : p ∈ 3 :: blocking_primes_0) : Nat.Prime p := by
  unfold blocking_primes_0 at h
  simp only [List.mem_cons] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | h_false
  · exact prime_3
  · exact prime_3
  · exact prime_11
  · exact prime_31
  · exact prime_3
  · exact prime_83
  · exact prime_11
  · exact prime_3
  · exact prime_31
  · exact prime_7867
  · exact prime_3
  · exact prime_11
  · exact prime_11
  · exact prime_3
  · exact prime_8731
  · exact prime_1223
  · exact prime_3
  · exact prime_11
  · exact prime_31
  · exact prime_3
  · exact prime_1279
  · exact prime_11
  · exact prime_3
  · exact prime_31
  · exact prime_9719
  · exact prime_3
  · exact prime_11
  · exact prime_11
  · exact prime_3
  · exact prime_1303
  · exact prime_2687
  · exact prime_3
  · exact prime_11
  · exact prime_31
  · exact prime_3
  · exact prime_1867
  · exact prime_11
  · exact prime_3
  · exact prime_31
  · exact prime_863
  · exact prime_3
  · exact prime_3
  · exact prime_19
  · exact prime_43
  · exact prime_3
  · exact prime_127
  · exact prime_739
  · exact prime_3
  · exact prime_8191
  · exact prime_83
  · exact prime_3
  · exact prime_19
  · exact prime_127
  · exact prime_3
  · exact prime_367
  · exact prime_4339
  · exact prime_3
  · exact prime_43
  · exact prime_47
  · exact prime_3
  · exact prime_19
  · exact prime_8191
  · exact prime_3
  · exact prime_607
  · exact prime_43
  · exact prime_3
  · exact prime_127
  · exact prime_5023
  · exact prime_3
  · exact prime_19
  · exact prime_6367
  · exact prime_3
  · exact prime_331
  · exact prime_127
  · exact prime_3
  · exact prime_383
  · exact prime_10343
  · exact prime_3
  · exact prime_19
  · exact prime_239
  · exact prime_3
  · exact prime_7
  · exact prime_23
  · exact prime_47
  · exact prime_79
  · exact prime_11
  · exact prime_3347
  · exact prime_7
  · exact prime_751
  · exact prime_79
  · exact prime_7
  · exact prime_127
  · exact prime_443
  · exact prime_7
  · exact prime_3391
  · exact prime_11
  · exact prime_7
  · exact prime_5623
  · exact prime_127
  · exact prime_7
  · exact prime_11
  · cases h_false

lemma blocking_prime_by_idx_0_prime (idx : ℕ) : Nat.Prime (blocking_prime_by_idx_0 idx) :=
  prime_of_mem_blocking_primes_0 (getD_mem blocking_primes_0 (idx - 0) 3)

lemma mod4_of_mem_blocking_primes_0 {p : ℕ} (h : p ∈ 3 :: blocking_primes_0) : p % 4 = 3 := by
  unfold blocking_primes_0 at h
  simp only [List.mem_cons] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | h_false
  · exact mod4_3
  · exact mod4_3
  · exact mod4_11
  · exact mod4_31
  · exact mod4_3
  · exact mod4_83
  · exact mod4_11
  · exact mod4_3
  · exact mod4_31
  · exact mod4_7867
  · exact mod4_3
  · exact mod4_11
  · exact mod4_11
  · exact mod4_3
  · exact mod4_8731
  · exact mod4_1223
  · exact mod4_3
  · exact mod4_11
  · exact mod4_31
  · exact mod4_3
  · exact mod4_1279
  · exact mod4_11
  · exact mod4_3
  · exact mod4_31
  · exact mod4_9719
  · exact mod4_3
  · exact mod4_11
  · exact mod4_11
  · exact mod4_3
  · exact mod4_1303
  · exact mod4_2687
  · exact mod4_3
  · exact mod4_11
  · exact mod4_31
  · exact mod4_3
  · exact mod4_1867
  · exact mod4_11
  · exact mod4_3
  · exact mod4_31
  · exact mod4_863
  · exact mod4_3
  · exact mod4_3
  · exact mod4_19
  · exact mod4_43
  · exact mod4_3
  · exact mod4_127
  · exact mod4_739
  · exact mod4_3
  · exact mod4_8191
  · exact mod4_83
  · exact mod4_3
  · exact mod4_19
  · exact mod4_127
  · exact mod4_3
  · exact mod4_367
  · exact mod4_4339
  · exact mod4_3
  · exact mod4_43
  · exact mod4_47
  · exact mod4_3
  · exact mod4_19
  · exact mod4_8191
  · exact mod4_3
  · exact mod4_607
  · exact mod4_43
  · exact mod4_3
  · exact mod4_127
  · exact mod4_5023
  · exact mod4_3
  · exact mod4_19
  · exact mod4_6367
  · exact mod4_3
  · exact mod4_331
  · exact mod4_127
  · exact mod4_3
  · exact mod4_383
  · exact mod4_10343
  · exact mod4_3
  · exact mod4_19
  · exact mod4_239
  · exact mod4_3
  · exact mod4_7
  · exact mod4_23
  · exact mod4_47
  · exact mod4_79
  · exact mod4_11
  · exact mod4_3347
  · exact mod4_7
  · exact mod4_751
  · exact mod4_79
  · exact mod4_7
  · exact mod4_127
  · exact mod4_443
  · exact mod4_7
  · exact mod4_3391
  · exact mod4_11
  · exact mod4_7
  · exact mod4_5623
  · exact mod4_127
  · exact mod4_7
  · exact mod4_11
  · cases h_false

lemma blocking_prime_by_idx_0_3mod4 (idx : ℕ) : blocking_prime_by_idx_0 idx % 4 = 3 :=
  mod4_of_mem_blocking_primes_0 (getD_mem blocking_primes_0 (idx - 0) 3)

def blocking_primes_1 : List ℕ := [2339, 7, 71, 23, 11, 47, 239, 7, 5939, 11, 7, 127, 8191, 7, 11, 1979, 7, 3739, 127, 7, 3, 59, 71, 3, 151, 4603, 3, 619, 19, 3, 2731, 9479, 3, 2267, 331, 3, 811, 19, 3, 151, 683, 3, 4099, 2731, 3, 9679, 19, 3, 71, 331, 3, 683, 9419, 3, 151, 19, 3, 71, 1531, 3, 3, 67, 107, 3, 167, 8179, 3, 271, 31, 3, 23, 271, 3, 31, 9391, 3, 5231, 367, 3, 431, 2971, 3, 919, 31, 3, 4783, 10567, 3, 31, 6011, 3, 6883, 23, 3, 67, 103, 3, 3163, 31, 3]
def blocking_prime_by_idx_1 (idx : ℕ) : ℕ := blocking_primes_1.getD (idx - 100) 3

lemma prime_of_mem_blocking_primes_1 {p : ℕ} (h : p ∈ 3 :: blocking_primes_1) : Nat.Prime p := by
  unfold blocking_primes_1 at h
  simp only [List.mem_cons] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | h_false
  · exact prime_3
  · exact prime_2339
  · exact prime_7
  · exact prime_71
  · exact prime_23
  · exact prime_11
  · exact prime_47
  · exact prime_239
  · exact prime_7
  · exact prime_5939
  · exact prime_11
  · exact prime_7
  · exact prime_127
  · exact prime_8191
  · exact prime_7
  · exact prime_11
  · exact prime_1979
  · exact prime_7
  · exact prime_3739
  · exact prime_127
  · exact prime_7
  · exact prime_3
  · exact prime_59
  · exact prime_71
  · exact prime_3
  · exact prime_151
  · exact prime_4603
  · exact prime_3
  · exact prime_619
  · exact prime_19
  · exact prime_3
  · exact prime_2731
  · exact prime_9479
  · exact prime_3
  · exact prime_2267
  · exact prime_331
  · exact prime_3
  · exact prime_811
  · exact prime_19
  · exact prime_3
  · exact prime_151
  · exact prime_683
  · exact prime_3
  · exact prime_4099
  · exact prime_2731
  · exact prime_3
  · exact prime_9679
  · exact prime_19
  · exact prime_3
  · exact prime_71
  · exact prime_331
  · exact prime_3
  · exact prime_683
  · exact prime_9419
  · exact prime_3
  · exact prime_151
  · exact prime_19
  · exact prime_3
  · exact prime_71
  · exact prime_1531
  · exact prime_3
  · exact prime_3
  · exact prime_67
  · exact prime_107
  · exact prime_3
  · exact prime_167
  · exact prime_8179
  · exact prime_3
  · exact prime_271
  · exact prime_31
  · exact prime_3
  · exact prime_23
  · exact prime_271
  · exact prime_3
  · exact prime_31
  · exact prime_9391
  · exact prime_3
  · exact prime_5231
  · exact prime_367
  · exact prime_3
  · exact prime_431
  · exact prime_2971
  · exact prime_3
  · exact prime_919
  · exact prime_31
  · exact prime_3
  · exact prime_4783
  · exact prime_10567
  · exact prime_3
  · exact prime_31
  · exact prime_6011
  · exact prime_3
  · exact prime_6883
  · exact prime_23
  · exact prime_3
  · exact prime_67
  · exact prime_103
  · exact prime_3
  · exact prime_3163
  · exact prime_31
  · exact prime_3
  · cases h_false

lemma blocking_prime_by_idx_1_prime (idx : ℕ) : Nat.Prime (blocking_prime_by_idx_1 idx) :=
  prime_of_mem_blocking_primes_1 (getD_mem blocking_primes_1 (idx - 100) 3)

lemma mod4_of_mem_blocking_primes_1 {p : ℕ} (h : p ∈ 3 :: blocking_primes_1) : p % 4 = 3 := by
  unfold blocking_primes_1 at h
  simp only [List.mem_cons] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | h_false
  · exact mod4_3
  · exact mod4_2339
  · exact mod4_7
  · exact mod4_71
  · exact mod4_23
  · exact mod4_11
  · exact mod4_47
  · exact mod4_239
  · exact mod4_7
  · exact mod4_5939
  · exact mod4_11
  · exact mod4_7
  · exact mod4_127
  · exact mod4_8191
  · exact mod4_7
  · exact mod4_11
  · exact mod4_1979
  · exact mod4_7
  · exact mod4_3739
  · exact mod4_127
  · exact mod4_7
  · exact mod4_3
  · exact mod4_59
  · exact mod4_71
  · exact mod4_3
  · exact mod4_151
  · exact mod4_4603
  · exact mod4_3
  · exact mod4_619
  · exact mod4_19
  · exact mod4_3
  · exact mod4_2731
  · exact mod4_9479
  · exact mod4_3
  · exact mod4_2267
  · exact mod4_331
  · exact mod4_3
  · exact mod4_811
  · exact mod4_19
  · exact mod4_3
  · exact mod4_151
  · exact mod4_683
  · exact mod4_3
  · exact mod4_4099
  · exact mod4_2731
  · exact mod4_3
  · exact mod4_9679
  · exact mod4_19
  · exact mod4_3
  · exact mod4_71
  · exact mod4_331
  · exact mod4_3
  · exact mod4_683
  · exact mod4_9419
  · exact mod4_3
  · exact mod4_151
  · exact mod4_19
  · exact mod4_3
  · exact mod4_71
  · exact mod4_1531
  · exact mod4_3
  · exact mod4_3
  · exact mod4_67
  · exact mod4_107
  · exact mod4_3
  · exact mod4_167
  · exact mod4_8179
  · exact mod4_3
  · exact mod4_271
  · exact mod4_31
  · exact mod4_3
  · exact mod4_23
  · exact mod4_271
  · exact mod4_3
  · exact mod4_31
  · exact mod4_9391
  · exact mod4_3
  · exact mod4_5231
  · exact mod4_367
  · exact mod4_3
  · exact mod4_431
  · exact mod4_2971
  · exact mod4_3
  · exact mod4_919
  · exact mod4_31
  · exact mod4_3
  · exact mod4_4783
  · exact mod4_10567
  · exact mod4_3
  · exact mod4_31
  · exact mod4_6011
  · exact mod4_3
  · exact mod4_6883
  · exact mod4_23
  · exact mod4_3
  · exact mod4_67
  · exact mod4_103
  · exact mod4_3
  · exact mod4_3163
  · exact mod4_31
  · exact mod4_3
  · cases h_false

lemma blocking_prime_by_idx_1_3mod4 (idx : ℕ) : blocking_prime_by_idx_1 idx % 4 = 3 :=
  mod4_of_mem_blocking_primes_1 (getD_mem blocking_primes_1 (idx - 100) 3)

def blocking_primes_2 : List ℕ := [11, 79, 31, 7, 223, 11, 7, 31, 6379, 7, 11, 11, 7, 4483, 3011, 7, 11, 31, 7, 43, 11, 11, 31, 547, 7, 11, 11, 7, 23, 787, 7, 11, 31, 7, 79, 11, 7, 31, 59, 7, 3, 103, 131, 3, 251, 23, 3, 1367, 10259, 3, 12959, 167, 3, 1447, 5179, 3, 23, 5591, 3, 67, 2143, 3, 59, 6203, 3, 8423, 1063, 3, 839, 251, 3, 6131, 67, 3, 587, 271, 3, 547, 23, 3, 3, 163, 59, 3, 11, 859, 3, 1699, 1103, 3, 4079, 2311, 3, 383, 11, 3, 2467, 11003, 3, 11]
def blocking_prime_by_idx_2 (idx : ℕ) : ℕ := blocking_primes_2.getD (idx - 200) 3

lemma prime_of_mem_blocking_primes_2 {p : ℕ} (h : p ∈ 3 :: blocking_primes_2) : Nat.Prime p := by
  unfold blocking_primes_2 at h
  simp only [List.mem_cons] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | h_false
  · exact prime_3
  · exact prime_11
  · exact prime_79
  · exact prime_31
  · exact prime_7
  · exact prime_223
  · exact prime_11
  · exact prime_7
  · exact prime_31
  · exact prime_6379
  · exact prime_7
  · exact prime_11
  · exact prime_11
  · exact prime_7
  · exact prime_4483
  · exact prime_3011
  · exact prime_7
  · exact prime_11
  · exact prime_31
  · exact prime_7
  · exact prime_43
  · exact prime_11
  · exact prime_11
  · exact prime_31
  · exact prime_547
  · exact prime_7
  · exact prime_11
  · exact prime_11
  · exact prime_7
  · exact prime_23
  · exact prime_787
  · exact prime_7
  · exact prime_11
  · exact prime_31
  · exact prime_7
  · exact prime_79
  · exact prime_11
  · exact prime_7
  · exact prime_31
  · exact prime_59
  · exact prime_7
  · exact prime_3
  · exact prime_103
  · exact prime_131
  · exact prime_3
  · exact prime_251
  · exact prime_23
  · exact prime_3
  · exact prime_1367
  · exact prime_10259
  · exact prime_3
  · exact prime_12959
  · exact prime_167
  · exact prime_3
  · exact prime_1447
  · exact prime_5179
  · exact prime_3
  · exact prime_23
  · exact prime_5591
  · exact prime_3
  · exact prime_67
  · exact prime_2143
  · exact prime_3
  · exact prime_59
  · exact prime_6203
  · exact prime_3
  · exact prime_8423
  · exact prime_1063
  · exact prime_3
  · exact prime_839
  · exact prime_251
  · exact prime_3
  · exact prime_6131
  · exact prime_67
  · exact prime_3
  · exact prime_587
  · exact prime_271
  · exact prime_3
  · exact prime_547
  · exact prime_23
  · exact prime_3
  · exact prime_3
  · exact prime_163
  · exact prime_59
  · exact prime_3
  · exact prime_11
  · exact prime_859
  · exact prime_3
  · exact prime_1699
  · exact prime_1103
  · exact prime_3
  · exact prime_4079
  · exact prime_2311
  · exact prime_3
  · exact prime_383
  · exact prime_11
  · exact prime_3
  · exact prime_2467
  · exact prime_11003
  · exact prime_3
  · exact prime_11
  · cases h_false

lemma blocking_prime_by_idx_2_prime (idx : ℕ) : Nat.Prime (blocking_prime_by_idx_2 idx) :=
  prime_of_mem_blocking_primes_2 (getD_mem blocking_primes_2 (idx - 200) 3)

lemma mod4_of_mem_blocking_primes_2 {p : ℕ} (h : p ∈ 3 :: blocking_primes_2) : p % 4 = 3 := by
  unfold blocking_primes_2 at h
  simp only [List.mem_cons] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | h_false
  · exact mod4_3
  · exact mod4_11
  · exact mod4_79
  · exact mod4_31
  · exact mod4_7
  · exact mod4_223
  · exact mod4_11
  · exact mod4_7
  · exact mod4_31
  · exact mod4_6379
  · exact mod4_7
  · exact mod4_11
  · exact mod4_11
  · exact mod4_7
  · exact mod4_4483
  · exact mod4_3011
  · exact mod4_7
  · exact mod4_11
  · exact mod4_31
  · exact mod4_7
  · exact mod4_43
  · exact mod4_11
  · exact mod4_11
  · exact mod4_31
  · exact mod4_547
  · exact mod4_7
  · exact mod4_11
  · exact mod4_11
  · exact mod4_7
  · exact mod4_23
  · exact mod4_787
  · exact mod4_7
  · exact mod4_11
  · exact mod4_31
  · exact mod4_7
  · exact mod4_79
  · exact mod4_11
  · exact mod4_7
  · exact mod4_31
  · exact mod4_59
  · exact mod4_7
  · exact mod4_3
  · exact mod4_103
  · exact mod4_131
  · exact mod4_3
  · exact mod4_251
  · exact mod4_23
  · exact mod4_3
  · exact mod4_1367
  · exact mod4_10259
  · exact mod4_3
  · exact mod4_12959
  · exact mod4_167
  · exact mod4_3
  · exact mod4_1447
  · exact mod4_5179
  · exact mod4_3
  · exact mod4_23
  · exact mod4_5591
  · exact mod4_3
  · exact mod4_67
  · exact mod4_2143
  · exact mod4_3
  · exact mod4_59
  · exact mod4_6203
  · exact mod4_3
  · exact mod4_8423
  · exact mod4_1063
  · exact mod4_3
  · exact mod4_839
  · exact mod4_251
  · exact mod4_3
  · exact mod4_6131
  · exact mod4_67
  · exact mod4_3
  · exact mod4_587
  · exact mod4_271
  · exact mod4_3
  · exact mod4_547
  · exact mod4_23
  · exact mod4_3
  · exact mod4_3
  · exact mod4_163
  · exact mod4_59
  · exact mod4_3
  · exact mod4_11
  · exact mod4_859
  · exact mod4_3
  · exact mod4_1699
  · exact mod4_1103
  · exact mod4_3
  · exact mod4_4079
  · exact mod4_2311
  · exact mod4_3
  · exact mod4_383
  · exact mod4_11
  · exact mod4_3
  · exact mod4_2467
  · exact mod4_11003
  · exact mod4_3
  · exact mod4_11
  · cases h_false

lemma blocking_prime_by_idx_2_3mod4 (idx : ℕ) : blocking_prime_by_idx_2 idx % 4 = 3 :=
  mod4_of_mem_blocking_primes_2 (getD_mem blocking_primes_2 (idx - 200) 3)

def blocking_primes_3 : List ℕ := [8831, 3, 14699, 3119, 3, 5347, 7187, 3, 887, 11, 3, 59, 883, 3, 11, 71, 3, 1103, 79, 3, 7, 191, 43, 7, 127, 1871, 7, 347, 659, 7, 79, 127, 7, 4451, 5419, 7, 43, 2887, 127, 3767, 7927, 7, 131, 43, 7, 127, 491, 7, 1151, 71, 7, 4259, 127, 7, 1291, 5419, 7, 43, 191, 127, 3, 199, 139, 3, 311, 811, 3, 79, 31, 3, 127, 2371, 3, 31, 6803, 3, 3319, 127, 3, 2939, 10111, 3, 1847, 31, 3, 9187, 7039, 3, 31, 3307, 3, 127, 4339, 3, 3727, 6067, 3, 1567, 31, 3]
def blocking_prime_by_idx_3 (idx : ℕ) : ℕ := blocking_primes_3.getD (idx - 300) 3

lemma prime_of_mem_blocking_primes_3 {p : ℕ} (h : p ∈ 3 :: blocking_primes_3) : Nat.Prime p := by
  unfold blocking_primes_3 at h
  simp only [List.mem_cons] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | h_false
  · exact prime_3
  · exact prime_8831
  · exact prime_3
  · exact prime_14699
  · exact prime_3119
  · exact prime_3
  · exact prime_5347
  · exact prime_7187
  · exact prime_3
  · exact prime_887
  · exact prime_11
  · exact prime_3
  · exact prime_59
  · exact prime_883
  · exact prime_3
  · exact prime_11
  · exact prime_71
  · exact prime_3
  · exact prime_1103
  · exact prime_79
  · exact prime_3
  · exact prime_7
  · exact prime_191
  · exact prime_43
  · exact prime_7
  · exact prime_127
  · exact prime_1871
  · exact prime_7
  · exact prime_347
  · exact prime_659
  · exact prime_7
  · exact prime_79
  · exact prime_127
  · exact prime_7
  · exact prime_4451
  · exact prime_5419
  · exact prime_7
  · exact prime_43
  · exact prime_2887
  · exact prime_127
  · exact prime_3767
  · exact prime_7927
  · exact prime_7
  · exact prime_131
  · exact prime_43
  · exact prime_7
  · exact prime_127
  · exact prime_491
  · exact prime_7
  · exact prime_1151
  · exact prime_71
  · exact prime_7
  · exact prime_4259
  · exact prime_127
  · exact prime_7
  · exact prime_1291
  · exact prime_5419
  · exact prime_7
  · exact prime_43
  · exact prime_191
  · exact prime_127
  · exact prime_3
  · exact prime_199
  · exact prime_139
  · exact prime_3
  · exact prime_311
  · exact prime_811
  · exact prime_3
  · exact prime_79
  · exact prime_31
  · exact prime_3
  · exact prime_127
  · exact prime_2371
  · exact prime_3
  · exact prime_31
  · exact prime_6803
  · exact prime_3
  · exact prime_3319
  · exact prime_127
  · exact prime_3
  · exact prime_2939
  · exact prime_10111
  · exact prime_3
  · exact prime_1847
  · exact prime_31
  · exact prime_3
  · exact prime_9187
  · exact prime_7039
  · exact prime_3
  · exact prime_31
  · exact prime_3307
  · exact prime_3
  · exact prime_127
  · exact prime_4339
  · exact prime_3
  · exact prime_3727
  · exact prime_6067
  · exact prime_3
  · exact prime_1567
  · exact prime_31
  · exact prime_3
  · cases h_false

lemma blocking_prime_by_idx_3_prime (idx : ℕ) : Nat.Prime (blocking_prime_by_idx_3 idx) :=
  prime_of_mem_blocking_primes_3 (getD_mem blocking_primes_3 (idx - 300) 3)

lemma mod4_of_mem_blocking_primes_3 {p : ℕ} (h : p ∈ 3 :: blocking_primes_3) : p % 4 = 3 := by
  unfold blocking_primes_3 at h
  simp only [List.mem_cons] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | h_false
  · exact mod4_3
  · exact mod4_8831
  · exact mod4_3
  · exact mod4_14699
  · exact mod4_3119
  · exact mod4_3
  · exact mod4_5347
  · exact mod4_7187
  · exact mod4_3
  · exact mod4_887
  · exact mod4_11
  · exact mod4_3
  · exact mod4_59
  · exact mod4_883
  · exact mod4_3
  · exact mod4_11
  · exact mod4_71
  · exact mod4_3
  · exact mod4_1103
  · exact mod4_79
  · exact mod4_3
  · exact mod4_7
  · exact mod4_191
  · exact mod4_43
  · exact mod4_7
  · exact mod4_127
  · exact mod4_1871
  · exact mod4_7
  · exact mod4_347
  · exact mod4_659
  · exact mod4_7
  · exact mod4_79
  · exact mod4_127
  · exact mod4_7
  · exact mod4_4451
  · exact mod4_5419
  · exact mod4_7
  · exact mod4_43
  · exact mod4_2887
  · exact mod4_127
  · exact mod4_3767
  · exact mod4_7927
  · exact mod4_7
  · exact mod4_131
  · exact mod4_43
  · exact mod4_7
  · exact mod4_127
  · exact mod4_491
  · exact mod4_7
  · exact mod4_1151
  · exact mod4_71
  · exact mod4_7
  · exact mod4_4259
  · exact mod4_127
  · exact mod4_7
  · exact mod4_1291
  · exact mod4_5419
  · exact mod4_7
  · exact mod4_43
  · exact mod4_191
  · exact mod4_127
  · exact mod4_3
  · exact mod4_199
  · exact mod4_139
  · exact mod4_3
  · exact mod4_311
  · exact mod4_811
  · exact mod4_3
  · exact mod4_79
  · exact mod4_31
  · exact mod4_3
  · exact mod4_127
  · exact mod4_2371
  · exact mod4_3
  · exact mod4_31
  · exact mod4_6803
  · exact mod4_3
  · exact mod4_3319
  · exact mod4_127
  · exact mod4_3
  · exact mod4_2939
  · exact mod4_10111
  · exact mod4_3
  · exact mod4_1847
  · exact mod4_31
  · exact mod4_3
  · exact mod4_9187
  · exact mod4_7039
  · exact mod4_3
  · exact mod4_31
  · exact mod4_3307
  · exact mod4_3
  · exact mod4_127
  · exact mod4_4339
  · exact mod4_3
  · exact mod4_3727
  · exact mod4_6067
  · exact mod4_3
  · exact mod4_1567
  · exact mod4_31
  · exact mod4_3
  · cases h_false

lemma blocking_prime_by_idx_3_3mod4 (idx : ℕ) : blocking_prime_by_idx_3 idx % 4 = 3 :=
  mod4_of_mem_blocking_primes_3 (getD_mem blocking_primes_3 (idx - 300) 3)

def blocking_primes_4 : List ℕ := [3, 11, 31, 3, 163, 11, 3, 31, 131, 3, 11, 11, 3, 683, 2531, 3, 2731, 31, 3, 19, 11, 3, 31, 7603, 3, 11, 11, 3, 19, 2731, 3, 11, 31, 3, 3847, 11, 3, 19, 3911, 3, 7, 227, 179, 7, 383, 47, 7, 1019, 191, 7, 3739, 151, 7, 71, 67, 4211, 227, 6367, 7, 107, 619, 7, 67, 379, 7, 4243, 151, 7, 47, 6599, 7, 15439, 283, 7, 3323, 211, 2887, 5479, 163, 7, 3, 263, 211, 3, 11, 43, 3, 2111, 19, 3, 1567, 2687, 3, 11003, 11, 3, 15991, 19, 3, 11]
def blocking_prime_by_idx_4 (idx : ℕ) : ℕ := blocking_primes_4.getD (idx - 400) 3

lemma prime_of_mem_blocking_primes_4 {p : ℕ} (h : p ∈ 3 :: blocking_primes_4) : Nat.Prime p := by
  unfold blocking_primes_4 at h
  simp only [List.mem_cons] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | h_false
  · exact prime_3
  · exact prime_3
  · exact prime_11
  · exact prime_31
  · exact prime_3
  · exact prime_163
  · exact prime_11
  · exact prime_3
  · exact prime_31
  · exact prime_131
  · exact prime_3
  · exact prime_11
  · exact prime_11
  · exact prime_3
  · exact prime_683
  · exact prime_2531
  · exact prime_3
  · exact prime_2731
  · exact prime_31
  · exact prime_3
  · exact prime_19
  · exact prime_11
  · exact prime_3
  · exact prime_31
  · exact prime_7603
  · exact prime_3
  · exact prime_11
  · exact prime_11
  · exact prime_3
  · exact prime_19
  · exact prime_2731
  · exact prime_3
  · exact prime_11
  · exact prime_31
  · exact prime_3
  · exact prime_3847
  · exact prime_11
  · exact prime_3
  · exact prime_19
  · exact prime_3911
  · exact prime_3
  · exact prime_7
  · exact prime_227
  · exact prime_179
  · exact prime_7
  · exact prime_383
  · exact prime_47
  · exact prime_7
  · exact prime_1019
  · exact prime_191
  · exact prime_7
  · exact prime_3739
  · exact prime_151
  · exact prime_7
  · exact prime_71
  · exact prime_67
  · exact prime_4211
  · exact prime_227
  · exact prime_6367
  · exact prime_7
  · exact prime_107
  · exact prime_619
  · exact prime_7
  · exact prime_67
  · exact prime_379
  · exact prime_7
  · exact prime_4243
  · exact prime_151
  · exact prime_7
  · exact prime_47
  · exact prime_6599
  · exact prime_7
  · exact prime_15439
  · exact prime_283
  · exact prime_7
  · exact prime_3323
  · exact prime_211
  · exact prime_2887
  · exact prime_5479
  · exact prime_163
  · exact prime_7
  · exact prime_3
  · exact prime_263
  · exact prime_211
  · exact prime_3
  · exact prime_11
  · exact prime_43
  · exact prime_3
  · exact prime_2111
  · exact prime_19
  · exact prime_3
  · exact prime_1567
  · exact prime_2687
  · exact prime_3
  · exact prime_11003
  · exact prime_11
  · exact prime_3
  · exact prime_15991
  · exact prime_19
  · exact prime_3
  · exact prime_11
  · cases h_false

lemma blocking_prime_by_idx_4_prime (idx : ℕ) : Nat.Prime (blocking_prime_by_idx_4 idx) :=
  prime_of_mem_blocking_primes_4 (getD_mem blocking_primes_4 (idx - 400) 3)

lemma mod4_of_mem_blocking_primes_4 {p : ℕ} (h : p ∈ 3 :: blocking_primes_4) : p % 4 = 3 := by
  unfold blocking_primes_4 at h
  simp only [List.mem_cons] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | h_false
  · exact mod4_3
  · exact mod4_3
  · exact mod4_11
  · exact mod4_31
  · exact mod4_3
  · exact mod4_163
  · exact mod4_11
  · exact mod4_3
  · exact mod4_31
  · exact mod4_131
  · exact mod4_3
  · exact mod4_11
  · exact mod4_11
  · exact mod4_3
  · exact mod4_683
  · exact mod4_2531
  · exact mod4_3
  · exact mod4_2731
  · exact mod4_31
  · exact mod4_3
  · exact mod4_19
  · exact mod4_11
  · exact mod4_3
  · exact mod4_31
  · exact mod4_7603
  · exact mod4_3
  · exact mod4_11
  · exact mod4_11
  · exact mod4_3
  · exact mod4_19
  · exact mod4_2731
  · exact mod4_3
  · exact mod4_11
  · exact mod4_31
  · exact mod4_3
  · exact mod4_3847
  · exact mod4_11
  · exact mod4_3
  · exact mod4_19
  · exact mod4_3911
  · exact mod4_3
  · exact mod4_7
  · exact mod4_227
  · exact mod4_179
  · exact mod4_7
  · exact mod4_383
  · exact mod4_47
  · exact mod4_7
  · exact mod4_1019
  · exact mod4_191
  · exact mod4_7
  · exact mod4_3739
  · exact mod4_151
  · exact mod4_7
  · exact mod4_71
  · exact mod4_67
  · exact mod4_4211
  · exact mod4_227
  · exact mod4_6367
  · exact mod4_7
  · exact mod4_107
  · exact mod4_619
  · exact mod4_7
  · exact mod4_67
  · exact mod4_379
  · exact mod4_7
  · exact mod4_4243
  · exact mod4_151
  · exact mod4_7
  · exact mod4_47
  · exact mod4_6599
  · exact mod4_7
  · exact mod4_15439
  · exact mod4_283
  · exact mod4_7
  · exact mod4_3323
  · exact mod4_211
  · exact mod4_2887
  · exact mod4_5479
  · exact mod4_163
  · exact mod4_7
  · exact mod4_3
  · exact mod4_263
  · exact mod4_211
  · exact mod4_3
  · exact mod4_11
  · exact mod4_43
  · exact mod4_3
  · exact mod4_2111
  · exact mod4_19
  · exact mod4_3
  · exact mod4_1567
  · exact mod4_2687
  · exact mod4_3
  · exact mod4_11003
  · exact mod4_11
  · exact mod4_3
  · exact mod4_15991
  · exact mod4_19
  · exact mod4_3
  · exact mod4_11
  · cases h_false

lemma blocking_prime_by_idx_4_3mod4 (idx : ℕ) : blocking_prime_by_idx_4 idx % 4 = 3 :=
  mod4_of_mem_blocking_primes_4 (getD_mem blocking_primes_4 (idx - 400) 3)

def blocking_primes_5 : List ℕ := [359, 3, 1439, 1831, 3, 2767, 19, 3, 8563, 11, 3, 6991, 12527, 3, 11, 19, 3, 1019, 2179, 3, 3, 23, 239, 3, 419, 4051, 3, 15391, 8539, 3, 3919, 4871, 3, 6343, 839, 3, 17239, 5347, 3, 3851, 10627, 3, 983, 23, 3, 131, 1399, 3, 1123, 8111, 3, 7727, 6047, 3, 23, 11587, 3, 107, 8291, 3, 7, 307, 379, 7, 463, 647, 7, 211, 31, 7, 6971, 2543, 3623, 31, 1931, 7, 163, 1163, 7, 227, 167, 7, 751, 31, 7, 547, 271, 7, 31, 83, 7, 683, 859, 31, 439, 3271, 7, 4591, 1667, 7]
def blocking_prime_by_idx_5 (idx : ℕ) : ℕ := blocking_primes_5.getD (idx - 500) 3

lemma prime_of_mem_blocking_primes_5 {p : ℕ} (h : p ∈ 3 :: blocking_primes_5) : Nat.Prime p := by
  unfold blocking_primes_5 at h
  simp only [List.mem_cons] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | h_false
  · exact prime_3
  · exact prime_359
  · exact prime_3
  · exact prime_1439
  · exact prime_1831
  · exact prime_3
  · exact prime_2767
  · exact prime_19
  · exact prime_3
  · exact prime_8563
  · exact prime_11
  · exact prime_3
  · exact prime_6991
  · exact prime_12527
  · exact prime_3
  · exact prime_11
  · exact prime_19
  · exact prime_3
  · exact prime_1019
  · exact prime_2179
  · exact prime_3
  · exact prime_3
  · exact prime_23
  · exact prime_239
  · exact prime_3
  · exact prime_419
  · exact prime_4051
  · exact prime_3
  · exact prime_15391
  · exact prime_8539
  · exact prime_3
  · exact prime_3919
  · exact prime_4871
  · exact prime_3
  · exact prime_6343
  · exact prime_839
  · exact prime_3
  · exact prime_17239
  · exact prime_5347
  · exact prime_3
  · exact prime_3851
  · exact prime_10627
  · exact prime_3
  · exact prime_983
  · exact prime_23
  · exact prime_3
  · exact prime_131
  · exact prime_1399
  · exact prime_3
  · exact prime_1123
  · exact prime_8111
  · exact prime_3
  · exact prime_7727
  · exact prime_6047
  · exact prime_3
  · exact prime_23
  · exact prime_11587
  · exact prime_3
  · exact prime_107
  · exact prime_8291
  · exact prime_3
  · exact prime_7
  · exact prime_307
  · exact prime_379
  · exact prime_7
  · exact prime_463
  · exact prime_647
  · exact prime_7
  · exact prime_211
  · exact prime_31
  · exact prime_7
  · exact prime_6971
  · exact prime_2543
  · exact prime_3623
  · exact prime_31
  · exact prime_1931
  · exact prime_7
  · exact prime_163
  · exact prime_1163
  · exact prime_7
  · exact prime_227
  · exact prime_167
  · exact prime_7
  · exact prime_751
  · exact prime_31
  · exact prime_7
  · exact prime_547
  · exact prime_271
  · exact prime_7
  · exact prime_31
  · exact prime_83
  · exact prime_7
  · exact prime_683
  · exact prime_859
  · exact prime_31
  · exact prime_439
  · exact prime_3271
  · exact prime_7
  · exact prime_4591
  · exact prime_1667
  · exact prime_7
  · cases h_false

lemma blocking_prime_by_idx_5_prime (idx : ℕ) : Nat.Prime (blocking_prime_by_idx_5 idx) :=
  prime_of_mem_blocking_primes_5 (getD_mem blocking_primes_5 (idx - 500) 3)

lemma mod4_of_mem_blocking_primes_5 {p : ℕ} (h : p ∈ 3 :: blocking_primes_5) : p % 4 = 3 := by
  unfold blocking_primes_5 at h
  simp only [List.mem_cons] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | h_false
  · exact mod4_3
  · exact mod4_359
  · exact mod4_3
  · exact mod4_1439
  · exact mod4_1831
  · exact mod4_3
  · exact mod4_2767
  · exact mod4_19
  · exact mod4_3
  · exact mod4_8563
  · exact mod4_11
  · exact mod4_3
  · exact mod4_6991
  · exact mod4_12527
  · exact mod4_3
  · exact mod4_11
  · exact mod4_19
  · exact mod4_3
  · exact mod4_1019
  · exact mod4_2179
  · exact mod4_3
  · exact mod4_3
  · exact mod4_23
  · exact mod4_239
  · exact mod4_3
  · exact mod4_419
  · exact mod4_4051
  · exact mod4_3
  · exact mod4_15391
  · exact mod4_8539
  · exact mod4_3
  · exact mod4_3919
  · exact mod4_4871
  · exact mod4_3
  · exact mod4_6343
  · exact mod4_839
  · exact mod4_3
  · exact mod4_17239
  · exact mod4_5347
  · exact mod4_3
  · exact mod4_3851
  · exact mod4_10627
  · exact mod4_3
  · exact mod4_983
  · exact mod4_23
  · exact mod4_3
  · exact mod4_131
  · exact mod4_1399
  · exact mod4_3
  · exact mod4_1123
  · exact mod4_8111
  · exact mod4_3
  · exact mod4_7727
  · exact mod4_6047
  · exact mod4_3
  · exact mod4_23
  · exact mod4_11587
  · exact mod4_3
  · exact mod4_107
  · exact mod4_8291
  · exact mod4_3
  · exact mod4_7
  · exact mod4_307
  · exact mod4_379
  · exact mod4_7
  · exact mod4_463
  · exact mod4_647
  · exact mod4_7
  · exact mod4_211
  · exact mod4_31
  · exact mod4_7
  · exact mod4_6971
  · exact mod4_2543
  · exact mod4_3623
  · exact mod4_31
  · exact mod4_1931
  · exact mod4_7
  · exact mod4_163
  · exact mod4_1163
  · exact mod4_7
  · exact mod4_227
  · exact mod4_167
  · exact mod4_7
  · exact mod4_751
  · exact mod4_31
  · exact mod4_7
  · exact mod4_547
  · exact mod4_271
  · exact mod4_7
  · exact mod4_31
  · exact mod4_83
  · exact mod4_7
  · exact mod4_683
  · exact mod4_859
  · exact mod4_31
  · exact mod4_439
  · exact mod4_3271
  · exact mod4_7
  · exact mod4_4591
  · exact mod4_1667
  · exact mod4_7
  · cases h_false

lemma blocking_prime_by_idx_5_3mod4 (idx : ℕ) : blocking_prime_by_idx_5 idx % 4 = 3 :=
  mod4_of_mem_blocking_primes_5 (getD_mem blocking_primes_5 (idx - 500) 3)

def blocking_primes_6 : List ℕ := [3, 11, 31, 3, 127, 11, 3, 31, 3323, 3, 11, 11, 3, 8467, 5927, 3, 11, 31, 3, 8191, 11, 3, 31, 43, 3, 11, 11, 3, 5419, 3167, 3, 3359, 31, 3, 6151, 11, 3, 31, 107, 3, 3, 331, 431, 3, 47, 3967, 3, 1283, 103, 3, 127, 23, 3, 6451, 983, 3, 331, 23, 3, 2579, 547, 3, 23, 2731, 3, 4799, 163, 3, 23, 107, 3, 127, 6871, 3, 9127, 5087, 3, 307, 127, 3, 7, 367, 443, 7, 11, 23, 7, 283, 2083, 11, 83, 5923, 7, 4027, 11, 7, 23, 8663, 7, 11]
def blocking_prime_by_idx_6 (idx : ℕ) : ℕ := blocking_primes_6.getD (idx - 600) 3

lemma prime_of_mem_blocking_primes_6 {p : ℕ} (h : p ∈ 3 :: blocking_primes_6) : Nat.Prime p := by
  unfold blocking_primes_6 at h
  simp only [List.mem_cons] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | h_false
  · exact prime_3
  · exact prime_3
  · exact prime_11
  · exact prime_31
  · exact prime_3
  · exact prime_127
  · exact prime_11
  · exact prime_3
  · exact prime_31
  · exact prime_3323
  · exact prime_3
  · exact prime_11
  · exact prime_11
  · exact prime_3
  · exact prime_8467
  · exact prime_5927
  · exact prime_3
  · exact prime_11
  · exact prime_31
  · exact prime_3
  · exact prime_8191
  · exact prime_11
  · exact prime_3
  · exact prime_31
  · exact prime_43
  · exact prime_3
  · exact prime_11
  · exact prime_11
  · exact prime_3
  · exact prime_5419
  · exact prime_3167
  · exact prime_3
  · exact prime_3359
  · exact prime_31
  · exact prime_3
  · exact prime_6151
  · exact prime_11
  · exact prime_3
  · exact prime_31
  · exact prime_107
  · exact prime_3
  · exact prime_3
  · exact prime_331
  · exact prime_431
  · exact prime_3
  · exact prime_47
  · exact prime_3967
  · exact prime_3
  · exact prime_1283
  · exact prime_103
  · exact prime_3
  · exact prime_127
  · exact prime_23
  · exact prime_3
  · exact prime_6451
  · exact prime_983
  · exact prime_3
  · exact prime_331
  · exact prime_23
  · exact prime_3
  · exact prime_2579
  · exact prime_547
  · exact prime_3
  · exact prime_23
  · exact prime_2731
  · exact prime_3
  · exact prime_4799
  · exact prime_163
  · exact prime_3
  · exact prime_23
  · exact prime_107
  · exact prime_3
  · exact prime_127
  · exact prime_6871
  · exact prime_3
  · exact prime_9127
  · exact prime_5087
  · exact prime_3
  · exact prime_307
  · exact prime_127
  · exact prime_3
  · exact prime_7
  · exact prime_367
  · exact prime_443
  · exact prime_7
  · exact prime_11
  · exact prime_23
  · exact prime_7
  · exact prime_283
  · exact prime_2083
  · exact prime_11
  · exact prime_83
  · exact prime_5923
  · exact prime_7
  · exact prime_4027
  · exact prime_11
  · exact prime_7
  · exact prime_23
  · exact prime_8663
  · exact prime_7
  · exact prime_11
  · cases h_false

lemma blocking_prime_by_idx_6_prime (idx : ℕ) : Nat.Prime (blocking_prime_by_idx_6 idx) :=
  prime_of_mem_blocking_primes_6 (getD_mem blocking_primes_6 (idx - 600) 3)

lemma mod4_of_mem_blocking_primes_6 {p : ℕ} (h : p ∈ 3 :: blocking_primes_6) : p % 4 = 3 := by
  unfold blocking_primes_6 at h
  simp only [List.mem_cons] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | h_false
  · exact mod4_3
  · exact mod4_3
  · exact mod4_11
  · exact mod4_31
  · exact mod4_3
  · exact mod4_127
  · exact mod4_11
  · exact mod4_3
  · exact mod4_31
  · exact mod4_3323
  · exact mod4_3
  · exact mod4_11
  · exact mod4_11
  · exact mod4_3
  · exact mod4_8467
  · exact mod4_5927
  · exact mod4_3
  · exact mod4_11
  · exact mod4_31
  · exact mod4_3
  · exact mod4_8191
  · exact mod4_11
  · exact mod4_3
  · exact mod4_31
  · exact mod4_43
  · exact mod4_3
  · exact mod4_11
  · exact mod4_11
  · exact mod4_3
  · exact mod4_5419
  · exact mod4_3167
  · exact mod4_3
  · exact mod4_3359
  · exact mod4_31
  · exact mod4_3
  · exact mod4_6151
  · exact mod4_11
  · exact mod4_3
  · exact mod4_31
  · exact mod4_107
  · exact mod4_3
  · exact mod4_3
  · exact mod4_331
  · exact mod4_431
  · exact mod4_3
  · exact mod4_47
  · exact mod4_3967
  · exact mod4_3
  · exact mod4_1283
  · exact mod4_103
  · exact mod4_3
  · exact mod4_127
  · exact mod4_23
  · exact mod4_3
  · exact mod4_6451
  · exact mod4_983
  · exact mod4_3
  · exact mod4_331
  · exact mod4_23
  · exact mod4_3
  · exact mod4_2579
  · exact mod4_547
  · exact mod4_3
  · exact mod4_23
  · exact mod4_2731
  · exact mod4_3
  · exact mod4_4799
  · exact mod4_163
  · exact mod4_3
  · exact mod4_23
  · exact mod4_107
  · exact mod4_3
  · exact mod4_127
  · exact mod4_6871
  · exact mod4_3
  · exact mod4_9127
  · exact mod4_5087
  · exact mod4_3
  · exact mod4_307
  · exact mod4_127
  · exact mod4_3
  · exact mod4_7
  · exact mod4_367
  · exact mod4_443
  · exact mod4_7
  · exact mod4_11
  · exact mod4_23
  · exact mod4_7
  · exact mod4_283
  · exact mod4_2083
  · exact mod4_11
  · exact mod4_83
  · exact mod4_5923
  · exact mod4_7
  · exact mod4_4027
  · exact mod4_11
  · exact mod4_7
  · exact mod4_23
  · exact mod4_8663
  · exact mod4_7
  · exact mod4_11
  · cases h_false

lemma blocking_prime_by_idx_6_3mod4 (idx : ℕ) : blocking_prime_by_idx_6 idx % 4 = 3 :=
  mod4_of_mem_blocking_primes_6 (getD_mem blocking_primes_6 (idx - 600) 3)

def blocking_primes_7 : List ℕ := [67, 7, 2659, 4639, 7, 7331, 14951, 7, 659, 11, 15671, 6691, 3719, 7, 2351, 3191, 7, 2887, 23, 7, 3, 439, 83, 3, 151, 103, 3, 1499, 1823, 3, 1543, 347, 3, 2039, 331, 3, 2707, 347, 3, 151, 2039, 3, 2711, 15439, 3, 379, 5171, 3, 2027, 103, 3, 79, 2371, 3, 151, 6043, 3, 1487, 131, 3, 3, 19, 487, 3, 467, 43, 3, 2711, 31, 3, 19, 10259, 3, 31, 3571, 3, 5483, 491, 3, 43, 8287, 3, 79, 31, 3, 619, 43, 3, 19, 11807, 3, 223, 4787, 3, 7963, 11239, 3, 19, 31, 3]
def blocking_prime_by_idx_7 (idx : ℕ) : ℕ := blocking_primes_7.getD (idx - 700) 3

lemma prime_of_mem_blocking_primes_7 {p : ℕ} (h : p ∈ 3 :: blocking_primes_7) : Nat.Prime p := by
  unfold blocking_primes_7 at h
  simp only [List.mem_cons] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | h_false
  · exact prime_3
  · exact prime_67
  · exact prime_7
  · exact prime_2659
  · exact prime_4639
  · exact prime_7
  · exact prime_7331
  · exact prime_14951
  · exact prime_7
  · exact prime_659
  · exact prime_11
  · exact prime_15671
  · exact prime_6691
  · exact prime_3719
  · exact prime_7
  · exact prime_2351
  · exact prime_3191
  · exact prime_7
  · exact prime_2887
  · exact prime_23
  · exact prime_7
  · exact prime_3
  · exact prime_439
  · exact prime_83
  · exact prime_3
  · exact prime_151
  · exact prime_103
  · exact prime_3
  · exact prime_1499
  · exact prime_1823
  · exact prime_3
  · exact prime_1543
  · exact prime_347
  · exact prime_3
  · exact prime_2039
  · exact prime_331
  · exact prime_3
  · exact prime_2707
  · exact prime_347
  · exact prime_3
  · exact prime_151
  · exact prime_2039
  · exact prime_3
  · exact prime_2711
  · exact prime_15439
  · exact prime_3
  · exact prime_379
  · exact prime_5171
  · exact prime_3
  · exact prime_2027
  · exact prime_103
  · exact prime_3
  · exact prime_79
  · exact prime_2371
  · exact prime_3
  · exact prime_151
  · exact prime_6043
  · exact prime_3
  · exact prime_1487
  · exact prime_131
  · exact prime_3
  · exact prime_3
  · exact prime_19
  · exact prime_487
  · exact prime_3
  · exact prime_467
  · exact prime_43
  · exact prime_3
  · exact prime_2711
  · exact prime_31
  · exact prime_3
  · exact prime_19
  · exact prime_10259
  · exact prime_3
  · exact prime_31
  · exact prime_3571
  · exact prime_3
  · exact prime_5483
  · exact prime_491
  · exact prime_3
  · exact prime_43
  · exact prime_8287
  · exact prime_3
  · exact prime_79
  · exact prime_31
  · exact prime_3
  · exact prime_619
  · exact prime_43
  · exact prime_3
  · exact prime_19
  · exact prime_11807
  · exact prime_3
  · exact prime_223
  · exact prime_4787
  · exact prime_3
  · exact prime_7963
  · exact prime_11239
  · exact prime_3
  · exact prime_19
  · exact prime_31
  · exact prime_3
  · cases h_false

lemma blocking_prime_by_idx_7_prime (idx : ℕ) : Nat.Prime (blocking_prime_by_idx_7 idx) :=
  prime_of_mem_blocking_primes_7 (getD_mem blocking_primes_7 (idx - 700) 3)

lemma mod4_of_mem_blocking_primes_7 {p : ℕ} (h : p ∈ 3 :: blocking_primes_7) : p % 4 = 3 := by
  unfold blocking_primes_7 at h
  simp only [List.mem_cons] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | h_false
  · exact mod4_3
  · exact mod4_67
  · exact mod4_7
  · exact mod4_2659
  · exact mod4_4639
  · exact mod4_7
  · exact mod4_7331
  · exact mod4_14951
  · exact mod4_7
  · exact mod4_659
  · exact mod4_11
  · exact mod4_15671
  · exact mod4_6691
  · exact mod4_3719
  · exact mod4_7
  · exact mod4_2351
  · exact mod4_3191
  · exact mod4_7
  · exact mod4_2887
  · exact mod4_23
  · exact mod4_7
  · exact mod4_3
  · exact mod4_439
  · exact mod4_83
  · exact mod4_3
  · exact mod4_151
  · exact mod4_103
  · exact mod4_3
  · exact mod4_1499
  · exact mod4_1823
  · exact mod4_3
  · exact mod4_1543
  · exact mod4_347
  · exact mod4_3
  · exact mod4_2039
  · exact mod4_331
  · exact mod4_3
  · exact mod4_2707
  · exact mod4_347
  · exact mod4_3
  · exact mod4_151
  · exact mod4_2039
  · exact mod4_3
  · exact mod4_2711
  · exact mod4_15439
  · exact mod4_3
  · exact mod4_379
  · exact mod4_5171
  · exact mod4_3
  · exact mod4_2027
  · exact mod4_103
  · exact mod4_3
  · exact mod4_79
  · exact mod4_2371
  · exact mod4_3
  · exact mod4_151
  · exact mod4_6043
  · exact mod4_3
  · exact mod4_1487
  · exact mod4_131
  · exact mod4_3
  · exact mod4_3
  · exact mod4_19
  · exact mod4_487
  · exact mod4_3
  · exact mod4_467
  · exact mod4_43
  · exact mod4_3
  · exact mod4_2711
  · exact mod4_31
  · exact mod4_3
  · exact mod4_19
  · exact mod4_10259
  · exact mod4_3
  · exact mod4_31
  · exact mod4_3571
  · exact mod4_3
  · exact mod4_5483
  · exact mod4_491
  · exact mod4_3
  · exact mod4_43
  · exact mod4_8287
  · exact mod4_3
  · exact mod4_79
  · exact mod4_31
  · exact mod4_3
  · exact mod4_619
  · exact mod4_43
  · exact mod4_3
  · exact mod4_19
  · exact mod4_11807
  · exact mod4_3
  · exact mod4_223
  · exact mod4_4787
  · exact mod4_3
  · exact mod4_7963
  · exact mod4_11239
  · exact mod4_3
  · exact mod4_19
  · exact mod4_31
  · exact mod4_3
  · cases h_false

lemma blocking_prime_by_idx_7_3mod4 (idx : ℕ) : blocking_prime_by_idx_7 idx % 4 = 3 :=
  mod4_of_mem_blocking_primes_7 (getD_mem blocking_primes_7 (idx - 700) 3)

def blocking_primes_8 : List ℕ := [7, 11, 31, 7, 479, 11, 11, 31, 11839, 7, 11, 11, 7, 3299, 2843, 7, 11, 31, 7, 4111, 11, 7, 31, 271, 7, 11, 11, 31, 283, 5591, 7, 11, 31, 7, 7559, 31, 7, 31, 811, 7, 3, 499, 491, 3, 523, 907, 3, 59, 6079, 3, 67, 10099, 3, 683, 971, 3, 2927, 19, 3, 4751, 4691, 3, 10691, 4663, 3, 3343, 19, 3, 5531, 883, 3, 191, 211, 3, 6803, 19, 3, 2551, 3539, 3, 3, 503, 43, 3, 11, 827, 3, 223, 15259, 3, 5351, 67, 3, 6011, 11, 3, 43, 59, 3, 11]
def blocking_prime_by_idx_8 (idx : ℕ) : ℕ := blocking_primes_8.getD (idx - 800) 3

lemma prime_of_mem_blocking_primes_8 {p : ℕ} (h : p ∈ 3 :: blocking_primes_8) : Nat.Prime p := by
  unfold blocking_primes_8 at h
  simp only [List.mem_cons] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | h_false
  · exact prime_3
  · exact prime_7
  · exact prime_11
  · exact prime_31
  · exact prime_7
  · exact prime_479
  · exact prime_11
  · exact prime_11
  · exact prime_31
  · exact prime_11839
  · exact prime_7
  · exact prime_11
  · exact prime_11
  · exact prime_7
  · exact prime_3299
  · exact prime_2843
  · exact prime_7
  · exact prime_11
  · exact prime_31
  · exact prime_7
  · exact prime_4111
  · exact prime_11
  · exact prime_7
  · exact prime_31
  · exact prime_271
  · exact prime_7
  · exact prime_11
  · exact prime_11
  · exact prime_31
  · exact prime_283
  · exact prime_5591
  · exact prime_7
  · exact prime_11
  · exact prime_31
  · exact prime_7
  · exact prime_7559
  · exact prime_31
  · exact prime_7
  · exact prime_31
  · exact prime_811
  · exact prime_7
  · exact prime_3
  · exact prime_499
  · exact prime_491
  · exact prime_3
  · exact prime_523
  · exact prime_907
  · exact prime_3
  · exact prime_59
  · exact prime_6079
  · exact prime_3
  · exact prime_67
  · exact prime_10099
  · exact prime_3
  · exact prime_683
  · exact prime_971
  · exact prime_3
  · exact prime_2927
  · exact prime_19
  · exact prime_3
  · exact prime_4751
  · exact prime_4691
  · exact prime_3
  · exact prime_10691
  · exact prime_4663
  · exact prime_3
  · exact prime_3343
  · exact prime_19
  · exact prime_3
  · exact prime_5531
  · exact prime_883
  · exact prime_3
  · exact prime_191
  · exact prime_211
  · exact prime_3
  · exact prime_6803
  · exact prime_19
  · exact prime_3
  · exact prime_2551
  · exact prime_3539
  · exact prime_3
  · exact prime_3
  · exact prime_503
  · exact prime_43
  · exact prime_3
  · exact prime_11
  · exact prime_827
  · exact prime_3
  · exact prime_223
  · exact prime_15259
  · exact prime_3
  · exact prime_5351
  · exact prime_67
  · exact prime_3
  · exact prime_6011
  · exact prime_11
  · exact prime_3
  · exact prime_43
  · exact prime_59
  · exact prime_3
  · exact prime_11
  · cases h_false

lemma blocking_prime_by_idx_8_prime (idx : ℕ) : Nat.Prime (blocking_prime_by_idx_8 idx) :=
  prime_of_mem_blocking_primes_8 (getD_mem blocking_primes_8 (idx - 800) 3)

lemma mod4_of_mem_blocking_primes_8 {p : ℕ} (h : p ∈ 3 :: blocking_primes_8) : p % 4 = 3 := by
  unfold blocking_primes_8 at h
  simp only [List.mem_cons] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | h_false
  · exact mod4_3
  · exact mod4_7
  · exact mod4_11
  · exact mod4_31
  · exact mod4_7
  · exact mod4_479
  · exact mod4_11
  · exact mod4_11
  · exact mod4_31
  · exact mod4_11839
  · exact mod4_7
  · exact mod4_11
  · exact mod4_11
  · exact mod4_7
  · exact mod4_3299
  · exact mod4_2843
  · exact mod4_7
  · exact mod4_11
  · exact mod4_31
  · exact mod4_7
  · exact mod4_4111
  · exact mod4_11
  · exact mod4_7
  · exact mod4_31
  · exact mod4_271
  · exact mod4_7
  · exact mod4_11
  · exact mod4_11
  · exact mod4_31
  · exact mod4_283
  · exact mod4_5591
  · exact mod4_7
  · exact mod4_11
  · exact mod4_31
  · exact mod4_7
  · exact mod4_7559
  · exact mod4_31
  · exact mod4_7
  · exact mod4_31
  · exact mod4_811
  · exact mod4_7
  · exact mod4_3
  · exact mod4_499
  · exact mod4_491
  · exact mod4_3
  · exact mod4_523
  · exact mod4_907
  · exact mod4_3
  · exact mod4_59
  · exact mod4_6079
  · exact mod4_3
  · exact mod4_67
  · exact mod4_10099
  · exact mod4_3
  · exact mod4_683
  · exact mod4_971
  · exact mod4_3
  · exact mod4_2927
  · exact mod4_19
  · exact mod4_3
  · exact mod4_4751
  · exact mod4_4691
  · exact mod4_3
  · exact mod4_10691
  · exact mod4_4663
  · exact mod4_3
  · exact mod4_3343
  · exact mod4_19
  · exact mod4_3
  · exact mod4_5531
  · exact mod4_883
  · exact mod4_3
  · exact mod4_191
  · exact mod4_211
  · exact mod4_3
  · exact mod4_6803
  · exact mod4_19
  · exact mod4_3
  · exact mod4_2551
  · exact mod4_3539
  · exact mod4_3
  · exact mod4_3
  · exact mod4_503
  · exact mod4_43
  · exact mod4_3
  · exact mod4_11
  · exact mod4_827
  · exact mod4_3
  · exact mod4_223
  · exact mod4_15259
  · exact mod4_3
  · exact mod4_5351
  · exact mod4_67
  · exact mod4_3
  · exact mod4_6011
  · exact mod4_11
  · exact mod4_3
  · exact mod4_43
  · exact mod4_59
  · exact mod4_3
  · exact mod4_11
  · cases h_false

lemma blocking_prime_by_idx_8_3mod4 (idx : ℕ) : blocking_prime_by_idx_8 idx % 4 = 3 :=
  mod4_of_mem_blocking_primes_8 (getD_mem blocking_primes_8 (idx - 800) 3)

def blocking_primes_9 : List ℕ := [5711, 3, 13367, 43, 3, 127, 3659, 3, 271, 11, 3, 691, 127, 3, 11, 6863, 3, 43, 12163, 3, 7, 587, 563, 59, 571, 2819, 7, 4691, 223, 7, 127, 14939, 7, 8179, 6491, 7, 103, 127, 7, 4339, 59, 7, 11279, 5623, 127, 1871, 2347, 7, 691, 2731, 7, 127, 59, 7, 2383, 1987, 7, 4523, 127, 7, 3, 23, 631, 3, 599, 4139, 3, 71, 31, 3, 8647, 1423, 3, 31, 11519, 3, 739, 47, 3, 47, 107, 3, 1783, 31, 3, 83, 2683, 3, 31, 8971, 3, 5303, 827, 3, 23, 3967, 3, 419, 31, 3]
def blocking_prime_by_idx_9 (idx : ℕ) : ℕ := blocking_primes_9.getD (idx - 900) 3

lemma prime_of_mem_blocking_primes_9 {p : ℕ} (h : p ∈ 3 :: blocking_primes_9) : Nat.Prime p := by
  unfold blocking_primes_9 at h
  simp only [List.mem_cons] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | h_false
  · exact prime_3
  · exact prime_5711
  · exact prime_3
  · exact prime_13367
  · exact prime_43
  · exact prime_3
  · exact prime_127
  · exact prime_3659
  · exact prime_3
  · exact prime_271
  · exact prime_11
  · exact prime_3
  · exact prime_691
  · exact prime_127
  · exact prime_3
  · exact prime_11
  · exact prime_6863
  · exact prime_3
  · exact prime_43
  · exact prime_12163
  · exact prime_3
  · exact prime_7
  · exact prime_587
  · exact prime_563
  · exact prime_59
  · exact prime_571
  · exact prime_2819
  · exact prime_7
  · exact prime_4691
  · exact prime_223
  · exact prime_7
  · exact prime_127
  · exact prime_14939
  · exact prime_7
  · exact prime_8179
  · exact prime_6491
  · exact prime_7
  · exact prime_103
  · exact prime_127
  · exact prime_7
  · exact prime_4339
  · exact prime_59
  · exact prime_7
  · exact prime_11279
  · exact prime_5623
  · exact prime_127
  · exact prime_1871
  · exact prime_2347
  · exact prime_7
  · exact prime_691
  · exact prime_2731
  · exact prime_7
  · exact prime_127
  · exact prime_59
  · exact prime_7
  · exact prime_2383
  · exact prime_1987
  · exact prime_7
  · exact prime_4523
  · exact prime_127
  · exact prime_7
  · exact prime_3
  · exact prime_23
  · exact prime_631
  · exact prime_3
  · exact prime_599
  · exact prime_4139
  · exact prime_3
  · exact prime_71
  · exact prime_31
  · exact prime_3
  · exact prime_8647
  · exact prime_1423
  · exact prime_3
  · exact prime_31
  · exact prime_11519
  · exact prime_3
  · exact prime_739
  · exact prime_47
  · exact prime_3
  · exact prime_47
  · exact prime_107
  · exact prime_3
  · exact prime_1783
  · exact prime_31
  · exact prime_3
  · exact prime_83
  · exact prime_2683
  · exact prime_3
  · exact prime_31
  · exact prime_8971
  · exact prime_3
  · exact prime_5303
  · exact prime_827
  · exact prime_3
  · exact prime_23
  · exact prime_3967
  · exact prime_3
  · exact prime_419
  · exact prime_31
  · exact prime_3
  · cases h_false

lemma blocking_prime_by_idx_9_prime (idx : ℕ) : Nat.Prime (blocking_prime_by_idx_9 idx) :=
  prime_of_mem_blocking_primes_9 (getD_mem blocking_primes_9 (idx - 900) 3)

lemma mod4_of_mem_blocking_primes_9 {p : ℕ} (h : p ∈ 3 :: blocking_primes_9) : p % 4 = 3 := by
  unfold blocking_primes_9 at h
  simp only [List.mem_cons] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | h_false
  · exact mod4_3
  · exact mod4_5711
  · exact mod4_3
  · exact mod4_13367
  · exact mod4_43
  · exact mod4_3
  · exact mod4_127
  · exact mod4_3659
  · exact mod4_3
  · exact mod4_271
  · exact mod4_11
  · exact mod4_3
  · exact mod4_691
  · exact mod4_127
  · exact mod4_3
  · exact mod4_11
  · exact mod4_6863
  · exact mod4_3
  · exact mod4_43
  · exact mod4_12163
  · exact mod4_3
  · exact mod4_7
  · exact mod4_587
  · exact mod4_563
  · exact mod4_59
  · exact mod4_571
  · exact mod4_2819
  · exact mod4_7
  · exact mod4_4691
  · exact mod4_223
  · exact mod4_7
  · exact mod4_127
  · exact mod4_14939
  · exact mod4_7
  · exact mod4_8179
  · exact mod4_6491
  · exact mod4_7
  · exact mod4_103
  · exact mod4_127
  · exact mod4_7
  · exact mod4_4339
  · exact mod4_59
  · exact mod4_7
  · exact mod4_11279
  · exact mod4_5623
  · exact mod4_127
  · exact mod4_1871
  · exact mod4_2347
  · exact mod4_7
  · exact mod4_691
  · exact mod4_2731
  · exact mod4_7
  · exact mod4_127
  · exact mod4_59
  · exact mod4_7
  · exact mod4_2383
  · exact mod4_1987
  · exact mod4_7
  · exact mod4_4523
  · exact mod4_127
  · exact mod4_7
  · exact mod4_3
  · exact mod4_23
  · exact mod4_631
  · exact mod4_3
  · exact mod4_599
  · exact mod4_4139
  · exact mod4_3
  · exact mod4_71
  · exact mod4_31
  · exact mod4_3
  · exact mod4_8647
  · exact mod4_1423
  · exact mod4_3
  · exact mod4_31
  · exact mod4_11519
  · exact mod4_3
  · exact mod4_739
  · exact mod4_47
  · exact mod4_3
  · exact mod4_47
  · exact mod4_107
  · exact mod4_3
  · exact mod4_1783
  · exact mod4_31
  · exact mod4_3
  · exact mod4_83
  · exact mod4_2683
  · exact mod4_3
  · exact mod4_31
  · exact mod4_8971
  · exact mod4_3
  · exact mod4_5303
  · exact mod4_827
  · exact mod4_3
  · exact mod4_23
  · exact mod4_3967
  · exact mod4_3
  · exact mod4_419
  · exact mod4_31
  · exact mod4_3
  · cases h_false

lemma blocking_prime_by_idx_9_3mod4 (idx : ℕ) : blocking_prime_by_idx_9 idx % 4 = 3 :=
  mod4_of_mem_blocking_primes_9 (getD_mem blocking_primes_9 (idx - 900) 3)

def blocking_primes_10 : List ℕ := [3, 11, 31, 3, 71, 11, 3, 31, 863, 3, 11, 11, 3, 4591, 2683, 3, 11, 31, 3, 13367, 11, 3, 31, 967, 3, 11, 11, 3, 1847, 59, 3, 11, 31, 3, 59, 11, 3, 31, 547, 3, 719, 643, 2347, 7, 2543, 43, 7, 7951, 9203, 7, 23, 151, 7, 3331, 863, 7, 131, 1303, 7, 43, 4567, 23, 2699, 167, 7, 587, 43, 7, 1523, 191, 7, 6791, 23, 7, 3547, 4523, 7, 7907, 3407, 7, 3, 11119, 911, 3, 11, 8963, 3, 8191, 59, 3, 1063, 23, 3, 107, 359, 3, 199, 3623, 3, 11]
def blocking_prime_by_idx_10 (idx : ℕ) : ℕ := blocking_primes_10.getD (idx - 1000) 3

lemma prime_of_mem_blocking_primes_10 {p : ℕ} (h : p ∈ 3 :: blocking_primes_10) : Nat.Prime p := by
  unfold blocking_primes_10 at h
  simp only [List.mem_cons] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | h_false
  · exact prime_3
  · exact prime_3
  · exact prime_11
  · exact prime_31
  · exact prime_3
  · exact prime_71
  · exact prime_11
  · exact prime_3
  · exact prime_31
  · exact prime_863
  · exact prime_3
  · exact prime_11
  · exact prime_11
  · exact prime_3
  · exact prime_4591
  · exact prime_2683
  · exact prime_3
  · exact prime_11
  · exact prime_31
  · exact prime_3
  · exact prime_13367
  · exact prime_11
  · exact prime_3
  · exact prime_31
  · exact prime_967
  · exact prime_3
  · exact prime_11
  · exact prime_11
  · exact prime_3
  · exact prime_1847
  · exact prime_59
  · exact prime_3
  · exact prime_11
  · exact prime_31
  · exact prime_3
  · exact prime_59
  · exact prime_11
  · exact prime_3
  · exact prime_31
  · exact prime_547
  · exact prime_3
  · exact prime_719
  · exact prime_643
  · exact prime_2347
  · exact prime_7
  · exact prime_2543
  · exact prime_43
  · exact prime_7
  · exact prime_7951
  · exact prime_9203
  · exact prime_7
  · exact prime_23
  · exact prime_151
  · exact prime_7
  · exact prime_3331
  · exact prime_863
  · exact prime_7
  · exact prime_131
  · exact prime_1303
  · exact prime_7
  · exact prime_43
  · exact prime_4567
  · exact prime_23
  · exact prime_2699
  · exact prime_167
  · exact prime_7
  · exact prime_587
  · exact prime_43
  · exact prime_7
  · exact prime_1523
  · exact prime_191
  · exact prime_7
  · exact prime_6791
  · exact prime_23
  · exact prime_7
  · exact prime_3547
  · exact prime_4523
  · exact prime_7
  · exact prime_7907
  · exact prime_3407
  · exact prime_7
  · exact prime_3
  · exact prime_11119
  · exact prime_911
  · exact prime_3
  · exact prime_11
  · exact prime_8963
  · exact prime_3
  · exact prime_8191
  · exact prime_59
  · exact prime_3
  · exact prime_1063
  · exact prime_23
  · exact prime_3
  · exact prime_107
  · exact prime_359
  · exact prime_3
  · exact prime_199
  · exact prime_3623
  · exact prime_3
  · exact prime_11
  · cases h_false

lemma blocking_prime_by_idx_10_prime (idx : ℕ) : Nat.Prime (blocking_prime_by_idx_10 idx) :=
  prime_of_mem_blocking_primes_10 (getD_mem blocking_primes_10 (idx - 1000) 3)

lemma mod4_of_mem_blocking_primes_10 {p : ℕ} (h : p ∈ 3 :: blocking_primes_10) : p % 4 = 3 := by
  unfold blocking_primes_10 at h
  simp only [List.mem_cons] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | h_false
  · exact mod4_3
  · exact mod4_3
  · exact mod4_11
  · exact mod4_31
  · exact mod4_3
  · exact mod4_71
  · exact mod4_11
  · exact mod4_3
  · exact mod4_31
  · exact mod4_863
  · exact mod4_3
  · exact mod4_11
  · exact mod4_11
  · exact mod4_3
  · exact mod4_4591
  · exact mod4_2683
  · exact mod4_3
  · exact mod4_11
  · exact mod4_31
  · exact mod4_3
  · exact mod4_13367
  · exact mod4_11
  · exact mod4_3
  · exact mod4_31
  · exact mod4_967
  · exact mod4_3
  · exact mod4_11
  · exact mod4_11
  · exact mod4_3
  · exact mod4_1847
  · exact mod4_59
  · exact mod4_3
  · exact mod4_11
  · exact mod4_31
  · exact mod4_3
  · exact mod4_59
  · exact mod4_11
  · exact mod4_3
  · exact mod4_31
  · exact mod4_547
  · exact mod4_3
  · exact mod4_719
  · exact mod4_643
  · exact mod4_2347
  · exact mod4_7
  · exact mod4_2543
  · exact mod4_43
  · exact mod4_7
  · exact mod4_7951
  · exact mod4_9203
  · exact mod4_7
  · exact mod4_23
  · exact mod4_151
  · exact mod4_7
  · exact mod4_3331
  · exact mod4_863
  · exact mod4_7
  · exact mod4_131
  · exact mod4_1303
  · exact mod4_7
  · exact mod4_43
  · exact mod4_4567
  · exact mod4_23
  · exact mod4_2699
  · exact mod4_167
  · exact mod4_7
  · exact mod4_587
  · exact mod4_43
  · exact mod4_7
  · exact mod4_1523
  · exact mod4_191
  · exact mod4_7
  · exact mod4_6791
  · exact mod4_23
  · exact mod4_7
  · exact mod4_3547
  · exact mod4_4523
  · exact mod4_7
  · exact mod4_7907
  · exact mod4_3407
  · exact mod4_7
  · exact mod4_3
  · exact mod4_11119
  · exact mod4_911
  · exact mod4_3
  · exact mod4_11
  · exact mod4_8963
  · exact mod4_3
  · exact mod4_8191
  · exact mod4_59
  · exact mod4_3
  · exact mod4_1063
  · exact mod4_23
  · exact mod4_3
  · exact mod4_107
  · exact mod4_359
  · exact mod4_3
  · exact mod4_199
  · exact mod4_3623
  · exact mod4_3
  · exact mod4_11
  · cases h_false

lemma blocking_prime_by_idx_10_3mod4 (idx : ℕ) : blocking_prime_by_idx_10 idx % 4 = 3 :=
  mod4_of_mem_blocking_primes_10 (getD_mem blocking_primes_10 (idx - 1000) 3)

def blocking_primes_11 : List ℕ := [191, 3, 23, 14563, 3, 12899, 3947, 3, 23, 11, 3, 3767, 5711, 3, 11, 3547, 3, 59, 12899, 3, 3, 19, 2287, 3, 4159, 23, 3, 463, 5647, 3, 19, 307, 3, 4547, 823, 3, 23, 2707, 3, 19, 14951, 3, 8599, 1879, 3, 431, 103, 3, 19, 79, 3, 1663, 8191, 3, 14411, 6907, 3, 19, 23, 3, 7, 1051, 43, 7, 127, 131, 7, 4271, 31, 7, 2731, 127, 7, 31, 5419, 7, 43, 5011, 31, 283, 2179, 7, 7219, 31, 7, 103, 59, 7, 31, 10271, 7, 1787, 127, 7, 691, 5419, 7, 43, 31, 127]
def blocking_prime_by_idx_11 (idx : ℕ) : ℕ := blocking_primes_11.getD (idx - 1100) 3

lemma prime_of_mem_blocking_primes_11 {p : ℕ} (h : p ∈ 3 :: blocking_primes_11) : Nat.Prime p := by
  unfold blocking_primes_11 at h
  simp only [List.mem_cons] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | h_false
  · exact prime_3
  · exact prime_191
  · exact prime_3
  · exact prime_23
  · exact prime_14563
  · exact prime_3
  · exact prime_12899
  · exact prime_3947
  · exact prime_3
  · exact prime_23
  · exact prime_11
  · exact prime_3
  · exact prime_3767
  · exact prime_5711
  · exact prime_3
  · exact prime_11
  · exact prime_3547
  · exact prime_3
  · exact prime_59
  · exact prime_12899
  · exact prime_3
  · exact prime_3
  · exact prime_19
  · exact prime_2287
  · exact prime_3
  · exact prime_4159
  · exact prime_23
  · exact prime_3
  · exact prime_463
  · exact prime_5647
  · exact prime_3
  · exact prime_19
  · exact prime_307
  · exact prime_3
  · exact prime_4547
  · exact prime_823
  · exact prime_3
  · exact prime_23
  · exact prime_2707
  · exact prime_3
  · exact prime_19
  · exact prime_14951
  · exact prime_3
  · exact prime_8599
  · exact prime_1879
  · exact prime_3
  · exact prime_431
  · exact prime_103
  · exact prime_3
  · exact prime_19
  · exact prime_79
  · exact prime_3
  · exact prime_1663
  · exact prime_8191
  · exact prime_3
  · exact prime_14411
  · exact prime_6907
  · exact prime_3
  · exact prime_19
  · exact prime_23
  · exact prime_3
  · exact prime_7
  · exact prime_1051
  · exact prime_43
  · exact prime_7
  · exact prime_127
  · exact prime_131
  · exact prime_7
  · exact prime_4271
  · exact prime_31
  · exact prime_7
  · exact prime_2731
  · exact prime_127
  · exact prime_7
  · exact prime_31
  · exact prime_5419
  · exact prime_7
  · exact prime_43
  · exact prime_5011
  · exact prime_31
  · exact prime_283
  · exact prime_2179
  · exact prime_7
  · exact prime_7219
  · exact prime_31
  · exact prime_7
  · exact prime_103
  · exact prime_59
  · exact prime_7
  · exact prime_31
  · exact prime_10271
  · exact prime_7
  · exact prime_1787
  · exact prime_127
  · exact prime_7
  · exact prime_691
  · exact prime_5419
  · exact prime_7
  · exact prime_43
  · exact prime_31
  · exact prime_127
  · cases h_false

lemma blocking_prime_by_idx_11_prime (idx : ℕ) : Nat.Prime (blocking_prime_by_idx_11 idx) :=
  prime_of_mem_blocking_primes_11 (getD_mem blocking_primes_11 (idx - 1100) 3)

lemma mod4_of_mem_blocking_primes_11 {p : ℕ} (h : p ∈ 3 :: blocking_primes_11) : p % 4 = 3 := by
  unfold blocking_primes_11 at h
  simp only [List.mem_cons] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | h_false
  · exact mod4_3
  · exact mod4_191
  · exact mod4_3
  · exact mod4_23
  · exact mod4_14563
  · exact mod4_3
  · exact mod4_12899
  · exact mod4_3947
  · exact mod4_3
  · exact mod4_23
  · exact mod4_11
  · exact mod4_3
  · exact mod4_3767
  · exact mod4_5711
  · exact mod4_3
  · exact mod4_11
  · exact mod4_3547
  · exact mod4_3
  · exact mod4_59
  · exact mod4_12899
  · exact mod4_3
  · exact mod4_3
  · exact mod4_19
  · exact mod4_2287
  · exact mod4_3
  · exact mod4_4159
  · exact mod4_23
  · exact mod4_3
  · exact mod4_463
  · exact mod4_5647
  · exact mod4_3
  · exact mod4_19
  · exact mod4_307
  · exact mod4_3
  · exact mod4_4547
  · exact mod4_823
  · exact mod4_3
  · exact mod4_23
  · exact mod4_2707
  · exact mod4_3
  · exact mod4_19
  · exact mod4_14951
  · exact mod4_3
  · exact mod4_8599
  · exact mod4_1879
  · exact mod4_3
  · exact mod4_431
  · exact mod4_103
  · exact mod4_3
  · exact mod4_19
  · exact mod4_79
  · exact mod4_3
  · exact mod4_1663
  · exact mod4_8191
  · exact mod4_3
  · exact mod4_14411
  · exact mod4_6907
  · exact mod4_3
  · exact mod4_19
  · exact mod4_23
  · exact mod4_3
  · exact mod4_7
  · exact mod4_1051
  · exact mod4_43
  · exact mod4_7
  · exact mod4_127
  · exact mod4_131
  · exact mod4_7
  · exact mod4_4271
  · exact mod4_31
  · exact mod4_7
  · exact mod4_2731
  · exact mod4_127
  · exact mod4_7
  · exact mod4_31
  · exact mod4_5419
  · exact mod4_7
  · exact mod4_43
  · exact mod4_5011
  · exact mod4_31
  · exact mod4_283
  · exact mod4_2179
  · exact mod4_7
  · exact mod4_7219
  · exact mod4_31
  · exact mod4_7
  · exact mod4_103
  · exact mod4_59
  · exact mod4_7
  · exact mod4_31
  · exact mod4_10271
  · exact mod4_7
  · exact mod4_1787
  · exact mod4_127
  · exact mod4_7
  · exact mod4_691
  · exact mod4_5419
  · exact mod4_7
  · exact mod4_43
  · exact mod4_31
  · exact mod4_127
  · cases h_false

lemma blocking_prime_by_idx_11_3mod4 (idx : ℕ) : blocking_prime_by_idx_11 idx % 4 = 3 :=
  mod4_of_mem_blocking_primes_11 (getD_mem blocking_primes_11 (idx - 1100) 3)

def blocking_primes_12 : List ℕ := [3, 11, 31, 3, 8971, 11, 3, 31, 19, 3, 11, 11, 3, 5783, 719, 3, 11, 19, 3, 487, 11, 3, 31, 5399, 3, 31, 11, 3, 4007, 5851, 3, 11, 31, 3, 5503, 11, 3, 31, 127, 3, 3, 83, 4447, 3, 251, 239, 3, 1319, 967, 3, 2111, 463, 3, 2399, 139, 3, 307, 11471, 3, 4327, 1907, 3, 15887, 4943, 3, 4127, 4327, 3, 2851, 251, 3, 331, 1423, 3, 2539, 5651, 3, 1559, 911, 3, 7, 59, 683, 7, 2083, 1051, 7, 2063, 1723, 7, 919, 14683, 7, 683, 11, 19739, 3607, 9767, 7, 11]
def blocking_prime_by_idx_12 (idx : ℕ) : ℕ := blocking_primes_12.getD (idx - 1200) 3

lemma prime_of_mem_blocking_primes_12 {p : ℕ} (h : p ∈ 3 :: blocking_primes_12) : Nat.Prime p := by
  unfold blocking_primes_12 at h
  simp only [List.mem_cons] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | h_false
  · exact prime_3
  · exact prime_3
  · exact prime_11
  · exact prime_31
  · exact prime_3
  · exact prime_8971
  · exact prime_11
  · exact prime_3
  · exact prime_31
  · exact prime_19
  · exact prime_3
  · exact prime_11
  · exact prime_11
  · exact prime_3
  · exact prime_5783
  · exact prime_719
  · exact prime_3
  · exact prime_11
  · exact prime_19
  · exact prime_3
  · exact prime_487
  · exact prime_11
  · exact prime_3
  · exact prime_31
  · exact prime_5399
  · exact prime_3
  · exact prime_31
  · exact prime_11
  · exact prime_3
  · exact prime_4007
  · exact prime_5851
  · exact prime_3
  · exact prime_11
  · exact prime_31
  · exact prime_3
  · exact prime_5503
  · exact prime_11
  · exact prime_3
  · exact prime_31
  · exact prime_127
  · exact prime_3
  · exact prime_3
  · exact prime_83
  · exact prime_4447
  · exact prime_3
  · exact prime_251
  · exact prime_239
  · exact prime_3
  · exact prime_1319
  · exact prime_967
  · exact prime_3
  · exact prime_2111
  · exact prime_463
  · exact prime_3
  · exact prime_2399
  · exact prime_139
  · exact prime_3
  · exact prime_307
  · exact prime_11471
  · exact prime_3
  · exact prime_4327
  · exact prime_1907
  · exact prime_3
  · exact prime_15887
  · exact prime_4943
  · exact prime_3
  · exact prime_4127
  · exact prime_4327
  · exact prime_3
  · exact prime_2851
  · exact prime_251
  · exact prime_3
  · exact prime_331
  · exact prime_1423
  · exact prime_3
  · exact prime_2539
  · exact prime_5651
  · exact prime_3
  · exact prime_1559
  · exact prime_911
  · exact prime_3
  · exact prime_7
  · exact prime_59
  · exact prime_683
  · exact prime_7
  · exact prime_2083
  · exact prime_1051
  · exact prime_7
  · exact prime_2063
  · exact prime_1723
  · exact prime_7
  · exact prime_919
  · exact prime_14683
  · exact prime_7
  · exact prime_683
  · exact prime_11
  · exact prime_19739
  · exact prime_3607
  · exact prime_9767
  · exact prime_7
  · exact prime_11
  · cases h_false

lemma blocking_prime_by_idx_12_prime (idx : ℕ) : Nat.Prime (blocking_prime_by_idx_12 idx) :=
  prime_of_mem_blocking_primes_12 (getD_mem blocking_primes_12 (idx - 1200) 3)

lemma mod4_of_mem_blocking_primes_12 {p : ℕ} (h : p ∈ 3 :: blocking_primes_12) : p % 4 = 3 := by
  unfold blocking_primes_12 at h
  simp only [List.mem_cons] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | h_false
  · exact mod4_3
  · exact mod4_3
  · exact mod4_11
  · exact mod4_31
  · exact mod4_3
  · exact mod4_8971
  · exact mod4_11
  · exact mod4_3
  · exact mod4_31
  · exact mod4_19
  · exact mod4_3
  · exact mod4_11
  · exact mod4_11
  · exact mod4_3
  · exact mod4_5783
  · exact mod4_719
  · exact mod4_3
  · exact mod4_11
  · exact mod4_19
  · exact mod4_3
  · exact mod4_487
  · exact mod4_11
  · exact mod4_3
  · exact mod4_31
  · exact mod4_5399
  · exact mod4_3
  · exact mod4_31
  · exact mod4_11
  · exact mod4_3
  · exact mod4_4007
  · exact mod4_5851
  · exact mod4_3
  · exact mod4_11
  · exact mod4_31
  · exact mod4_3
  · exact mod4_5503
  · exact mod4_11
  · exact mod4_3
  · exact mod4_31
  · exact mod4_127
  · exact mod4_3
  · exact mod4_3
  · exact mod4_83
  · exact mod4_4447
  · exact mod4_3
  · exact mod4_251
  · exact mod4_239
  · exact mod4_3
  · exact mod4_1319
  · exact mod4_967
  · exact mod4_3
  · exact mod4_2111
  · exact mod4_463
  · exact mod4_3
  · exact mod4_2399
  · exact mod4_139
  · exact mod4_3
  · exact mod4_307
  · exact mod4_11471
  · exact mod4_3
  · exact mod4_4327
  · exact mod4_1907
  · exact mod4_3
  · exact mod4_15887
  · exact mod4_4943
  · exact mod4_3
  · exact mod4_4127
  · exact mod4_4327
  · exact mod4_3
  · exact mod4_2851
  · exact mod4_251
  · exact mod4_3
  · exact mod4_331
  · exact mod4_1423
  · exact mod4_3
  · exact mod4_2539
  · exact mod4_5651
  · exact mod4_3
  · exact mod4_1559
  · exact mod4_911
  · exact mod4_3
  · exact mod4_7
  · exact mod4_59
  · exact mod4_683
  · exact mod4_7
  · exact mod4_2083
  · exact mod4_1051
  · exact mod4_7
  · exact mod4_2063
  · exact mod4_1723
  · exact mod4_7
  · exact mod4_919
  · exact mod4_14683
  · exact mod4_7
  · exact mod4_683
  · exact mod4_11
  · exact mod4_19739
  · exact mod4_3607
  · exact mod4_9767
  · exact mod4_7
  · exact mod4_11
  · cases h_false

lemma blocking_prime_by_idx_12_3mod4 (idx : ℕ) : blocking_prime_by_idx_12 idx % 4 = 3 :=
  mod4_of_mem_blocking_primes_12 (getD_mem blocking_primes_12 (idx - 1200) 3)

def blocking_primes_13 : List ℕ := [3191, 7, 4451, 3467, 7, 5647, 4219, 7, 2663, 11, 7, 4019, 83, 7, 11, 683, 2687, 9319, 3823, 7, 3, 5119, 10463, 3, 151, 43, 3, 2131, 71, 3, 607, 1019, 3, 11807, 331, 3, 83, 9403, 3, 43, 743, 3, 7247, 5227, 3, 5431, 43, 3, 1999, 331, 3, 71, 1667, 3, 151, 6491, 3, 12479, 2371, 3, 3, 10247, 15227, 3, 3671, 47, 3, 7547, 31, 3, 271, 71, 3, 31, 7607, 3, 107, 5783, 3, 379, 2503, 3, 12263, 31, 3, 199, 3167, 3, 31, 3851, 3, 167, 1619, 3, 11587, 9619, 3, 227, 31, 3]
def blocking_prime_by_idx_13 (idx : ℕ) : ℕ := blocking_primes_13.getD (idx - 1300) 3

lemma prime_of_mem_blocking_primes_13 {p : ℕ} (h : p ∈ 3 :: blocking_primes_13) : Nat.Prime p := by
  unfold blocking_primes_13 at h
  simp only [List.mem_cons] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | h_false
  · exact prime_3
  · exact prime_3191
  · exact prime_7
  · exact prime_4451
  · exact prime_3467
  · exact prime_7
  · exact prime_5647
  · exact prime_4219
  · exact prime_7
  · exact prime_2663
  · exact prime_11
  · exact prime_7
  · exact prime_4019
  · exact prime_83
  · exact prime_7
  · exact prime_11
  · exact prime_683
  · exact prime_2687
  · exact prime_9319
  · exact prime_3823
  · exact prime_7
  · exact prime_3
  · exact prime_5119
  · exact prime_10463
  · exact prime_3
  · exact prime_151
  · exact prime_43
  · exact prime_3
  · exact prime_2131
  · exact prime_71
  · exact prime_3
  · exact prime_607
  · exact prime_1019
  · exact prime_3
  · exact prime_11807
  · exact prime_331
  · exact prime_3
  · exact prime_83
  · exact prime_9403
  · exact prime_3
  · exact prime_43
  · exact prime_743
  · exact prime_3
  · exact prime_7247
  · exact prime_5227
  · exact prime_3
  · exact prime_5431
  · exact prime_43
  · exact prime_3
  · exact prime_1999
  · exact prime_331
  · exact prime_3
  · exact prime_71
  · exact prime_1667
  · exact prime_3
  · exact prime_151
  · exact prime_6491
  · exact prime_3
  · exact prime_12479
  · exact prime_2371
  · exact prime_3
  · exact prime_3
  · exact prime_10247
  · exact prime_15227
  · exact prime_3
  · exact prime_3671
  · exact prime_47
  · exact prime_3
  · exact prime_7547
  · exact prime_31
  · exact prime_3
  · exact prime_271
  · exact prime_71
  · exact prime_3
  · exact prime_31
  · exact prime_7607
  · exact prime_3
  · exact prime_107
  · exact prime_5783
  · exact prime_3
  · exact prime_379
  · exact prime_2503
  · exact prime_3
  · exact prime_12263
  · exact prime_31
  · exact prime_3
  · exact prime_199
  · exact prime_3167
  · exact prime_3
  · exact prime_31
  · exact prime_3851
  · exact prime_3
  · exact prime_167
  · exact prime_1619
  · exact prime_3
  · exact prime_11587
  · exact prime_9619
  · exact prime_3
  · exact prime_227
  · exact prime_31
  · exact prime_3
  · cases h_false

lemma blocking_prime_by_idx_13_prime (idx : ℕ) : Nat.Prime (blocking_prime_by_idx_13 idx) :=
  prime_of_mem_blocking_primes_13 (getD_mem blocking_primes_13 (idx - 1300) 3)

lemma mod4_of_mem_blocking_primes_13 {p : ℕ} (h : p ∈ 3 :: blocking_primes_13) : p % 4 = 3 := by
  unfold blocking_primes_13 at h
  simp only [List.mem_cons] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | h_false
  · exact mod4_3
  · exact mod4_3191
  · exact mod4_7
  · exact mod4_4451
  · exact mod4_3467
  · exact mod4_7
  · exact mod4_5647
  · exact mod4_4219
  · exact mod4_7
  · exact mod4_2663
  · exact mod4_11
  · exact mod4_7
  · exact mod4_4019
  · exact mod4_83
  · exact mod4_7
  · exact mod4_11
  · exact mod4_683
  · exact mod4_2687
  · exact mod4_9319
  · exact mod4_3823
  · exact mod4_7
  · exact mod4_3
  · exact mod4_5119
  · exact mod4_10463
  · exact mod4_3
  · exact mod4_151
  · exact mod4_43
  · exact mod4_3
  · exact mod4_2131
  · exact mod4_71
  · exact mod4_3
  · exact mod4_607
  · exact mod4_1019
  · exact mod4_3
  · exact mod4_11807
  · exact mod4_331
  · exact mod4_3
  · exact mod4_83
  · exact mod4_9403
  · exact mod4_3
  · exact mod4_43
  · exact mod4_743
  · exact mod4_3
  · exact mod4_7247
  · exact mod4_5227
  · exact mod4_3
  · exact mod4_5431
  · exact mod4_43
  · exact mod4_3
  · exact mod4_1999
  · exact mod4_331
  · exact mod4_3
  · exact mod4_71
  · exact mod4_1667
  · exact mod4_3
  · exact mod4_151
  · exact mod4_6491
  · exact mod4_3
  · exact mod4_12479
  · exact mod4_2371
  · exact mod4_3
  · exact mod4_3
  · exact mod4_10247
  · exact mod4_15227
  · exact mod4_3
  · exact mod4_3671
  · exact mod4_47
  · exact mod4_3
  · exact mod4_7547
  · exact mod4_31
  · exact mod4_3
  · exact mod4_271
  · exact mod4_71
  · exact mod4_3
  · exact mod4_31
  · exact mod4_7607
  · exact mod4_3
  · exact mod4_107
  · exact mod4_5783
  · exact mod4_3
  · exact mod4_379
  · exact mod4_2503
  · exact mod4_3
  · exact mod4_12263
  · exact mod4_31
  · exact mod4_3
  · exact mod4_199
  · exact mod4_3167
  · exact mod4_3
  · exact mod4_31
  · exact mod4_3851
  · exact mod4_3
  · exact mod4_167
  · exact mod4_1619
  · exact mod4_3
  · exact mod4_11587
  · exact mod4_9619
  · exact mod4_3
  · exact mod4_227
  · exact mod4_31
  · exact mod4_3
  · cases h_false

lemma blocking_prime_by_idx_13_3mod4 (idx : ℕ) : blocking_prime_by_idx_13 idx % 4 = 3 :=
  mod4_of_mem_blocking_primes_13 (getD_mem blocking_primes_13 (idx - 1300) 3)

def blocking_primes_14 : List ℕ := [7, 11, 31, 7, 3931, 11, 7, 9767, 4447, 7, 11, 11, 31, 3319, 2647, 7, 11, 31, 7, 1759, 31, 7, 31, 2503, 7, 11, 11, 7, 6091, 47, 7, 11, 31, 359, 23, 11, 7, 31, 15647, 7, 3, 3527, 43, 3, 127, 823, 3, 5419, 1103, 3, 1171, 127, 3, 911, 6827, 3, 43, 139, 3, 743, 683, 3, 16831, 43, 3, 127, 5839, 3, 5419, 523, 3, 59, 127, 3, 1223, 83, 3, 43, 607, 3, 3, 19, 3259, 3, 11, 3491, 3, 1523, 2027, 3, 19, 7507, 3, 1087, 11, 3, 4243, 127, 3, 11]
def blocking_prime_by_idx_14 (idx : ℕ) : ℕ := blocking_primes_14.getD (idx - 1400) 3

lemma prime_of_mem_blocking_primes_14 {p : ℕ} (h : p ∈ 3 :: blocking_primes_14) : Nat.Prime p := by
  unfold blocking_primes_14 at h
  simp only [List.mem_cons] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | h_false
  · exact prime_3
  · exact prime_7
  · exact prime_11
  · exact prime_31
  · exact prime_7
  · exact prime_3931
  · exact prime_11
  · exact prime_7
  · exact prime_9767
  · exact prime_4447
  · exact prime_7
  · exact prime_11
  · exact prime_11
  · exact prime_31
  · exact prime_3319
  · exact prime_2647
  · exact prime_7
  · exact prime_11
  · exact prime_31
  · exact prime_7
  · exact prime_1759
  · exact prime_31
  · exact prime_7
  · exact prime_31
  · exact prime_2503
  · exact prime_7
  · exact prime_11
  · exact prime_11
  · exact prime_7
  · exact prime_6091
  · exact prime_47
  · exact prime_7
  · exact prime_11
  · exact prime_31
  · exact prime_359
  · exact prime_23
  · exact prime_11
  · exact prime_7
  · exact prime_31
  · exact prime_15647
  · exact prime_7
  · exact prime_3
  · exact prime_3527
  · exact prime_43
  · exact prime_3
  · exact prime_127
  · exact prime_823
  · exact prime_3
  · exact prime_5419
  · exact prime_1103
  · exact prime_3
  · exact prime_1171
  · exact prime_127
  · exact prime_3
  · exact prime_911
  · exact prime_6827
  · exact prime_3
  · exact prime_43
  · exact prime_139
  · exact prime_3
  · exact prime_743
  · exact prime_683
  · exact prime_3
  · exact prime_16831
  · exact prime_43
  · exact prime_3
  · exact prime_127
  · exact prime_5839
  · exact prime_3
  · exact prime_5419
  · exact prime_523
  · exact prime_3
  · exact prime_59
  · exact prime_127
  · exact prime_3
  · exact prime_1223
  · exact prime_83
  · exact prime_3
  · exact prime_43
  · exact prime_607
  · exact prime_3
  · exact prime_3
  · exact prime_19
  · exact prime_3259
  · exact prime_3
  · exact prime_11
  · exact prime_3491
  · exact prime_3
  · exact prime_1523
  · exact prime_2027
  · exact prime_3
  · exact prime_19
  · exact prime_7507
  · exact prime_3
  · exact prime_1087
  · exact prime_11
  · exact prime_3
  · exact prime_4243
  · exact prime_127
  · exact prime_3
  · exact prime_11
  · cases h_false

lemma blocking_prime_by_idx_14_prime (idx : ℕ) : Nat.Prime (blocking_prime_by_idx_14 idx) :=
  prime_of_mem_blocking_primes_14 (getD_mem blocking_primes_14 (idx - 1400) 3)

lemma mod4_of_mem_blocking_primes_14 {p : ℕ} (h : p ∈ 3 :: blocking_primes_14) : p % 4 = 3 := by
  unfold blocking_primes_14 at h
  simp only [List.mem_cons] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | h_false
  · exact mod4_3
  · exact mod4_7
  · exact mod4_11
  · exact mod4_31
  · exact mod4_7
  · exact mod4_3931
  · exact mod4_11
  · exact mod4_7
  · exact mod4_9767
  · exact mod4_4447
  · exact mod4_7
  · exact mod4_11
  · exact mod4_11
  · exact mod4_31
  · exact mod4_3319
  · exact mod4_2647
  · exact mod4_7
  · exact mod4_11
  · exact mod4_31
  · exact mod4_7
  · exact mod4_1759
  · exact mod4_31
  · exact mod4_7
  · exact mod4_31
  · exact mod4_2503
  · exact mod4_7
  · exact mod4_11
  · exact mod4_11
  · exact mod4_7
  · exact mod4_6091
  · exact mod4_47
  · exact mod4_7
  · exact mod4_11
  · exact mod4_31
  · exact mod4_359
  · exact mod4_23
  · exact mod4_11
  · exact mod4_7
  · exact mod4_31
  · exact mod4_15647
  · exact mod4_7
  · exact mod4_3
  · exact mod4_3527
  · exact mod4_43
  · exact mod4_3
  · exact mod4_127
  · exact mod4_823
  · exact mod4_3
  · exact mod4_5419
  · exact mod4_1103
  · exact mod4_3
  · exact mod4_1171
  · exact mod4_127
  · exact mod4_3
  · exact mod4_911
  · exact mod4_6827
  · exact mod4_3
  · exact mod4_43
  · exact mod4_139
  · exact mod4_3
  · exact mod4_743
  · exact mod4_683
  · exact mod4_3
  · exact mod4_16831
  · exact mod4_43
  · exact mod4_3
  · exact mod4_127
  · exact mod4_5839
  · exact mod4_3
  · exact mod4_5419
  · exact mod4_523
  · exact mod4_3
  · exact mod4_59
  · exact mod4_127
  · exact mod4_3
  · exact mod4_1223
  · exact mod4_83
  · exact mod4_3
  · exact mod4_43
  · exact mod4_607
  · exact mod4_3
  · exact mod4_3
  · exact mod4_19
  · exact mod4_3259
  · exact mod4_3
  · exact mod4_11
  · exact mod4_3491
  · exact mod4_3
  · exact mod4_1523
  · exact mod4_2027
  · exact mod4_3
  · exact mod4_19
  · exact mod4_7507
  · exact mod4_3
  · exact mod4_1087
  · exact mod4_11
  · exact mod4_3
  · exact mod4_4243
  · exact mod4_127
  · exact mod4_3
  · exact mod4_11
  · cases h_false

lemma blocking_prime_by_idx_14_3mod4 (idx : ℕ) : blocking_prime_by_idx_14 idx % 4 = 3 :=
  mod4_of_mem_blocking_primes_14 (getD_mem blocking_primes_14 (idx - 1400) 3)

def blocking_primes_15 : List ℕ := [10243, 3, 71, 3079, 3, 2531, 6703, 3, 19, 11, 3, 83, 23, 3, 11, 2719, 3, 19, 127, 3, 7, 6967, 71, 7, 503, 4051, 7, 7507, 431, 9403, 7159, 23, 7, 2351, 227, 7, 8543, 23, 7, 8059, 8087, 7, 23, 47, 7, 727, 1831, 7, 23, 6719, 4051, 211, 7951, 7, 2311, 8627, 7, 71, 5843, 7, 3, 5939, 7699, 3, 47, 23, 3, 1091, 19, 3, 15443, 6199, 3, 31, 307, 3, 23, 19, 3, 67, 971, 3, 379, 31, 3, 271, 19, 3, 2879, 223, 3, 499, 67, 3, 1259, 19, 3, 13807, 31, 3]
def blocking_prime_by_idx_15 (idx : ℕ) : ℕ := blocking_primes_15.getD (idx - 1500) 3

lemma prime_of_mem_blocking_primes_15 {p : ℕ} (h : p ∈ 3 :: blocking_primes_15) : Nat.Prime p := by
  unfold blocking_primes_15 at h
  simp only [List.mem_cons] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | h_false
  · exact prime_3
  · exact prime_10243
  · exact prime_3
  · exact prime_71
  · exact prime_3079
  · exact prime_3
  · exact prime_2531
  · exact prime_6703
  · exact prime_3
  · exact prime_19
  · exact prime_11
  · exact prime_3
  · exact prime_83
  · exact prime_23
  · exact prime_3
  · exact prime_11
  · exact prime_2719
  · exact prime_3
  · exact prime_19
  · exact prime_127
  · exact prime_3
  · exact prime_7
  · exact prime_6967
  · exact prime_71
  · exact prime_7
  · exact prime_503
  · exact prime_4051
  · exact prime_7
  · exact prime_7507
  · exact prime_431
  · exact prime_9403
  · exact prime_7159
  · exact prime_23
  · exact prime_7
  · exact prime_2351
  · exact prime_227
  · exact prime_7
  · exact prime_8543
  · exact prime_23
  · exact prime_7
  · exact prime_8059
  · exact prime_8087
  · exact prime_7
  · exact prime_23
  · exact prime_47
  · exact prime_7
  · exact prime_727
  · exact prime_1831
  · exact prime_7
  · exact prime_23
  · exact prime_6719
  · exact prime_4051
  · exact prime_211
  · exact prime_7951
  · exact prime_7
  · exact prime_2311
  · exact prime_8627
  · exact prime_7
  · exact prime_71
  · exact prime_5843
  · exact prime_7
  · exact prime_3
  · exact prime_5939
  · exact prime_7699
  · exact prime_3
  · exact prime_47
  · exact prime_23
  · exact prime_3
  · exact prime_1091
  · exact prime_19
  · exact prime_3
  · exact prime_15443
  · exact prime_6199
  · exact prime_3
  · exact prime_31
  · exact prime_307
  · exact prime_3
  · exact prime_23
  · exact prime_19
  · exact prime_3
  · exact prime_67
  · exact prime_971
  · exact prime_3
  · exact prime_379
  · exact prime_31
  · exact prime_3
  · exact prime_271
  · exact prime_19
  · exact prime_3
  · exact prime_2879
  · exact prime_223
  · exact prime_3
  · exact prime_499
  · exact prime_67
  · exact prime_3
  · exact prime_1259
  · exact prime_19
  · exact prime_3
  · exact prime_13807
  · exact prime_31
  · exact prime_3
  · cases h_false

lemma blocking_prime_by_idx_15_prime (idx : ℕ) : Nat.Prime (blocking_prime_by_idx_15 idx) :=
  prime_of_mem_blocking_primes_15 (getD_mem blocking_primes_15 (idx - 1500) 3)

lemma mod4_of_mem_blocking_primes_15 {p : ℕ} (h : p ∈ 3 :: blocking_primes_15) : p % 4 = 3 := by
  unfold blocking_primes_15 at h
  simp only [List.mem_cons] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | h_false
  · exact mod4_3
  · exact mod4_10243
  · exact mod4_3
  · exact mod4_71
  · exact mod4_3079
  · exact mod4_3
  · exact mod4_2531
  · exact mod4_6703
  · exact mod4_3
  · exact mod4_19
  · exact mod4_11
  · exact mod4_3
  · exact mod4_83
  · exact mod4_23
  · exact mod4_3
  · exact mod4_11
  · exact mod4_2719
  · exact mod4_3
  · exact mod4_19
  · exact mod4_127
  · exact mod4_3
  · exact mod4_7
  · exact mod4_6967
  · exact mod4_71
  · exact mod4_7
  · exact mod4_503
  · exact mod4_4051
  · exact mod4_7
  · exact mod4_7507
  · exact mod4_431
  · exact mod4_9403
  · exact mod4_7159
  · exact mod4_23
  · exact mod4_7
  · exact mod4_2351
  · exact mod4_227
  · exact mod4_7
  · exact mod4_8543
  · exact mod4_23
  · exact mod4_7
  · exact mod4_8059
  · exact mod4_8087
  · exact mod4_7
  · exact mod4_23
  · exact mod4_47
  · exact mod4_7
  · exact mod4_727
  · exact mod4_1831
  · exact mod4_7
  · exact mod4_23
  · exact mod4_6719
  · exact mod4_4051
  · exact mod4_211
  · exact mod4_7951
  · exact mod4_7
  · exact mod4_2311
  · exact mod4_8627
  · exact mod4_7
  · exact mod4_71
  · exact mod4_5843
  · exact mod4_7
  · exact mod4_3
  · exact mod4_5939
  · exact mod4_7699
  · exact mod4_3
  · exact mod4_47
  · exact mod4_23
  · exact mod4_3
  · exact mod4_1091
  · exact mod4_19
  · exact mod4_3
  · exact mod4_15443
  · exact mod4_6199
  · exact mod4_3
  · exact mod4_31
  · exact mod4_307
  · exact mod4_3
  · exact mod4_23
  · exact mod4_19
  · exact mod4_3
  · exact mod4_67
  · exact mod4_971
  · exact mod4_3
  · exact mod4_379
  · exact mod4_31
  · exact mod4_3
  · exact mod4_271
  · exact mod4_19
  · exact mod4_3
  · exact mod4_2879
  · exact mod4_223
  · exact mod4_3
  · exact mod4_499
  · exact mod4_67
  · exact mod4_3
  · exact mod4_1259
  · exact mod4_19
  · exact mod4_3
  · exact mod4_13807
  · exact mod4_31
  · exact mod4_3
  · cases h_false

lemma blocking_prime_by_idx_15_3mod4 (idx : ℕ) : blocking_prime_by_idx_15 idx % 4 = 3 :=
  mod4_of_mem_blocking_primes_15 (getD_mem blocking_primes_15 (idx - 1500) 3)

def blocking_primes_16 : List ℕ := [3, 11, 31, 3, 1151, 11, 3, 31, 3923, 3, 11, 11, 3, 1459, 1459, 3, 11, 1499, 3, 43, 11, 3, 31, 1063, 3, 11, 11, 3, 11119, 503, 3, 11, 31, 3, 163, 11, 3, 31, 1327, 3, 7, 2579, 3511, 7, 83, 8563, 8191, 5107, 79, 7, 2011, 151, 7, 139, 1811, 7, 3467, 4507, 7, 8191, 5527, 7, 827, 67, 7, 10159, 151, 167, 263, 3919, 7, 4783, 8191, 7, 487, 1091, 7, 2099, 1987, 7, 3, 5059, 647, 3, 11, 10771, 3, 3083, 83, 3, 2731, 719, 3, 991, 11, 3, 383, 3187, 3, 11]
def blocking_prime_by_idx_16 (idx : ℕ) : ℕ := blocking_primes_16.getD (idx - 1600) 3

lemma prime_of_mem_blocking_primes_16 {p : ℕ} (h : p ∈ 3 :: blocking_primes_16) : Nat.Prime p := by
  unfold blocking_primes_16 at h
  simp only [List.mem_cons] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | h_false
  · exact prime_3
  · exact prime_3
  · exact prime_11
  · exact prime_31
  · exact prime_3
  · exact prime_1151
  · exact prime_11
  · exact prime_3
  · exact prime_31
  · exact prime_3923
  · exact prime_3
  · exact prime_11
  · exact prime_11
  · exact prime_3
  · exact prime_1459
  · exact prime_1459
  · exact prime_3
  · exact prime_11
  · exact prime_1499
  · exact prime_3
  · exact prime_43
  · exact prime_11
  · exact prime_3
  · exact prime_31
  · exact prime_1063
  · exact prime_3
  · exact prime_11
  · exact prime_11
  · exact prime_3
  · exact prime_11119
  · exact prime_503
  · exact prime_3
  · exact prime_11
  · exact prime_31
  · exact prime_3
  · exact prime_163
  · exact prime_11
  · exact prime_3
  · exact prime_31
  · exact prime_1327
  · exact prime_3
  · exact prime_7
  · exact prime_2579
  · exact prime_3511
  · exact prime_7
  · exact prime_83
  · exact prime_8563
  · exact prime_8191
  · exact prime_5107
  · exact prime_79
  · exact prime_7
  · exact prime_2011
  · exact prime_151
  · exact prime_7
  · exact prime_139
  · exact prime_1811
  · exact prime_7
  · exact prime_3467
  · exact prime_4507
  · exact prime_7
  · exact prime_8191
  · exact prime_5527
  · exact prime_7
  · exact prime_827
  · exact prime_67
  · exact prime_7
  · exact prime_10159
  · exact prime_151
  · exact prime_167
  · exact prime_263
  · exact prime_3919
  · exact prime_7
  · exact prime_4783
  · exact prime_8191
  · exact prime_7
  · exact prime_487
  · exact prime_1091
  · exact prime_7
  · exact prime_2099
  · exact prime_1987
  · exact prime_7
  · exact prime_3
  · exact prime_5059
  · exact prime_647
  · exact prime_3
  · exact prime_11
  · exact prime_10771
  · exact prime_3
  · exact prime_3083
  · exact prime_83
  · exact prime_3
  · exact prime_2731
  · exact prime_719
  · exact prime_3
  · exact prime_991
  · exact prime_11
  · exact prime_3
  · exact prime_383
  · exact prime_3187
  · exact prime_3
  · exact prime_11
  · cases h_false

lemma blocking_prime_by_idx_16_prime (idx : ℕ) : Nat.Prime (blocking_prime_by_idx_16 idx) :=
  prime_of_mem_blocking_primes_16 (getD_mem blocking_primes_16 (idx - 1600) 3)

lemma mod4_of_mem_blocking_primes_16 {p : ℕ} (h : p ∈ 3 :: blocking_primes_16) : p % 4 = 3 := by
  unfold blocking_primes_16 at h
  simp only [List.mem_cons] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | h_false
  · exact mod4_3
  · exact mod4_3
  · exact mod4_11
  · exact mod4_31
  · exact mod4_3
  · exact mod4_1151
  · exact mod4_11
  · exact mod4_3
  · exact mod4_31
  · exact mod4_3923
  · exact mod4_3
  · exact mod4_11
  · exact mod4_11
  · exact mod4_3
  · exact mod4_1459
  · exact mod4_1459
  · exact mod4_3
  · exact mod4_11
  · exact mod4_1499
  · exact mod4_3
  · exact mod4_43
  · exact mod4_11
  · exact mod4_3
  · exact mod4_31
  · exact mod4_1063
  · exact mod4_3
  · exact mod4_11
  · exact mod4_11
  · exact mod4_3
  · exact mod4_11119
  · exact mod4_503
  · exact mod4_3
  · exact mod4_11
  · exact mod4_31
  · exact mod4_3
  · exact mod4_163
  · exact mod4_11
  · exact mod4_3
  · exact mod4_31
  · exact mod4_1327
  · exact mod4_3
  · exact mod4_7
  · exact mod4_2579
  · exact mod4_3511
  · exact mod4_7
  · exact mod4_83
  · exact mod4_8563
  · exact mod4_8191
  · exact mod4_5107
  · exact mod4_79
  · exact mod4_7
  · exact mod4_2011
  · exact mod4_151
  · exact mod4_7
  · exact mod4_139
  · exact mod4_1811
  · exact mod4_7
  · exact mod4_3467
  · exact mod4_4507
  · exact mod4_7
  · exact mod4_8191
  · exact mod4_5527
  · exact mod4_7
  · exact mod4_827
  · exact mod4_67
  · exact mod4_7
  · exact mod4_10159
  · exact mod4_151
  · exact mod4_167
  · exact mod4_263
  · exact mod4_3919
  · exact mod4_7
  · exact mod4_4783
  · exact mod4_8191
  · exact mod4_7
  · exact mod4_487
  · exact mod4_1091
  · exact mod4_7
  · exact mod4_2099
  · exact mod4_1987
  · exact mod4_7
  · exact mod4_3
  · exact mod4_5059
  · exact mod4_647
  · exact mod4_3
  · exact mod4_11
  · exact mod4_10771
  · exact mod4_3
  · exact mod4_3083
  · exact mod4_83
  · exact mod4_3
  · exact mod4_2731
  · exact mod4_719
  · exact mod4_3
  · exact mod4_991
  · exact mod4_11
  · exact mod4_3
  · exact mod4_383
  · exact mod4_3187
  · exact mod4_3
  · exact mod4_11
  · cases h_false

lemma blocking_prime_by_idx_16_3mod4 (idx : ℕ) : blocking_prime_by_idx_16 idx % 4 = 3 :=
  mod4_of_mem_blocking_primes_16 (getD_mem blocking_primes_16 (idx - 1600) 3)

def blocking_primes_17 : List ℕ := [1447, 3, 7151, 2731, 3, 499, 4583, 3, 619, 11, 3, 2963, 7243, 3, 11, 71, 3, 3331, 5399, 3, 3, 739, 43, 3, 127, 6007, 3, 17539, 3719, 3, 191, 127, 3, 683, 1619, 3, 43, 1399, 3, 15859, 5507, 3, 3491, 43, 3, 127, 607, 3, 2699, 71, 3, 6299, 127, 3, 2671, 683, 3, 43, 263, 3, 7, 79, 12203, 31, 10531, 1811, 7, 167, 31, 7, 127, 1907, 7, 31, 67, 7, 7879, 1511, 7, 167, 1319, 7, 67, 31, 127, 7103, 1723, 7, 31, 2131, 7, 127, 103, 7, 79, 2971, 7, 9587, 31, 7]
def blocking_prime_by_idx_17 (idx : ℕ) : ℕ := blocking_primes_17.getD (idx - 1700) 3

lemma prime_of_mem_blocking_primes_17 {p : ℕ} (h : p ∈ 3 :: blocking_primes_17) : Nat.Prime p := by
  unfold blocking_primes_17 at h
  simp only [List.mem_cons] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | h_false
  · exact prime_3
  · exact prime_1447
  · exact prime_3
  · exact prime_7151
  · exact prime_2731
  · exact prime_3
  · exact prime_499
  · exact prime_4583
  · exact prime_3
  · exact prime_619
  · exact prime_11
  · exact prime_3
  · exact prime_2963
  · exact prime_7243
  · exact prime_3
  · exact prime_11
  · exact prime_71
  · exact prime_3
  · exact prime_3331
  · exact prime_5399
  · exact prime_3
  · exact prime_3
  · exact prime_739
  · exact prime_43
  · exact prime_3
  · exact prime_127
  · exact prime_6007
  · exact prime_3
  · exact prime_17539
  · exact prime_3719
  · exact prime_3
  · exact prime_191
  · exact prime_127
  · exact prime_3
  · exact prime_683
  · exact prime_1619
  · exact prime_3
  · exact prime_43
  · exact prime_1399
  · exact prime_3
  · exact prime_15859
  · exact prime_5507
  · exact prime_3
  · exact prime_3491
  · exact prime_43
  · exact prime_3
  · exact prime_127
  · exact prime_607
  · exact prime_3
  · exact prime_2699
  · exact prime_71
  · exact prime_3
  · exact prime_6299
  · exact prime_127
  · exact prime_3
  · exact prime_2671
  · exact prime_683
  · exact prime_3
  · exact prime_43
  · exact prime_263
  · exact prime_3
  · exact prime_7
  · exact prime_79
  · exact prime_12203
  · exact prime_31
  · exact prime_10531
  · exact prime_1811
  · exact prime_7
  · exact prime_167
  · exact prime_31
  · exact prime_7
  · exact prime_127
  · exact prime_1907
  · exact prime_7
  · exact prime_31
  · exact prime_67
  · exact prime_7
  · exact prime_7879
  · exact prime_1511
  · exact prime_7
  · exact prime_167
  · exact prime_1319
  · exact prime_7
  · exact prime_67
  · exact prime_31
  · exact prime_127
  · exact prime_7103
  · exact prime_1723
  · exact prime_7
  · exact prime_31
  · exact prime_2131
  · exact prime_7
  · exact prime_127
  · exact prime_103
  · exact prime_7
  · exact prime_79
  · exact prime_2971
  · exact prime_7
  · exact prime_9587
  · exact prime_31
  · exact prime_7
  · cases h_false

lemma blocking_prime_by_idx_17_prime (idx : ℕ) : Nat.Prime (blocking_prime_by_idx_17 idx) :=
  prime_of_mem_blocking_primes_17 (getD_mem blocking_primes_17 (idx - 1700) 3)

lemma mod4_of_mem_blocking_primes_17 {p : ℕ} (h : p ∈ 3 :: blocking_primes_17) : p % 4 = 3 := by
  unfold blocking_primes_17 at h
  simp only [List.mem_cons] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | h_false
  · exact mod4_3
  · exact mod4_1447
  · exact mod4_3
  · exact mod4_7151
  · exact mod4_2731
  · exact mod4_3
  · exact mod4_499
  · exact mod4_4583
  · exact mod4_3
  · exact mod4_619
  · exact mod4_11
  · exact mod4_3
  · exact mod4_2963
  · exact mod4_7243
  · exact mod4_3
  · exact mod4_11
  · exact mod4_71
  · exact mod4_3
  · exact mod4_3331
  · exact mod4_5399
  · exact mod4_3
  · exact mod4_3
  · exact mod4_739
  · exact mod4_43
  · exact mod4_3
  · exact mod4_127
  · exact mod4_6007
  · exact mod4_3
  · exact mod4_17539
  · exact mod4_3719
  · exact mod4_3
  · exact mod4_191
  · exact mod4_127
  · exact mod4_3
  · exact mod4_683
  · exact mod4_1619
  · exact mod4_3
  · exact mod4_43
  · exact mod4_1399
  · exact mod4_3
  · exact mod4_15859
  · exact mod4_5507
  · exact mod4_3
  · exact mod4_3491
  · exact mod4_43
  · exact mod4_3
  · exact mod4_127
  · exact mod4_607
  · exact mod4_3
  · exact mod4_2699
  · exact mod4_71
  · exact mod4_3
  · exact mod4_6299
  · exact mod4_127
  · exact mod4_3
  · exact mod4_2671
  · exact mod4_683
  · exact mod4_3
  · exact mod4_43
  · exact mod4_263
  · exact mod4_3
  · exact mod4_7
  · exact mod4_79
  · exact mod4_12203
  · exact mod4_31
  · exact mod4_10531
  · exact mod4_1811
  · exact mod4_7
  · exact mod4_167
  · exact mod4_31
  · exact mod4_7
  · exact mod4_127
  · exact mod4_1907
  · exact mod4_7
  · exact mod4_31
  · exact mod4_67
  · exact mod4_7
  · exact mod4_7879
  · exact mod4_1511
  · exact mod4_7
  · exact mod4_167
  · exact mod4_1319
  · exact mod4_7
  · exact mod4_67
  · exact mod4_31
  · exact mod4_127
  · exact mod4_7103
  · exact mod4_1723
  · exact mod4_7
  · exact mod4_31
  · exact mod4_2131
  · exact mod4_7
  · exact mod4_127
  · exact mod4_103
  · exact mod4_7
  · exact mod4_79
  · exact mod4_2971
  · exact mod4_7
  · exact mod4_9587
  · exact mod4_31
  · exact mod4_7
  · cases h_false

lemma blocking_prime_by_idx_17_3mod4 (idx : ℕ) : blocking_prime_by_idx_17 idx % 4 = 3 :=
  mod4_of_mem_blocking_primes_17 (getD_mem blocking_primes_17 (idx - 1700) 3)

def blocking_primes_18 : List ℕ := [3, 11, 31, 3, 103, 11, 3, 31, 547, 3, 31, 331, 3, 479, 4567, 3, 11, 31, 3, 2459, 11, 3, 31, 11119, 3, 11, 11, 3, 13807, 1291, 3, 11, 31, 3, 659, 11, 3, 31, 6763, 3, 3, 19, 3347, 3, 15227, 15331, 3, 659, 1787, 3, 19, 5879, 3, 71, 211, 3, 331, 419, 3, 19, 9719, 3, 4231, 23, 3, 463, 11867, 3, 19, 5839, 3, 331, 1367, 3, 23, 12899, 3, 19, 79, 3, 2011, 2887, 10859, 7, 11, 43, 7, 3319, 719, 7, 79, 5051, 7, 347, 11, 7, 5431, 47, 7, 11]
def blocking_prime_by_idx_18 (idx : ℕ) : ℕ := blocking_primes_18.getD (idx - 1800) 3

lemma prime_of_mem_blocking_primes_18 {p : ℕ} (h : p ∈ 3 :: blocking_primes_18) : Nat.Prime p := by
  unfold blocking_primes_18 at h
  simp only [List.mem_cons] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | h_false
  · exact prime_3
  · exact prime_3
  · exact prime_11
  · exact prime_31
  · exact prime_3
  · exact prime_103
  · exact prime_11
  · exact prime_3
  · exact prime_31
  · exact prime_547
  · exact prime_3
  · exact prime_31
  · exact prime_331
  · exact prime_3
  · exact prime_479
  · exact prime_4567
  · exact prime_3
  · exact prime_11
  · exact prime_31
  · exact prime_3
  · exact prime_2459
  · exact prime_11
  · exact prime_3
  · exact prime_31
  · exact prime_11119
  · exact prime_3
  · exact prime_11
  · exact prime_11
  · exact prime_3
  · exact prime_13807
  · exact prime_1291
  · exact prime_3
  · exact prime_11
  · exact prime_31
  · exact prime_3
  · exact prime_659
  · exact prime_11
  · exact prime_3
  · exact prime_31
  · exact prime_6763
  · exact prime_3
  · exact prime_3
  · exact prime_19
  · exact prime_3347
  · exact prime_3
  · exact prime_15227
  · exact prime_15331
  · exact prime_3
  · exact prime_659
  · exact prime_1787
  · exact prime_3
  · exact prime_19
  · exact prime_5879
  · exact prime_3
  · exact prime_71
  · exact prime_211
  · exact prime_3
  · exact prime_331
  · exact prime_419
  · exact prime_3
  · exact prime_19
  · exact prime_9719
  · exact prime_3
  · exact prime_4231
  · exact prime_23
  · exact prime_3
  · exact prime_463
  · exact prime_11867
  · exact prime_3
  · exact prime_19
  · exact prime_5839
  · exact prime_3
  · exact prime_331
  · exact prime_1367
  · exact prime_3
  · exact prime_23
  · exact prime_12899
  · exact prime_3
  · exact prime_19
  · exact prime_79
  · exact prime_3
  · exact prime_2011
  · exact prime_2887
  · exact prime_10859
  · exact prime_7
  · exact prime_11
  · exact prime_43
  · exact prime_7
  · exact prime_3319
  · exact prime_719
  · exact prime_7
  · exact prime_79
  · exact prime_5051
  · exact prime_7
  · exact prime_347
  · exact prime_11
  · exact prime_7
  · exact prime_5431
  · exact prime_47
  · exact prime_7
  · exact prime_11
  · cases h_false

lemma blocking_prime_by_idx_18_prime (idx : ℕ) : Nat.Prime (blocking_prime_by_idx_18 idx) :=
  prime_of_mem_blocking_primes_18 (getD_mem blocking_primes_18 (idx - 1800) 3)

lemma mod4_of_mem_blocking_primes_18 {p : ℕ} (h : p ∈ 3 :: blocking_primes_18) : p % 4 = 3 := by
  unfold blocking_primes_18 at h
  simp only [List.mem_cons] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | h_false
  · exact mod4_3
  · exact mod4_3
  · exact mod4_11
  · exact mod4_31
  · exact mod4_3
  · exact mod4_103
  · exact mod4_11
  · exact mod4_3
  · exact mod4_31
  · exact mod4_547
  · exact mod4_3
  · exact mod4_31
  · exact mod4_331
  · exact mod4_3
  · exact mod4_479
  · exact mod4_4567
  · exact mod4_3
  · exact mod4_11
  · exact mod4_31
  · exact mod4_3
  · exact mod4_2459
  · exact mod4_11
  · exact mod4_3
  · exact mod4_31
  · exact mod4_11119
  · exact mod4_3
  · exact mod4_11
  · exact mod4_11
  · exact mod4_3
  · exact mod4_13807
  · exact mod4_1291
  · exact mod4_3
  · exact mod4_11
  · exact mod4_31
  · exact mod4_3
  · exact mod4_659
  · exact mod4_11
  · exact mod4_3
  · exact mod4_31
  · exact mod4_6763
  · exact mod4_3
  · exact mod4_3
  · exact mod4_19
  · exact mod4_3347
  · exact mod4_3
  · exact mod4_15227
  · exact mod4_15331
  · exact mod4_3
  · exact mod4_659
  · exact mod4_1787
  · exact mod4_3
  · exact mod4_19
  · exact mod4_5879
  · exact mod4_3
  · exact mod4_71
  · exact mod4_211
  · exact mod4_3
  · exact mod4_331
  · exact mod4_419
  · exact mod4_3
  · exact mod4_19
  · exact mod4_9719
  · exact mod4_3
  · exact mod4_4231
  · exact mod4_23
  · exact mod4_3
  · exact mod4_463
  · exact mod4_11867
  · exact mod4_3
  · exact mod4_19
  · exact mod4_5839
  · exact mod4_3
  · exact mod4_331
  · exact mod4_1367
  · exact mod4_3
  · exact mod4_23
  · exact mod4_12899
  · exact mod4_3
  · exact mod4_19
  · exact mod4_79
  · exact mod4_3
  · exact mod4_2011
  · exact mod4_2887
  · exact mod4_10859
  · exact mod4_7
  · exact mod4_11
  · exact mod4_43
  · exact mod4_7
  · exact mod4_3319
  · exact mod4_719
  · exact mod4_7
  · exact mod4_79
  · exact mod4_5051
  · exact mod4_7
  · exact mod4_347
  · exact mod4_11
  · exact mod4_7
  · exact mod4_5431
  · exact mod4_47
  · exact mod4_7
  · exact mod4_11
  · cases h_false

lemma blocking_prime_by_idx_18_3mod4 (idx : ℕ) : blocking_prime_by_idx_18 idx % 4 = 3 :=
  mod4_of_mem_blocking_primes_18 (getD_mem blocking_primes_18 (idx - 1800) 3)

def blocking_primes_19 : List ℕ := [683, 479, 239, 1583, 7, 691, 43, 7, 6551, 967, 7, 683, 7759, 7, 11, 10631, 7, 13591, 6359, 7, 3, 1523, 47, 3, 151, 1259, 3, 79, 19, 3, 23, 1399, 3, 2903, 331, 3, 6299, 19, 3, 151, 4051, 3, 12343, 71, 3, 47, 19, 3, 6379, 331, 3, 5563, 23, 3, 151, 19, 3, 10463, 4019, 3, 3, 1951, 4079, 3, 9067, 11299, 3, 1627, 31, 3, 5059, 23, 3, 31, 6679, 3, 2731, 23, 3, 8447, 647, 3, 23, 31, 3, 383, 10067, 3, 31, 2731, 3, 13691, 307, 3, 107, 107, 3, 83, 31, 3]
def blocking_prime_by_idx_19 (idx : ℕ) : ℕ := blocking_primes_19.getD (idx - 1900) 3

lemma prime_of_mem_blocking_primes_19 {p : ℕ} (h : p ∈ 3 :: blocking_primes_19) : Nat.Prime p := by
  unfold blocking_primes_19 at h
  simp only [List.mem_cons] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | h_false
  · exact prime_3
  · exact prime_683
  · exact prime_479
  · exact prime_239
  · exact prime_1583
  · exact prime_7
  · exact prime_691
  · exact prime_43
  · exact prime_7
  · exact prime_6551
  · exact prime_967
  · exact prime_7
  · exact prime_683
  · exact prime_7759
  · exact prime_7
  · exact prime_11
  · exact prime_10631
  · exact prime_7
  · exact prime_13591
  · exact prime_6359
  · exact prime_7
  · exact prime_3
  · exact prime_1523
  · exact prime_47
  · exact prime_3
  · exact prime_151
  · exact prime_1259
  · exact prime_3
  · exact prime_79
  · exact prime_19
  · exact prime_3
  · exact prime_23
  · exact prime_1399
  · exact prime_3
  · exact prime_2903
  · exact prime_331
  · exact prime_3
  · exact prime_6299
  · exact prime_19
  · exact prime_3
  · exact prime_151
  · exact prime_4051
  · exact prime_3
  · exact prime_12343
  · exact prime_71
  · exact prime_3
  · exact prime_47
  · exact prime_19
  · exact prime_3
  · exact prime_6379
  · exact prime_331
  · exact prime_3
  · exact prime_5563
  · exact prime_23
  · exact prime_3
  · exact prime_151
  · exact prime_19
  · exact prime_3
  · exact prime_10463
  · exact prime_4019
  · exact prime_3
  · exact prime_3
  · exact prime_1951
  · exact prime_4079
  · exact prime_3
  · exact prime_9067
  · exact prime_11299
  · exact prime_3
  · exact prime_1627
  · exact prime_31
  · exact prime_3
  · exact prime_5059
  · exact prime_23
  · exact prime_3
  · exact prime_31
  · exact prime_6679
  · exact prime_3
  · exact prime_2731
  · exact prime_23
  · exact prime_3
  · exact prime_8447
  · exact prime_647
  · exact prime_3
  · exact prime_23
  · exact prime_31
  · exact prime_3
  · exact prime_383
  · exact prime_10067
  · exact prime_3
  · exact prime_31
  · exact prime_2731
  · exact prime_3
  · exact prime_13691
  · exact prime_307
  · exact prime_3
  · exact prime_107
  · exact prime_107
  · exact prime_3
  · exact prime_83
  · exact prime_31
  · exact prime_3
  · cases h_false

lemma blocking_prime_by_idx_19_prime (idx : ℕ) : Nat.Prime (blocking_prime_by_idx_19 idx) :=
  prime_of_mem_blocking_primes_19 (getD_mem blocking_primes_19 (idx - 1900) 3)

lemma mod4_of_mem_blocking_primes_19 {p : ℕ} (h : p ∈ 3 :: blocking_primes_19) : p % 4 = 3 := by
  unfold blocking_primes_19 at h
  simp only [List.mem_cons] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | h_false
  · exact mod4_3
  · exact mod4_683
  · exact mod4_479
  · exact mod4_239
  · exact mod4_1583
  · exact mod4_7
  · exact mod4_691
  · exact mod4_43
  · exact mod4_7
  · exact mod4_6551
  · exact mod4_967
  · exact mod4_7
  · exact mod4_683
  · exact mod4_7759
  · exact mod4_7
  · exact mod4_11
  · exact mod4_10631
  · exact mod4_7
  · exact mod4_13591
  · exact mod4_6359
  · exact mod4_7
  · exact mod4_3
  · exact mod4_1523
  · exact mod4_47
  · exact mod4_3
  · exact mod4_151
  · exact mod4_1259
  · exact mod4_3
  · exact mod4_79
  · exact mod4_19
  · exact mod4_3
  · exact mod4_23
  · exact mod4_1399
  · exact mod4_3
  · exact mod4_2903
  · exact mod4_331
  · exact mod4_3
  · exact mod4_6299
  · exact mod4_19
  · exact mod4_3
  · exact mod4_151
  · exact mod4_4051
  · exact mod4_3
  · exact mod4_12343
  · exact mod4_71
  · exact mod4_3
  · exact mod4_47
  · exact mod4_19
  · exact mod4_3
  · exact mod4_6379
  · exact mod4_331
  · exact mod4_3
  · exact mod4_5563
  · exact mod4_23
  · exact mod4_3
  · exact mod4_151
  · exact mod4_19
  · exact mod4_3
  · exact mod4_10463
  · exact mod4_4019
  · exact mod4_3
  · exact mod4_3
  · exact mod4_1951
  · exact mod4_4079
  · exact mod4_3
  · exact mod4_9067
  · exact mod4_11299
  · exact mod4_3
  · exact mod4_1627
  · exact mod4_31
  · exact mod4_3
  · exact mod4_5059
  · exact mod4_23
  · exact mod4_3
  · exact mod4_31
  · exact mod4_6679
  · exact mod4_3
  · exact mod4_2731
  · exact mod4_23
  · exact mod4_3
  · exact mod4_8447
  · exact mod4_647
  · exact mod4_3
  · exact mod4_23
  · exact mod4_31
  · exact mod4_3
  · exact mod4_383
  · exact mod4_10067
  · exact mod4_3
  · exact mod4_31
  · exact mod4_2731
  · exact mod4_3
  · exact mod4_13691
  · exact mod4_307
  · exact mod4_3
  · exact mod4_107
  · exact mod4_107
  · exact mod4_3
  · exact mod4_83
  · exact mod4_31
  · exact mod4_3
  · cases h_false

lemma blocking_prime_by_idx_19_3mod4 (idx : ℕ) : blocking_prime_by_idx_19 idx % 4 = 3 :=
  mod4_of_mem_blocking_primes_19 (getD_mem blocking_primes_19 (idx - 1900) 3)

def blocking_primes_20 : List ℕ := [7, 11, 31, 7, 127, 31, 7, 31, 5987, 7, 11, 11, 7, 4079, 5419, 7, 11, 31, 127, 1303, 11, 7, 31, 43, 7, 11, 643, 7, 2819, 1783, 7, 11, 31, 7, 5531, 11, 7, 43, 23, 127, 3, 3727, 587, 3, 131, 139, 3, 647, 1607, 3, 107, 1871, 3, 2879, 7499, 3, 1907, 59, 3, 1559, 643, 3, 1511, 10247, 3, 9323, 967, 3, 1571, 6211, 3, 127, 12671, 3, 1319, 1559, 3, 1151, 127, 3, 3, 3323, 4831, 3, 11, 211, 3, 2243, 2411, 3, 1531, 587, 3, 6607, 11, 3, 859, 751, 3, 331]
def blocking_prime_by_idx_20 (idx : ℕ) : ℕ := blocking_primes_20.getD (idx - 2000) 3

lemma prime_of_mem_blocking_primes_20 {p : ℕ} (h : p ∈ 3 :: blocking_primes_20) : Nat.Prime p := by
  unfold blocking_primes_20 at h
  simp only [List.mem_cons] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | h_false
  · exact prime_3
  · exact prime_7
  · exact prime_11
  · exact prime_31
  · exact prime_7
  · exact prime_127
  · exact prime_31
  · exact prime_7
  · exact prime_31
  · exact prime_5987
  · exact prime_7
  · exact prime_11
  · exact prime_11
  · exact prime_7
  · exact prime_4079
  · exact prime_5419
  · exact prime_7
  · exact prime_11
  · exact prime_31
  · exact prime_127
  · exact prime_1303
  · exact prime_11
  · exact prime_7
  · exact prime_31
  · exact prime_43
  · exact prime_7
  · exact prime_11
  · exact prime_643
  · exact prime_7
  · exact prime_2819
  · exact prime_1783
  · exact prime_7
  · exact prime_11
  · exact prime_31
  · exact prime_7
  · exact prime_5531
  · exact prime_11
  · exact prime_7
  · exact prime_43
  · exact prime_23
  · exact prime_127
  · exact prime_3
  · exact prime_3727
  · exact prime_587
  · exact prime_3
  · exact prime_131
  · exact prime_139
  · exact prime_3
  · exact prime_647
  · exact prime_1607
  · exact prime_3
  · exact prime_107
  · exact prime_1871
  · exact prime_3
  · exact prime_2879
  · exact prime_7499
  · exact prime_3
  · exact prime_1907
  · exact prime_59
  · exact prime_3
  · exact prime_1559
  · exact prime_643
  · exact prime_3
  · exact prime_1511
  · exact prime_10247
  · exact prime_3
  · exact prime_9323
  · exact prime_967
  · exact prime_3
  · exact prime_1571
  · exact prime_6211
  · exact prime_3
  · exact prime_127
  · exact prime_12671
  · exact prime_3
  · exact prime_1319
  · exact prime_1559
  · exact prime_3
  · exact prime_1151
  · exact prime_127
  · exact prime_3
  · exact prime_3
  · exact prime_3323
  · exact prime_4831
  · exact prime_3
  · exact prime_11
  · exact prime_211
  · exact prime_3
  · exact prime_2243
  · exact prime_2411
  · exact prime_3
  · exact prime_1531
  · exact prime_587
  · exact prime_3
  · exact prime_6607
  · exact prime_11
  · exact prime_3
  · exact prime_859
  · exact prime_751
  · exact prime_3
  · exact prime_331
  · cases h_false

lemma blocking_prime_by_idx_20_prime (idx : ℕ) : Nat.Prime (blocking_prime_by_idx_20 idx) :=
  prime_of_mem_blocking_primes_20 (getD_mem blocking_primes_20 (idx - 2000) 3)

lemma mod4_of_mem_blocking_primes_20 {p : ℕ} (h : p ∈ 3 :: blocking_primes_20) : p % 4 = 3 := by
  unfold blocking_primes_20 at h
  simp only [List.mem_cons] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | h_false
  · exact mod4_3
  · exact mod4_7
  · exact mod4_11
  · exact mod4_31
  · exact mod4_7
  · exact mod4_127
  · exact mod4_31
  · exact mod4_7
  · exact mod4_31
  · exact mod4_5987
  · exact mod4_7
  · exact mod4_11
  · exact mod4_11
  · exact mod4_7
  · exact mod4_4079
  · exact mod4_5419
  · exact mod4_7
  · exact mod4_11
  · exact mod4_31
  · exact mod4_127
  · exact mod4_1303
  · exact mod4_11
  · exact mod4_7
  · exact mod4_31
  · exact mod4_43
  · exact mod4_7
  · exact mod4_11
  · exact mod4_643
  · exact mod4_7
  · exact mod4_2819
  · exact mod4_1783
  · exact mod4_7
  · exact mod4_11
  · exact mod4_31
  · exact mod4_7
  · exact mod4_5531
  · exact mod4_11
  · exact mod4_7
  · exact mod4_43
  · exact mod4_23
  · exact mod4_127
  · exact mod4_3
  · exact mod4_3727
  · exact mod4_587
  · exact mod4_3
  · exact mod4_131
  · exact mod4_139
  · exact mod4_3
  · exact mod4_647
  · exact mod4_1607
  · exact mod4_3
  · exact mod4_107
  · exact mod4_1871
  · exact mod4_3
  · exact mod4_2879
  · exact mod4_7499
  · exact mod4_3
  · exact mod4_1907
  · exact mod4_59
  · exact mod4_3
  · exact mod4_1559
  · exact mod4_643
  · exact mod4_3
  · exact mod4_1511
  · exact mod4_10247
  · exact mod4_3
  · exact mod4_9323
  · exact mod4_967
  · exact mod4_3
  · exact mod4_1571
  · exact mod4_6211
  · exact mod4_3
  · exact mod4_127
  · exact mod4_12671
  · exact mod4_3
  · exact mod4_1319
  · exact mod4_1559
  · exact mod4_3
  · exact mod4_1151
  · exact mod4_127
  · exact mod4_3
  · exact mod4_3
  · exact mod4_3323
  · exact mod4_4831
  · exact mod4_3
  · exact mod4_11
  · exact mod4_211
  · exact mod4_3
  · exact mod4_2243
  · exact mod4_2411
  · exact mod4_3
  · exact mod4_1531
  · exact mod4_587
  · exact mod4_3
  · exact mod4_6607
  · exact mod4_11
  · exact mod4_3
  · exact mod4_859
  · exact mod4_751
  · exact mod4_3
  · exact mod4_331
  · cases h_false

lemma blocking_prime_by_idx_20_3mod4 (idx : ℕ) : blocking_prime_by_idx_20 idx % 4 = 3 :=
  mod4_of_mem_blocking_primes_20 (getD_mem blocking_primes_20 (idx - 2000) 3)

def blocking_primes_21 : List ℕ := [59, 3, 4723, 1999, 3, 5279, 12919, 3, 6911, 11, 3, 2179, 59, 3, 11, 2027, 3, 863, 823, 3, 7, 10079, 199, 7, 4363, 1031, 7, 8191, 11423, 7, 307, 1087, 7, 8719, 15859, 463, 5927, 1487, 7, 9787, 8191, 7, 5779, 4691, 7, 9431, 10531, 7, 4987, 5399, 7, 1831, 1811, 7, 9323, 2447, 8747, 1759, 479, 7, 3, 2803, 683, 3, 3527, 43, 3, 4871, 31, 3, 67, 9467, 3, 31, 2803, 3, 4723, 1367, 3, 43, 2903, 3, 2267, 31, 3, 2111, 43, 3, 31, 59, 3, 2767, 8191, 3, 59, 431, 3, 6263, 31, 3]
def blocking_prime_by_idx_21 (idx : ℕ) : ℕ := blocking_primes_21.getD (idx - 2100) 3

lemma prime_of_mem_blocking_primes_21 {p : ℕ} (h : p ∈ 3 :: blocking_primes_21) : Nat.Prime p := by
  unfold blocking_primes_21 at h
  simp only [List.mem_cons] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | h_false
  · exact prime_3
  · exact prime_59
  · exact prime_3
  · exact prime_4723
  · exact prime_1999
  · exact prime_3
  · exact prime_5279
  · exact prime_12919
  · exact prime_3
  · exact prime_6911
  · exact prime_11
  · exact prime_3
  · exact prime_2179
  · exact prime_59
  · exact prime_3
  · exact prime_11
  · exact prime_2027
  · exact prime_3
  · exact prime_863
  · exact prime_823
  · exact prime_3
  · exact prime_7
  · exact prime_10079
  · exact prime_199
  · exact prime_7
  · exact prime_4363
  · exact prime_1031
  · exact prime_7
  · exact prime_8191
  · exact prime_11423
  · exact prime_7
  · exact prime_307
  · exact prime_1087
  · exact prime_7
  · exact prime_8719
  · exact prime_15859
  · exact prime_463
  · exact prime_5927
  · exact prime_1487
  · exact prime_7
  · exact prime_9787
  · exact prime_8191
  · exact prime_7
  · exact prime_5779
  · exact prime_4691
  · exact prime_7
  · exact prime_9431
  · exact prime_10531
  · exact prime_7
  · exact prime_4987
  · exact prime_5399
  · exact prime_7
  · exact prime_1831
  · exact prime_1811
  · exact prime_7
  · exact prime_9323
  · exact prime_2447
  · exact prime_8747
  · exact prime_1759
  · exact prime_479
  · exact prime_7
  · exact prime_3
  · exact prime_2803
  · exact prime_683
  · exact prime_3
  · exact prime_3527
  · exact prime_43
  · exact prime_3
  · exact prime_4871
  · exact prime_31
  · exact prime_3
  · exact prime_67
  · exact prime_9467
  · exact prime_3
  · exact prime_31
  · exact prime_2803
  · exact prime_3
  · exact prime_4723
  · exact prime_1367
  · exact prime_3
  · exact prime_43
  · exact prime_2903
  · exact prime_3
  · exact prime_2267
  · exact prime_31
  · exact prime_3
  · exact prime_2111
  · exact prime_43
  · exact prime_3
  · exact prime_31
  · exact prime_59
  · exact prime_3
  · exact prime_2767
  · exact prime_8191
  · exact prime_3
  · exact prime_59
  · exact prime_431
  · exact prime_3
  · exact prime_6263
  · exact prime_31
  · exact prime_3
  · cases h_false

lemma blocking_prime_by_idx_21_prime (idx : ℕ) : Nat.Prime (blocking_prime_by_idx_21 idx) :=
  prime_of_mem_blocking_primes_21 (getD_mem blocking_primes_21 (idx - 2100) 3)

lemma mod4_of_mem_blocking_primes_21 {p : ℕ} (h : p ∈ 3 :: blocking_primes_21) : p % 4 = 3 := by
  unfold blocking_primes_21 at h
  simp only [List.mem_cons] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | h_false
  · exact mod4_3
  · exact mod4_59
  · exact mod4_3
  · exact mod4_4723
  · exact mod4_1999
  · exact mod4_3
  · exact mod4_5279
  · exact mod4_12919
  · exact mod4_3
  · exact mod4_6911
  · exact mod4_11
  · exact mod4_3
  · exact mod4_2179
  · exact mod4_59
  · exact mod4_3
  · exact mod4_11
  · exact mod4_2027
  · exact mod4_3
  · exact mod4_863
  · exact mod4_823
  · exact mod4_3
  · exact mod4_7
  · exact mod4_10079
  · exact mod4_199
  · exact mod4_7
  · exact mod4_4363
  · exact mod4_1031
  · exact mod4_7
  · exact mod4_8191
  · exact mod4_11423
  · exact mod4_7
  · exact mod4_307
  · exact mod4_1087
  · exact mod4_7
  · exact mod4_8719
  · exact mod4_15859
  · exact mod4_463
  · exact mod4_5927
  · exact mod4_1487
  · exact mod4_7
  · exact mod4_9787
  · exact mod4_8191
  · exact mod4_7
  · exact mod4_5779
  · exact mod4_4691
  · exact mod4_7
  · exact mod4_9431
  · exact mod4_10531
  · exact mod4_7
  · exact mod4_4987
  · exact mod4_5399
  · exact mod4_7
  · exact mod4_1831
  · exact mod4_1811
  · exact mod4_7
  · exact mod4_9323
  · exact mod4_2447
  · exact mod4_8747
  · exact mod4_1759
  · exact mod4_479
  · exact mod4_7
  · exact mod4_3
  · exact mod4_2803
  · exact mod4_683
  · exact mod4_3
  · exact mod4_3527
  · exact mod4_43
  · exact mod4_3
  · exact mod4_4871
  · exact mod4_31
  · exact mod4_3
  · exact mod4_67
  · exact mod4_9467
  · exact mod4_3
  · exact mod4_31
  · exact mod4_2803
  · exact mod4_3
  · exact mod4_4723
  · exact mod4_1367
  · exact mod4_3
  · exact mod4_43
  · exact mod4_2903
  · exact mod4_3
  · exact mod4_2267
  · exact mod4_31
  · exact mod4_3
  · exact mod4_2111
  · exact mod4_43
  · exact mod4_3
  · exact mod4_31
  · exact mod4_59
  · exact mod4_3
  · exact mod4_2767
  · exact mod4_8191
  · exact mod4_3
  · exact mod4_59
  · exact mod4_431
  · exact mod4_3
  · exact mod4_6263
  · exact mod4_31
  · exact mod4_3
  · cases h_false

lemma blocking_prime_by_idx_21_3mod4 (idx : ℕ) : blocking_prime_by_idx_21 idx % 4 = 3 :=
  mod4_of_mem_blocking_primes_21 (getD_mem blocking_primes_21 (idx - 2100) 3)

def blocking_primes_22 : List ℕ := [3, 11, 31, 3, 3023, 11, 3, 31, 107, 3, 11, 11, 3, 307, 5807, 3, 11, 31, 3, 19, 11, 3, 31, 2731, 3, 11, 11, 3, 19, 83, 3, 11, 31, 3, 131, 11, 3, 19, 6823, 3, 7, 11287, 1231, 7, 251, 5119, 7, 9643, 59, 7, 3347, 151, 59, 199, 15259, 7, 479, 14563, 7, 9103, 3203, 7, 12503, 1627, 7, 5851, 151, 7, 163, 251, 7, 223, 2411, 607, 19891, 2903, 7, 59, 2699, 7, 3, 23, 43, 3, 11, 47, 3, 5419, 19, 3, 991, 127, 3, 67, 11, 3, 43, 19, 3, 11]
def blocking_prime_by_idx_22 (idx : ℕ) : ℕ := blocking_primes_22.getD (idx - 2200) 3

lemma prime_of_mem_blocking_primes_22 {p : ℕ} (h : p ∈ 3 :: blocking_primes_22) : Nat.Prime p := by
  unfold blocking_primes_22 at h
  simp only [List.mem_cons] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | h_false
  · exact prime_3
  · exact prime_3
  · exact prime_11
  · exact prime_31
  · exact prime_3
  · exact prime_3023
  · exact prime_11
  · exact prime_3
  · exact prime_31
  · exact prime_107
  · exact prime_3
  · exact prime_11
  · exact prime_11
  · exact prime_3
  · exact prime_307
  · exact prime_5807
  · exact prime_3
  · exact prime_11
  · exact prime_31
  · exact prime_3
  · exact prime_19
  · exact prime_11
  · exact prime_3
  · exact prime_31
  · exact prime_2731
  · exact prime_3
  · exact prime_11
  · exact prime_11
  · exact prime_3
  · exact prime_19
  · exact prime_83
  · exact prime_3
  · exact prime_11
  · exact prime_31
  · exact prime_3
  · exact prime_131
  · exact prime_11
  · exact prime_3
  · exact prime_19
  · exact prime_6823
  · exact prime_3
  · exact prime_7
  · exact prime_11287
  · exact prime_1231
  · exact prime_7
  · exact prime_251
  · exact prime_5119
  · exact prime_7
  · exact prime_9643
  · exact prime_59
  · exact prime_7
  · exact prime_3347
  · exact prime_151
  · exact prime_59
  · exact prime_199
  · exact prime_15259
  · exact prime_7
  · exact prime_479
  · exact prime_14563
  · exact prime_7
  · exact prime_9103
  · exact prime_3203
  · exact prime_7
  · exact prime_12503
  · exact prime_1627
  · exact prime_7
  · exact prime_5851
  · exact prime_151
  · exact prime_7
  · exact prime_163
  · exact prime_251
  · exact prime_7
  · exact prime_223
  · exact prime_2411
  · exact prime_607
  · exact prime_19891
  · exact prime_2903
  · exact prime_7
  · exact prime_59
  · exact prime_2699
  · exact prime_7
  · exact prime_3
  · exact prime_23
  · exact prime_43
  · exact prime_3
  · exact prime_11
  · exact prime_47
  · exact prime_3
  · exact prime_5419
  · exact prime_19
  · exact prime_3
  · exact prime_991
  · exact prime_127
  · exact prime_3
  · exact prime_67
  · exact prime_11
  · exact prime_3
  · exact prime_43
  · exact prime_19
  · exact prime_3
  · exact prime_11
  · cases h_false

lemma blocking_prime_by_idx_22_prime (idx : ℕ) : Nat.Prime (blocking_prime_by_idx_22 idx) :=
  prime_of_mem_blocking_primes_22 (getD_mem blocking_primes_22 (idx - 2200) 3)

lemma mod4_of_mem_blocking_primes_22 {p : ℕ} (h : p ∈ 3 :: blocking_primes_22) : p % 4 = 3 := by
  unfold blocking_primes_22 at h
  simp only [List.mem_cons] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | h_false
  · exact mod4_3
  · exact mod4_3
  · exact mod4_11
  · exact mod4_31
  · exact mod4_3
  · exact mod4_3023
  · exact mod4_11
  · exact mod4_3
  · exact mod4_31
  · exact mod4_107
  · exact mod4_3
  · exact mod4_11
  · exact mod4_11
  · exact mod4_3
  · exact mod4_307
  · exact mod4_5807
  · exact mod4_3
  · exact mod4_11
  · exact mod4_31
  · exact mod4_3
  · exact mod4_19
  · exact mod4_11
  · exact mod4_3
  · exact mod4_31
  · exact mod4_2731
  · exact mod4_3
  · exact mod4_11
  · exact mod4_11
  · exact mod4_3
  · exact mod4_19
  · exact mod4_83
  · exact mod4_3
  · exact mod4_11
  · exact mod4_31
  · exact mod4_3
  · exact mod4_131
  · exact mod4_11
  · exact mod4_3
  · exact mod4_19
  · exact mod4_6823
  · exact mod4_3
  · exact mod4_7
  · exact mod4_11287
  · exact mod4_1231
  · exact mod4_7
  · exact mod4_251
  · exact mod4_5119
  · exact mod4_7
  · exact mod4_9643
  · exact mod4_59
  · exact mod4_7
  · exact mod4_3347
  · exact mod4_151
  · exact mod4_59
  · exact mod4_199
  · exact mod4_15259
  · exact mod4_7
  · exact mod4_479
  · exact mod4_14563
  · exact mod4_7
  · exact mod4_9103
  · exact mod4_3203
  · exact mod4_7
  · exact mod4_12503
  · exact mod4_1627
  · exact mod4_7
  · exact mod4_5851
  · exact mod4_151
  · exact mod4_7
  · exact mod4_163
  · exact mod4_251
  · exact mod4_7
  · exact mod4_223
  · exact mod4_2411
  · exact mod4_607
  · exact mod4_19891
  · exact mod4_2903
  · exact mod4_7
  · exact mod4_59
  · exact mod4_2699
  · exact mod4_7
  · exact mod4_3
  · exact mod4_23
  · exact mod4_43
  · exact mod4_3
  · exact mod4_11
  · exact mod4_47
  · exact mod4_3
  · exact mod4_5419
  · exact mod4_19
  · exact mod4_3
  · exact mod4_991
  · exact mod4_127
  · exact mod4_3
  · exact mod4_67
  · exact mod4_11
  · exact mod4_3
  · exact mod4_43
  · exact mod4_19
  · exact mod4_3
  · exact mod4_11
  · cases h_false

lemma blocking_prime_by_idx_22_3mod4 (idx : ℕ) : blocking_prime_by_idx_22 idx % 4 = 3 :=
  mod4_of_mem_blocking_primes_22 (getD_mem blocking_primes_22 (idx - 2200) 3)

def blocking_primes_23 : List ℕ := [2143, 3, 6779, 23, 3, 127, 19, 3, 47, 11, 3, 79, 127, 3, 11, 19, 3, 43, 4211, 3, 3, 1511, 2243, 3, 5387, 5903, 3, 3779, 4603, 3, 83, 1031, 3, 2659, 1583, 3, 11807, 127, 3, 17519, 683, 3, 79, 5927, 3, 9151, 59, 3, 1259, 47, 3, 127, 283, 3, 211, 7523, 3, 2767, 127, 3, 7, 1039, 83, 7, 14627, 3167, 7, 71, 31, 2699, 23, 263, 7, 31, 8839, 7, 4463, 1319, 7, 3659, 2971, 7, 6211, 31, 7, 1163, 1459, 7, 31, 2179, 211, 10099, 23, 7, 3511, 131, 7, 191, 31, 7]
def blocking_prime_by_idx_23 (idx : ℕ) : ℕ := blocking_primes_23.getD (idx - 2300) 3

lemma prime_of_mem_blocking_primes_23 {p : ℕ} (h : p ∈ 3 :: blocking_primes_23) : Nat.Prime p := by
  unfold blocking_primes_23 at h
  simp only [List.mem_cons] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | h_false
  · exact prime_3
  · exact prime_2143
  · exact prime_3
  · exact prime_6779
  · exact prime_23
  · exact prime_3
  · exact prime_127
  · exact prime_19
  · exact prime_3
  · exact prime_47
  · exact prime_11
  · exact prime_3
  · exact prime_79
  · exact prime_127
  · exact prime_3
  · exact prime_11
  · exact prime_19
  · exact prime_3
  · exact prime_43
  · exact prime_4211
  · exact prime_3
  · exact prime_3
  · exact prime_1511
  · exact prime_2243
  · exact prime_3
  · exact prime_5387
  · exact prime_5903
  · exact prime_3
  · exact prime_3779
  · exact prime_4603
  · exact prime_3
  · exact prime_83
  · exact prime_1031
  · exact prime_3
  · exact prime_2659
  · exact prime_1583
  · exact prime_3
  · exact prime_11807
  · exact prime_127
  · exact prime_3
  · exact prime_17519
  · exact prime_683
  · exact prime_3
  · exact prime_79
  · exact prime_5927
  · exact prime_3
  · exact prime_9151
  · exact prime_59
  · exact prime_3
  · exact prime_1259
  · exact prime_47
  · exact prime_3
  · exact prime_127
  · exact prime_283
  · exact prime_3
  · exact prime_211
  · exact prime_7523
  · exact prime_3
  · exact prime_2767
  · exact prime_127
  · exact prime_3
  · exact prime_7
  · exact prime_1039
  · exact prime_83
  · exact prime_7
  · exact prime_14627
  · exact prime_3167
  · exact prime_7
  · exact prime_71
  · exact prime_31
  · exact prime_2699
  · exact prime_23
  · exact prime_263
  · exact prime_7
  · exact prime_31
  · exact prime_8839
  · exact prime_7
  · exact prime_4463
  · exact prime_1319
  · exact prime_7
  · exact prime_3659
  · exact prime_2971
  · exact prime_7
  · exact prime_6211
  · exact prime_31
  · exact prime_7
  · exact prime_1163
  · exact prime_1459
  · exact prime_7
  · exact prime_31
  · exact prime_2179
  · exact prime_211
  · exact prime_10099
  · exact prime_23
  · exact prime_7
  · exact prime_3511
  · exact prime_131
  · exact prime_7
  · exact prime_191
  · exact prime_31
  · exact prime_7
  · cases h_false

lemma blocking_prime_by_idx_23_prime (idx : ℕ) : Nat.Prime (blocking_prime_by_idx_23 idx) :=
  prime_of_mem_blocking_primes_23 (getD_mem blocking_primes_23 (idx - 2300) 3)

lemma mod4_of_mem_blocking_primes_23 {p : ℕ} (h : p ∈ 3 :: blocking_primes_23) : p % 4 = 3 := by
  unfold blocking_primes_23 at h
  simp only [List.mem_cons] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | h_false
  · exact mod4_3
  · exact mod4_2143
  · exact mod4_3
  · exact mod4_6779
  · exact mod4_23
  · exact mod4_3
  · exact mod4_127
  · exact mod4_19
  · exact mod4_3
  · exact mod4_47
  · exact mod4_11
  · exact mod4_3
  · exact mod4_79
  · exact mod4_127
  · exact mod4_3
  · exact mod4_11
  · exact mod4_19
  · exact mod4_3
  · exact mod4_43
  · exact mod4_4211
  · exact mod4_3
  · exact mod4_3
  · exact mod4_1511
  · exact mod4_2243
  · exact mod4_3
  · exact mod4_5387
  · exact mod4_5903
  · exact mod4_3
  · exact mod4_3779
  · exact mod4_4603
  · exact mod4_3
  · exact mod4_83
  · exact mod4_1031
  · exact mod4_3
  · exact mod4_2659
  · exact mod4_1583
  · exact mod4_3
  · exact mod4_11807
  · exact mod4_127
  · exact mod4_3
  · exact mod4_17519
  · exact mod4_683
  · exact mod4_3
  · exact mod4_79
  · exact mod4_5927
  · exact mod4_3
  · exact mod4_9151
  · exact mod4_59
  · exact mod4_3
  · exact mod4_1259
  · exact mod4_47
  · exact mod4_3
  · exact mod4_127
  · exact mod4_283
  · exact mod4_3
  · exact mod4_211
  · exact mod4_7523
  · exact mod4_3
  · exact mod4_2767
  · exact mod4_127
  · exact mod4_3
  · exact mod4_7
  · exact mod4_1039
  · exact mod4_83
  · exact mod4_7
  · exact mod4_14627
  · exact mod4_3167
  · exact mod4_7
  · exact mod4_71
  · exact mod4_31
  · exact mod4_2699
  · exact mod4_23
  · exact mod4_263
  · exact mod4_7
  · exact mod4_31
  · exact mod4_8839
  · exact mod4_7
  · exact mod4_4463
  · exact mod4_1319
  · exact mod4_7
  · exact mod4_3659
  · exact mod4_2971
  · exact mod4_7
  · exact mod4_6211
  · exact mod4_31
  · exact mod4_7
  · exact mod4_1163
  · exact mod4_1459
  · exact mod4_7
  · exact mod4_31
  · exact mod4_2179
  · exact mod4_211
  · exact mod4_10099
  · exact mod4_23
  · exact mod4_7
  · exact mod4_3511
  · exact mod4_131
  · exact mod4_7
  · exact mod4_191
  · exact mod4_31
  · exact mod4_7
  · cases h_false

lemma blocking_prime_by_idx_23_3mod4 (idx : ℕ) : blocking_prime_by_idx_23 idx % 4 = 3 :=
  mod4_of_mem_blocking_primes_23 (getD_mem blocking_primes_23 (idx - 2300) 3)

def blocking_primes_24 : List ℕ := [3, 6263, 31, 3, 71, 11, 3, 31, 223, 3, 11, 11, 3, 7727, 5039, 3, 11, 31, 3, 9319, 11, 3, 31, 2203, 3, 11, 11, 3, 23, 2267, 3, 11, 31, 3, 4259, 11, 3, 31, 1291, 3, 3, 59, 1663, 3, 991, 23, 3, 17471, 10159, 3, 1279, 3271, 3, 3767, 383, 3, 23, 1171, 3, 43, 14251, 3, 139, 47, 3, 607, 43, 3, 103, 10267, 3, 331, 3803, 3, 367, 5167, 3, 2087, 23, 3, 7, 3491, 1567, 7, 11, 15991, 3203, 9371, 2063, 7, 19891, 5531, 7, 727, 11, 7, 2731, 283, 7, 11]
def blocking_prime_by_idx_24 (idx : ℕ) : ℕ := blocking_primes_24.getD (idx - 2400) 3

lemma prime_of_mem_blocking_primes_24 {p : ℕ} (h : p ∈ 3 :: blocking_primes_24) : Nat.Prime p := by
  unfold blocking_primes_24 at h
  simp only [List.mem_cons] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | h_false
  · exact prime_3
  · exact prime_3
  · exact prime_6263
  · exact prime_31
  · exact prime_3
  · exact prime_71
  · exact prime_11
  · exact prime_3
  · exact prime_31
  · exact prime_223
  · exact prime_3
  · exact prime_11
  · exact prime_11
  · exact prime_3
  · exact prime_7727
  · exact prime_5039
  · exact prime_3
  · exact prime_11
  · exact prime_31
  · exact prime_3
  · exact prime_9319
  · exact prime_11
  · exact prime_3
  · exact prime_31
  · exact prime_2203
  · exact prime_3
  · exact prime_11
  · exact prime_11
  · exact prime_3
  · exact prime_23
  · exact prime_2267
  · exact prime_3
  · exact prime_11
  · exact prime_31
  · exact prime_3
  · exact prime_4259
  · exact prime_11
  · exact prime_3
  · exact prime_31
  · exact prime_1291
  · exact prime_3
  · exact prime_3
  · exact prime_59
  · exact prime_1663
  · exact prime_3
  · exact prime_991
  · exact prime_23
  · exact prime_3
  · exact prime_17471
  · exact prime_10159
  · exact prime_3
  · exact prime_1279
  · exact prime_3271
  · exact prime_3
  · exact prime_3767
  · exact prime_383
  · exact prime_3
  · exact prime_23
  · exact prime_1171
  · exact prime_3
  · exact prime_43
  · exact prime_14251
  · exact prime_3
  · exact prime_139
  · exact prime_47
  · exact prime_3
  · exact prime_607
  · exact prime_43
  · exact prime_3
  · exact prime_103
  · exact prime_10267
  · exact prime_3
  · exact prime_331
  · exact prime_3803
  · exact prime_3
  · exact prime_367
  · exact prime_5167
  · exact prime_3
  · exact prime_2087
  · exact prime_23
  · exact prime_3
  · exact prime_7
  · exact prime_3491
  · exact prime_1567
  · exact prime_7
  · exact prime_11
  · exact prime_15991
  · exact prime_3203
  · exact prime_9371
  · exact prime_2063
  · exact prime_7
  · exact prime_19891
  · exact prime_5531
  · exact prime_7
  · exact prime_727
  · exact prime_11
  · exact prime_7
  · exact prime_2731
  · exact prime_283
  · exact prime_7
  · exact prime_11
  · cases h_false

lemma blocking_prime_by_idx_24_prime (idx : ℕ) : Nat.Prime (blocking_prime_by_idx_24 idx) :=
  prime_of_mem_blocking_primes_24 (getD_mem blocking_primes_24 (idx - 2400) 3)

lemma mod4_of_mem_blocking_primes_24 {p : ℕ} (h : p ∈ 3 :: blocking_primes_24) : p % 4 = 3 := by
  unfold blocking_primes_24 at h
  simp only [List.mem_cons] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | h_false
  · exact mod4_3
  · exact mod4_3
  · exact mod4_6263
  · exact mod4_31
  · exact mod4_3
  · exact mod4_71
  · exact mod4_11
  · exact mod4_3
  · exact mod4_31
  · exact mod4_223
  · exact mod4_3
  · exact mod4_11
  · exact mod4_11
  · exact mod4_3
  · exact mod4_7727
  · exact mod4_5039
  · exact mod4_3
  · exact mod4_11
  · exact mod4_31
  · exact mod4_3
  · exact mod4_9319
  · exact mod4_11
  · exact mod4_3
  · exact mod4_31
  · exact mod4_2203
  · exact mod4_3
  · exact mod4_11
  · exact mod4_11
  · exact mod4_3
  · exact mod4_23
  · exact mod4_2267
  · exact mod4_3
  · exact mod4_11
  · exact mod4_31
  · exact mod4_3
  · exact mod4_4259
  · exact mod4_11
  · exact mod4_3
  · exact mod4_31
  · exact mod4_1291
  · exact mod4_3
  · exact mod4_3
  · exact mod4_59
  · exact mod4_1663
  · exact mod4_3
  · exact mod4_991
  · exact mod4_23
  · exact mod4_3
  · exact mod4_17471
  · exact mod4_10159
  · exact mod4_3
  · exact mod4_1279
  · exact mod4_3271
  · exact mod4_3
  · exact mod4_3767
  · exact mod4_383
  · exact mod4_3
  · exact mod4_23
  · exact mod4_1171
  · exact mod4_3
  · exact mod4_43
  · exact mod4_14251
  · exact mod4_3
  · exact mod4_139
  · exact mod4_47
  · exact mod4_3
  · exact mod4_607
  · exact mod4_43
  · exact mod4_3
  · exact mod4_103
  · exact mod4_10267
  · exact mod4_3
  · exact mod4_331
  · exact mod4_3803
  · exact mod4_3
  · exact mod4_367
  · exact mod4_5167
  · exact mod4_3
  · exact mod4_2087
  · exact mod4_23
  · exact mod4_3
  · exact mod4_7
  · exact mod4_3491
  · exact mod4_1567
  · exact mod4_7
  · exact mod4_11
  · exact mod4_15991
  · exact mod4_3203
  · exact mod4_9371
  · exact mod4_2063
  · exact mod4_7
  · exact mod4_19891
  · exact mod4_5531
  · exact mod4_7
  · exact mod4_727
  · exact mod4_11
  · exact mod4_7
  · exact mod4_2731
  · exact mod4_283
  · exact mod4_7
  · exact mod4_11
  · cases h_false

lemma blocking_prime_by_idx_24_3mod4 (idx : ℕ) : blocking_prime_by_idx_24 idx % 4 = 3 :=
  mod4_of_mem_blocking_primes_24 (getD_mem blocking_primes_24 (idx - 2400) 3)

def blocking_primes_25 : List ℕ := [11047, 7, 19319, 6827, 7, 2347, 17027, 47, 1667, 11, 7, 467, 79, 7, 11, 8699, 7, 6067, 887, 7, 3, 1579, 1607, 3, 151, 4051, 3, 7919, 8863, 3, 6659, 4547, 3, 167, 331, 3, 6199, 79, 3, 151, 8147, 3, 13367, 8311, 3, 191, 1427, 3, 59, 331, 3, 2287, 2399, 3, 151, 307, 3, 2039, 59, 3, 3, 19, 43, 3, 127, 6991, 3, 283, 31, 3, 19, 127, 3, 31, 7603, 3, 43, 5099, 3, 19, 15887, 3, 59, 31, 3, 3607, 3643, 3, 19, 271, 3, 19891, 127, 3, 2351, 479, 3, 43, 31, 3]
def blocking_prime_by_idx_25 (idx : ℕ) : ℕ := blocking_primes_25.getD (idx - 2500) 3

lemma prime_of_mem_blocking_primes_25 {p : ℕ} (h : p ∈ 3 :: blocking_primes_25) : Nat.Prime p := by
  unfold blocking_primes_25 at h
  simp only [List.mem_cons] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | h_false
  · exact prime_3
  · exact prime_11047
  · exact prime_7
  · exact prime_19319
  · exact prime_6827
  · exact prime_7
  · exact prime_2347
  · exact prime_17027
  · exact prime_47
  · exact prime_1667
  · exact prime_11
  · exact prime_7
  · exact prime_467
  · exact prime_79
  · exact prime_7
  · exact prime_11
  · exact prime_8699
  · exact prime_7
  · exact prime_6067
  · exact prime_887
  · exact prime_7
  · exact prime_3
  · exact prime_1579
  · exact prime_1607
  · exact prime_3
  · exact prime_151
  · exact prime_4051
  · exact prime_3
  · exact prime_7919
  · exact prime_8863
  · exact prime_3
  · exact prime_6659
  · exact prime_4547
  · exact prime_3
  · exact prime_167
  · exact prime_331
  · exact prime_3
  · exact prime_6199
  · exact prime_79
  · exact prime_3
  · exact prime_151
  · exact prime_8147
  · exact prime_3
  · exact prime_13367
  · exact prime_8311
  · exact prime_3
  · exact prime_191
  · exact prime_1427
  · exact prime_3
  · exact prime_59
  · exact prime_331
  · exact prime_3
  · exact prime_2287
  · exact prime_2399
  · exact prime_3
  · exact prime_151
  · exact prime_307
  · exact prime_3
  · exact prime_2039
  · exact prime_59
  · exact prime_3
  · exact prime_3
  · exact prime_19
  · exact prime_43
  · exact prime_3
  · exact prime_127
  · exact prime_6991
  · exact prime_3
  · exact prime_283
  · exact prime_31
  · exact prime_3
  · exact prime_19
  · exact prime_127
  · exact prime_3
  · exact prime_31
  · exact prime_7603
  · exact prime_3
  · exact prime_43
  · exact prime_5099
  · exact prime_3
  · exact prime_19
  · exact prime_15887
  · exact prime_3
  · exact prime_59
  · exact prime_31
  · exact prime_3
  · exact prime_3607
  · exact prime_3643
  · exact prime_3
  · exact prime_19
  · exact prime_271
  · exact prime_3
  · exact prime_19891
  · exact prime_127
  · exact prime_3
  · exact prime_2351
  · exact prime_479
  · exact prime_3
  · exact prime_43
  · exact prime_31
  · exact prime_3
  · cases h_false

lemma blocking_prime_by_idx_25_prime (idx : ℕ) : Nat.Prime (blocking_prime_by_idx_25 idx) :=
  prime_of_mem_blocking_primes_25 (getD_mem blocking_primes_25 (idx - 2500) 3)

lemma mod4_of_mem_blocking_primes_25 {p : ℕ} (h : p ∈ 3 :: blocking_primes_25) : p % 4 = 3 := by
  unfold blocking_primes_25 at h
  simp only [List.mem_cons] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | h_false
  · exact mod4_3
  · exact mod4_11047
  · exact mod4_7
  · exact mod4_19319
  · exact mod4_6827
  · exact mod4_7
  · exact mod4_2347
  · exact mod4_17027
  · exact mod4_47
  · exact mod4_1667
  · exact mod4_11
  · exact mod4_7
  · exact mod4_467
  · exact mod4_79
  · exact mod4_7
  · exact mod4_11
  · exact mod4_8699
  · exact mod4_7
  · exact mod4_6067
  · exact mod4_887
  · exact mod4_7
  · exact mod4_3
  · exact mod4_1579
  · exact mod4_1607
  · exact mod4_3
  · exact mod4_151
  · exact mod4_4051
  · exact mod4_3
  · exact mod4_7919
  · exact mod4_8863
  · exact mod4_3
  · exact mod4_6659
  · exact mod4_4547
  · exact mod4_3
  · exact mod4_167
  · exact mod4_331
  · exact mod4_3
  · exact mod4_6199
  · exact mod4_79
  · exact mod4_3
  · exact mod4_151
  · exact mod4_8147
  · exact mod4_3
  · exact mod4_13367
  · exact mod4_8311
  · exact mod4_3
  · exact mod4_191
  · exact mod4_1427
  · exact mod4_3
  · exact mod4_59
  · exact mod4_331
  · exact mod4_3
  · exact mod4_2287
  · exact mod4_2399
  · exact mod4_3
  · exact mod4_151
  · exact mod4_307
  · exact mod4_3
  · exact mod4_2039
  · exact mod4_59
  · exact mod4_3
  · exact mod4_3
  · exact mod4_19
  · exact mod4_43
  · exact mod4_3
  · exact mod4_127
  · exact mod4_6991
  · exact mod4_3
  · exact mod4_283
  · exact mod4_31
  · exact mod4_3
  · exact mod4_19
  · exact mod4_127
  · exact mod4_3
  · exact mod4_31
  · exact mod4_7603
  · exact mod4_3
  · exact mod4_43
  · exact mod4_5099
  · exact mod4_3
  · exact mod4_19
  · exact mod4_15887
  · exact mod4_3
  · exact mod4_59
  · exact mod4_31
  · exact mod4_3
  · exact mod4_3607
  · exact mod4_3643
  · exact mod4_3
  · exact mod4_19
  · exact mod4_271
  · exact mod4_3
  · exact mod4_19891
  · exact mod4_127
  · exact mod4_3
  · exact mod4_2351
  · exact mod4_479
  · exact mod4_3
  · exact mod4_43
  · exact mod4_31
  · exact mod4_3
  · cases h_false

lemma blocking_prime_by_idx_25_3mod4 (idx : ℕ) : blocking_prime_by_idx_25 idx % 4 = 3 :=
  mod4_of_mem_blocking_primes_25 (getD_mem blocking_primes_25 (idx - 2500) 3)

def blocking_primes_26 : List ℕ := [7, 11, 31, 127, 10859, 11, 7, 31, 1103, 7, 11, 11, 7, 683, 2087, 7, 5651, 31, 7, 1451, 11, 7, 31, 2339, 127, 11, 11, 7, 787, 5443, 7, 11, 31, 7, 823, 11, 7, 31, 127, 7, 3, 4483, 7459, 3, 16603, 5039, 3, 8191, 19, 3, 13691, 10607, 3, 2699, 9043, 3, 1399, 887, 3, 13367, 8191, 3, 9311, 103, 3, 4099, 19, 3, 2399, 4159, 3, 4931, 6551, 3, 10163, 19, 3, 107, 4919, 3, 3, 4759, 11839, 3, 11, 8147, 3, 1123, 103, 3, 743, 1999, 3, 17107, 11, 3, 1627, 8999, 3, 11]
def blocking_prime_by_idx_26 (idx : ℕ) : ℕ := blocking_primes_26.getD (idx - 2600) 3

lemma prime_of_mem_blocking_primes_26 {p : ℕ} (h : p ∈ 3 :: blocking_primes_26) : Nat.Prime p := by
  unfold blocking_primes_26 at h
  simp only [List.mem_cons] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | h_false
  · exact prime_3
  · exact prime_7
  · exact prime_11
  · exact prime_31
  · exact prime_127
  · exact prime_10859
  · exact prime_11
  · exact prime_7
  · exact prime_31
  · exact prime_1103
  · exact prime_7
  · exact prime_11
  · exact prime_11
  · exact prime_7
  · exact prime_683
  · exact prime_2087
  · exact prime_7
  · exact prime_5651
  · exact prime_31
  · exact prime_7
  · exact prime_1451
  · exact prime_11
  · exact prime_7
  · exact prime_31
  · exact prime_2339
  · exact prime_127
  · exact prime_11
  · exact prime_11
  · exact prime_7
  · exact prime_787
  · exact prime_5443
  · exact prime_7
  · exact prime_11
  · exact prime_31
  · exact prime_7
  · exact prime_823
  · exact prime_11
  · exact prime_7
  · exact prime_31
  · exact prime_127
  · exact prime_7
  · exact prime_3
  · exact prime_4483
  · exact prime_7459
  · exact prime_3
  · exact prime_16603
  · exact prime_5039
  · exact prime_3
  · exact prime_8191
  · exact prime_19
  · exact prime_3
  · exact prime_13691
  · exact prime_10607
  · exact prime_3
  · exact prime_2699
  · exact prime_9043
  · exact prime_3
  · exact prime_1399
  · exact prime_887
  · exact prime_3
  · exact prime_13367
  · exact prime_8191
  · exact prime_3
  · exact prime_9311
  · exact prime_103
  · exact prime_3
  · exact prime_4099
  · exact prime_19
  · exact prime_3
  · exact prime_2399
  · exact prime_4159
  · exact prime_3
  · exact prime_4931
  · exact prime_6551
  · exact prime_3
  · exact prime_10163
  · exact prime_19
  · exact prime_3
  · exact prime_107
  · exact prime_4919
  · exact prime_3
  · exact prime_3
  · exact prime_4759
  · exact prime_11839
  · exact prime_3
  · exact prime_11
  · exact prime_8147
  · exact prime_3
  · exact prime_1123
  · exact prime_103
  · exact prime_3
  · exact prime_743
  · exact prime_1999
  · exact prime_3
  · exact prime_17107
  · exact prime_11
  · exact prime_3
  · exact prime_1627
  · exact prime_8999
  · exact prime_3
  · exact prime_11
  · cases h_false

lemma blocking_prime_by_idx_26_prime (idx : ℕ) : Nat.Prime (blocking_prime_by_idx_26 idx) :=
  prime_of_mem_blocking_primes_26 (getD_mem blocking_primes_26 (idx - 2600) 3)

lemma mod4_of_mem_blocking_primes_26 {p : ℕ} (h : p ∈ 3 :: blocking_primes_26) : p % 4 = 3 := by
  unfold blocking_primes_26 at h
  simp only [List.mem_cons] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | h_false
  · exact mod4_3
  · exact mod4_7
  · exact mod4_11
  · exact mod4_31
  · exact mod4_127
  · exact mod4_10859
  · exact mod4_11
  · exact mod4_7
  · exact mod4_31
  · exact mod4_1103
  · exact mod4_7
  · exact mod4_11
  · exact mod4_11
  · exact mod4_7
  · exact mod4_683
  · exact mod4_2087
  · exact mod4_7
  · exact mod4_5651
  · exact mod4_31
  · exact mod4_7
  · exact mod4_1451
  · exact mod4_11
  · exact mod4_7
  · exact mod4_31
  · exact mod4_2339
  · exact mod4_127
  · exact mod4_11
  · exact mod4_11
  · exact mod4_7
  · exact mod4_787
  · exact mod4_5443
  · exact mod4_7
  · exact mod4_11
  · exact mod4_31
  · exact mod4_7
  · exact mod4_823
  · exact mod4_11
  · exact mod4_7
  · exact mod4_31
  · exact mod4_127
  · exact mod4_7
  · exact mod4_3
  · exact mod4_4483
  · exact mod4_7459
  · exact mod4_3
  · exact mod4_16603
  · exact mod4_5039
  · exact mod4_3
  · exact mod4_8191
  · exact mod4_19
  · exact mod4_3
  · exact mod4_13691
  · exact mod4_10607
  · exact mod4_3
  · exact mod4_2699
  · exact mod4_9043
  · exact mod4_3
  · exact mod4_1399
  · exact mod4_887
  · exact mod4_3
  · exact mod4_13367
  · exact mod4_8191
  · exact mod4_3
  · exact mod4_9311
  · exact mod4_103
  · exact mod4_3
  · exact mod4_4099
  · exact mod4_19
  · exact mod4_3
  · exact mod4_2399
  · exact mod4_4159
  · exact mod4_3
  · exact mod4_4931
  · exact mod4_6551
  · exact mod4_3
  · exact mod4_10163
  · exact mod4_19
  · exact mod4_3
  · exact mod4_107
  · exact mod4_4919
  · exact mod4_3
  · exact mod4_3
  · exact mod4_4759
  · exact mod4_11839
  · exact mod4_3
  · exact mod4_11
  · exact mod4_8147
  · exact mod4_3
  · exact mod4_1123
  · exact mod4_103
  · exact mod4_3
  · exact mod4_743
  · exact mod4_1999
  · exact mod4_3
  · exact mod4_17107
  · exact mod4_11
  · exact mod4_3
  · exact mod4_1627
  · exact mod4_8999
  · exact mod4_3
  · exact mod4_11
  · cases h_false

lemma blocking_prime_by_idx_26_3mod4 (idx : ℕ) : blocking_prime_by_idx_26 idx % 4 = 3 :=
  mod4_of_mem_blocking_primes_26 (getD_mem blocking_primes_26 (idx - 2600) 3)

def blocking_primes_27 : List ℕ := [5531, 3, 4603, 827, 3, 14939, 3631, 3, 283, 11, 3, 7019, 8191, 3, 11, 7691, 3, 307, 8627, 3, 5107, 23, 13591, 7, 907, 43, 7, 17239, 71, 7, 2731, 1619, 7, 3719, 4951, 7, 1031, 2207, 7, 43, 179, 347, 2087, 23, 7, 9239, 43, 7, 11519, 14699, 7, 71, 6791, 7, 23, 8423, 7, 2843, 107, 7, 3, 7691, 631, 3, 3371, 103, 3, 2011, 31, 3, 6791, 71, 3, 31, 4831, 3, 1847, 107, 3, 3907, 683, 3, 2539, 31, 3, 883, 4871, 3, 31, 107, 3, 683, 239, 3, 947, 607, 3, 11867, 31, 3]
def blocking_prime_by_idx_27 (idx : ℕ) : ℕ := blocking_primes_27.getD (idx - 2700) 3

lemma prime_of_mem_blocking_primes_27 {p : ℕ} (h : p ∈ 3 :: blocking_primes_27) : Nat.Prime p := by
  unfold blocking_primes_27 at h
  simp only [List.mem_cons] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | h_false
  · exact prime_3
  · exact prime_5531
  · exact prime_3
  · exact prime_4603
  · exact prime_827
  · exact prime_3
  · exact prime_14939
  · exact prime_3631
  · exact prime_3
  · exact prime_283
  · exact prime_11
  · exact prime_3
  · exact prime_7019
  · exact prime_8191
  · exact prime_3
  · exact prime_11
  · exact prime_7691
  · exact prime_3
  · exact prime_307
  · exact prime_8627
  · exact prime_3
  · exact prime_5107
  · exact prime_23
  · exact prime_13591
  · exact prime_7
  · exact prime_907
  · exact prime_43
  · exact prime_7
  · exact prime_17239
  · exact prime_71
  · exact prime_7
  · exact prime_2731
  · exact prime_1619
  · exact prime_7
  · exact prime_3719
  · exact prime_4951
  · exact prime_7
  · exact prime_1031
  · exact prime_2207
  · exact prime_7
  · exact prime_43
  · exact prime_179
  · exact prime_347
  · exact prime_2087
  · exact prime_23
  · exact prime_7
  · exact prime_9239
  · exact prime_43
  · exact prime_7
  · exact prime_11519
  · exact prime_14699
  · exact prime_7
  · exact prime_71
  · exact prime_6791
  · exact prime_7
  · exact prime_23
  · exact prime_8423
  · exact prime_7
  · exact prime_2843
  · exact prime_107
  · exact prime_7
  · exact prime_3
  · exact prime_7691
  · exact prime_631
  · exact prime_3
  · exact prime_3371
  · exact prime_103
  · exact prime_3
  · exact prime_2011
  · exact prime_31
  · exact prime_3
  · exact prime_6791
  · exact prime_71
  · exact prime_3
  · exact prime_31
  · exact prime_4831
  · exact prime_3
  · exact prime_1847
  · exact prime_107
  · exact prime_3
  · exact prime_3907
  · exact prime_683
  · exact prime_3
  · exact prime_2539
  · exact prime_31
  · exact prime_3
  · exact prime_883
  · exact prime_4871
  · exact prime_3
  · exact prime_31
  · exact prime_107
  · exact prime_3
  · exact prime_683
  · exact prime_239
  · exact prime_3
  · exact prime_947
  · exact prime_607
  · exact prime_3
  · exact prime_11867
  · exact prime_31
  · exact prime_3
  · cases h_false

lemma blocking_prime_by_idx_27_prime (idx : ℕ) : Nat.Prime (blocking_prime_by_idx_27 idx) :=
  prime_of_mem_blocking_primes_27 (getD_mem blocking_primes_27 (idx - 2700) 3)

lemma mod4_of_mem_blocking_primes_27 {p : ℕ} (h : p ∈ 3 :: blocking_primes_27) : p % 4 = 3 := by
  unfold blocking_primes_27 at h
  simp only [List.mem_cons] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | h_false
  · exact mod4_3
  · exact mod4_5531
  · exact mod4_3
  · exact mod4_4603
  · exact mod4_827
  · exact mod4_3
  · exact mod4_14939
  · exact mod4_3631
  · exact mod4_3
  · exact mod4_283
  · exact mod4_11
  · exact mod4_3
  · exact mod4_7019
  · exact mod4_8191
  · exact mod4_3
  · exact mod4_11
  · exact mod4_7691
  · exact mod4_3
  · exact mod4_307
  · exact mod4_8627
  · exact mod4_3
  · exact mod4_5107
  · exact mod4_23
  · exact mod4_13591
  · exact mod4_7
  · exact mod4_907
  · exact mod4_43
  · exact mod4_7
  · exact mod4_17239
  · exact mod4_71
  · exact mod4_7
  · exact mod4_2731
  · exact mod4_1619
  · exact mod4_7
  · exact mod4_3719
  · exact mod4_4951
  · exact mod4_7
  · exact mod4_1031
  · exact mod4_2207
  · exact mod4_7
  · exact mod4_43
  · exact mod4_179
  · exact mod4_347
  · exact mod4_2087
  · exact mod4_23
  · exact mod4_7
  · exact mod4_9239
  · exact mod4_43
  · exact mod4_7
  · exact mod4_11519
  · exact mod4_14699
  · exact mod4_7
  · exact mod4_71
  · exact mod4_6791
  · exact mod4_7
  · exact mod4_23
  · exact mod4_8423
  · exact mod4_7
  · exact mod4_2843
  · exact mod4_107
  · exact mod4_7
  · exact mod4_3
  · exact mod4_7691
  · exact mod4_631
  · exact mod4_3
  · exact mod4_3371
  · exact mod4_103
  · exact mod4_3
  · exact mod4_2011
  · exact mod4_31
  · exact mod4_3
  · exact mod4_6791
  · exact mod4_71
  · exact mod4_3
  · exact mod4_31
  · exact mod4_4831
  · exact mod4_3
  · exact mod4_1847
  · exact mod4_107
  · exact mod4_3
  · exact mod4_3907
  · exact mod4_683
  · exact mod4_3
  · exact mod4_2539
  · exact mod4_31
  · exact mod4_3
  · exact mod4_883
  · exact mod4_4871
  · exact mod4_3
  · exact mod4_31
  · exact mod4_107
  · exact mod4_3
  · exact mod4_683
  · exact mod4_239
  · exact mod4_3
  · exact mod4_947
  · exact mod4_607
  · exact mod4_3
  · exact mod4_11867
  · exact mod4_31
  · exact mod4_3
  · cases h_false

lemma blocking_prime_by_idx_27_3mod4 (idx : ℕ) : blocking_prime_by_idx_27 idx % 4 = 3 :=
  mod4_of_mem_blocking_primes_27 (getD_mem blocking_primes_27 (idx - 2700) 3)

def blocking_primes_28 : List ℕ := [3, 11, 31, 3, 1087, 11, 3, 31, 6703, 3, 11, 11, 3, 3079, 6247, 3, 11, 31, 3, 47, 11, 3, 31, 6211, 3, 11, 11, 3, 1987, 2423, 3, 587, 31, 3, 67, 11, 3, 31, 1871, 3, 7, 5903, 43, 7, 7411, 947, 7, 5471, 2879, 7, 1483, 23, 7, 1523, 5419, 7, 43, 23, 127, 4027, 1811, 7, 23, 43, 7, 47, 151, 7, 23, 607, 7, 10067, 127, 7, 2791, 5419, 7, 43, 139, 127, 3, 10607, 5147, 3, 11, 23, 3, 1931, 7103, 3, 127, 6619, 3, 9463, 11, 3, 23, 127, 3, 11]
def blocking_prime_by_idx_28 (idx : ℕ) : ℕ := blocking_primes_28.getD (idx - 2800) 3

lemma prime_of_mem_blocking_primes_28 {p : ℕ} (h : p ∈ 3 :: blocking_primes_28) : Nat.Prime p := by
  unfold blocking_primes_28 at h
  simp only [List.mem_cons] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | h_false
  · exact prime_3
  · exact prime_3
  · exact prime_11
  · exact prime_31
  · exact prime_3
  · exact prime_1087
  · exact prime_11
  · exact prime_3
  · exact prime_31
  · exact prime_6703
  · exact prime_3
  · exact prime_11
  · exact prime_11
  · exact prime_3
  · exact prime_3079
  · exact prime_6247
  · exact prime_3
  · exact prime_11
  · exact prime_31
  · exact prime_3
  · exact prime_47
  · exact prime_11
  · exact prime_3
  · exact prime_31
  · exact prime_6211
  · exact prime_3
  · exact prime_11
  · exact prime_11
  · exact prime_3
  · exact prime_1987
  · exact prime_2423
  · exact prime_3
  · exact prime_587
  · exact prime_31
  · exact prime_3
  · exact prime_67
  · exact prime_11
  · exact prime_3
  · exact prime_31
  · exact prime_1871
  · exact prime_3
  · exact prime_7
  · exact prime_5903
  · exact prime_43
  · exact prime_7
  · exact prime_7411
  · exact prime_947
  · exact prime_7
  · exact prime_5471
  · exact prime_2879
  · exact prime_7
  · exact prime_1483
  · exact prime_23
  · exact prime_7
  · exact prime_1523
  · exact prime_5419
  · exact prime_7
  · exact prime_43
  · exact prime_23
  · exact prime_127
  · exact prime_4027
  · exact prime_1811
  · exact prime_7
  · exact prime_23
  · exact prime_43
  · exact prime_7
  · exact prime_47
  · exact prime_151
  · exact prime_7
  · exact prime_23
  · exact prime_607
  · exact prime_7
  · exact prime_10067
  · exact prime_127
  · exact prime_7
  · exact prime_2791
  · exact prime_5419
  · exact prime_7
  · exact prime_43
  · exact prime_139
  · exact prime_127
  · exact prime_3
  · exact prime_10607
  · exact prime_5147
  · exact prime_3
  · exact prime_11
  · exact prime_23
  · exact prime_3
  · exact prime_1931
  · exact prime_7103
  · exact prime_3
  · exact prime_127
  · exact prime_6619
  · exact prime_3
  · exact prime_9463
  · exact prime_11
  · exact prime_3
  · exact prime_23
  · exact prime_127
  · exact prime_3
  · exact prime_11
  · cases h_false

lemma blocking_prime_by_idx_28_prime (idx : ℕ) : Nat.Prime (blocking_prime_by_idx_28 idx) :=
  prime_of_mem_blocking_primes_28 (getD_mem blocking_primes_28 (idx - 2800) 3)

lemma mod4_of_mem_blocking_primes_28 {p : ℕ} (h : p ∈ 3 :: blocking_primes_28) : p % 4 = 3 := by
  unfold blocking_primes_28 at h
  simp only [List.mem_cons] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | h_false
  · exact mod4_3
  · exact mod4_3
  · exact mod4_11
  · exact mod4_31
  · exact mod4_3
  · exact mod4_1087
  · exact mod4_11
  · exact mod4_3
  · exact mod4_31
  · exact mod4_6703
  · exact mod4_3
  · exact mod4_11
  · exact mod4_11
  · exact mod4_3
  · exact mod4_3079
  · exact mod4_6247
  · exact mod4_3
  · exact mod4_11
  · exact mod4_31
  · exact mod4_3
  · exact mod4_47
  · exact mod4_11
  · exact mod4_3
  · exact mod4_31
  · exact mod4_6211
  · exact mod4_3
  · exact mod4_11
  · exact mod4_11
  · exact mod4_3
  · exact mod4_1987
  · exact mod4_2423
  · exact mod4_3
  · exact mod4_587
  · exact mod4_31
  · exact mod4_3
  · exact mod4_67
  · exact mod4_11
  · exact mod4_3
  · exact mod4_31
  · exact mod4_1871
  · exact mod4_3
  · exact mod4_7
  · exact mod4_5903
  · exact mod4_43
  · exact mod4_7
  · exact mod4_7411
  · exact mod4_947
  · exact mod4_7
  · exact mod4_5471
  · exact mod4_2879
  · exact mod4_7
  · exact mod4_1483
  · exact mod4_23
  · exact mod4_7
  · exact mod4_1523
  · exact mod4_5419
  · exact mod4_7
  · exact mod4_43
  · exact mod4_23
  · exact mod4_127
  · exact mod4_4027
  · exact mod4_1811
  · exact mod4_7
  · exact mod4_23
  · exact mod4_43
  · exact mod4_7
  · exact mod4_47
  · exact mod4_151
  · exact mod4_7
  · exact mod4_23
  · exact mod4_607
  · exact mod4_7
  · exact mod4_10067
  · exact mod4_127
  · exact mod4_7
  · exact mod4_2791
  · exact mod4_5419
  · exact mod4_7
  · exact mod4_43
  · exact mod4_139
  · exact mod4_127
  · exact mod4_3
  · exact mod4_10607
  · exact mod4_5147
  · exact mod4_3
  · exact mod4_11
  · exact mod4_23
  · exact mod4_3
  · exact mod4_1931
  · exact mod4_7103
  · exact mod4_3
  · exact mod4_127
  · exact mod4_6619
  · exact mod4_3
  · exact mod4_9463
  · exact mod4_11
  · exact mod4_3
  · exact mod4_23
  · exact mod4_127
  · exact mod4_3
  · exact mod4_11
  · cases h_false

lemma blocking_prime_by_idx_28_3mod4 (idx : ℕ) : blocking_prime_by_idx_28 idx % 4 = 3 :=
  mod4_of_mem_blocking_primes_28 (getD_mem blocking_primes_28 (idx - 2800) 3)

def blocking_primes_29 : List ℕ := [1879, 3, 71, 6619, 3, 1747, 179, 3, 6719, 11, 3, 127, 67, 3, 5431, 3191, 3, 3011, 23, 3, 3, 19, 6323, 3, 2267, 79, 3, 11863, 3119, 3, 19, 2707, 3, 1283, 10139, 3, 6983, 4759, 3, 19, 4051, 3, 131, 2411, 3, 6823, 9127, 3, 19, 1571, 3, 7211, 83, 3, 179, 10111, 3, 19, 5443, 3, 7, 16831, 17471, 7, 8999, 5791, 7, 8363, 31, 7, 223, 2179, 7, 31, 1039, 10243, 83, 5503, 7, 15679, 271, 7, 1399, 31, 7, 719, 1663, 7, 31, 1307, 7, 12203, 2207, 7, 5051, 1571, 739, 3499, 31, 7]
def blocking_prime_by_idx_29 (idx : ℕ) : ℕ := blocking_primes_29.getD (idx - 2900) 3

lemma prime_of_mem_blocking_primes_29 {p : ℕ} (h : p ∈ 3 :: blocking_primes_29) : Nat.Prime p := by
  unfold blocking_primes_29 at h
  simp only [List.mem_cons] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | h_false
  · exact prime_3
  · exact prime_1879
  · exact prime_3
  · exact prime_71
  · exact prime_6619
  · exact prime_3
  · exact prime_1747
  · exact prime_179
  · exact prime_3
  · exact prime_6719
  · exact prime_11
  · exact prime_3
  · exact prime_127
  · exact prime_67
  · exact prime_3
  · exact prime_5431
  · exact prime_3191
  · exact prime_3
  · exact prime_3011
  · exact prime_23
  · exact prime_3
  · exact prime_3
  · exact prime_19
  · exact prime_6323
  · exact prime_3
  · exact prime_2267
  · exact prime_79
  · exact prime_3
  · exact prime_11863
  · exact prime_3119
  · exact prime_3
  · exact prime_19
  · exact prime_2707
  · exact prime_3
  · exact prime_1283
  · exact prime_10139
  · exact prime_3
  · exact prime_6983
  · exact prime_4759
  · exact prime_3
  · exact prime_19
  · exact prime_4051
  · exact prime_3
  · exact prime_131
  · exact prime_2411
  · exact prime_3
  · exact prime_6823
  · exact prime_9127
  · exact prime_3
  · exact prime_19
  · exact prime_1571
  · exact prime_3
  · exact prime_7211
  · exact prime_83
  · exact prime_3
  · exact prime_179
  · exact prime_10111
  · exact prime_3
  · exact prime_19
  · exact prime_5443
  · exact prime_3
  · exact prime_7
  · exact prime_16831
  · exact prime_17471
  · exact prime_7
  · exact prime_8999
  · exact prime_5791
  · exact prime_7
  · exact prime_8363
  · exact prime_31
  · exact prime_7
  · exact prime_223
  · exact prime_2179
  · exact prime_7
  · exact prime_31
  · exact prime_1039
  · exact prime_10243
  · exact prime_83
  · exact prime_5503
  · exact prime_7
  · exact prime_15679
  · exact prime_271
  · exact prime_7
  · exact prime_1399
  · exact prime_31
  · exact prime_7
  · exact prime_719
  · exact prime_1663
  · exact prime_7
  · exact prime_31
  · exact prime_1307
  · exact prime_7
  · exact prime_12203
  · exact prime_2207
  · exact prime_7
  · exact prime_5051
  · exact prime_1571
  · exact prime_739
  · exact prime_3499
  · exact prime_31
  · exact prime_7
  · cases h_false

lemma blocking_prime_by_idx_29_prime (idx : ℕ) : Nat.Prime (blocking_prime_by_idx_29 idx) :=
  prime_of_mem_blocking_primes_29 (getD_mem blocking_primes_29 (idx - 2900) 3)

lemma mod4_of_mem_blocking_primes_29 {p : ℕ} (h : p ∈ 3 :: blocking_primes_29) : p % 4 = 3 := by
  unfold blocking_primes_29 at h
  simp only [List.mem_cons] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | h_false
  · exact mod4_3
  · exact mod4_1879
  · exact mod4_3
  · exact mod4_71
  · exact mod4_6619
  · exact mod4_3
  · exact mod4_1747
  · exact mod4_179
  · exact mod4_3
  · exact mod4_6719
  · exact mod4_11
  · exact mod4_3
  · exact mod4_127
  · exact mod4_67
  · exact mod4_3
  · exact mod4_5431
  · exact mod4_3191
  · exact mod4_3
  · exact mod4_3011
  · exact mod4_23
  · exact mod4_3
  · exact mod4_3
  · exact mod4_19
  · exact mod4_6323
  · exact mod4_3
  · exact mod4_2267
  · exact mod4_79
  · exact mod4_3
  · exact mod4_11863
  · exact mod4_3119
  · exact mod4_3
  · exact mod4_19
  · exact mod4_2707
  · exact mod4_3
  · exact mod4_1283
  · exact mod4_10139
  · exact mod4_3
  · exact mod4_6983
  · exact mod4_4759
  · exact mod4_3
  · exact mod4_19
  · exact mod4_4051
  · exact mod4_3
  · exact mod4_131
  · exact mod4_2411
  · exact mod4_3
  · exact mod4_6823
  · exact mod4_9127
  · exact mod4_3
  · exact mod4_19
  · exact mod4_1571
  · exact mod4_3
  · exact mod4_7211
  · exact mod4_83
  · exact mod4_3
  · exact mod4_179
  · exact mod4_10111
  · exact mod4_3
  · exact mod4_19
  · exact mod4_5443
  · exact mod4_3
  · exact mod4_7
  · exact mod4_16831
  · exact mod4_17471
  · exact mod4_7
  · exact mod4_8999
  · exact mod4_5791
  · exact mod4_7
  · exact mod4_8363
  · exact mod4_31
  · exact mod4_7
  · exact mod4_223
  · exact mod4_2179
  · exact mod4_7
  · exact mod4_31
  · exact mod4_1039
  · exact mod4_10243
  · exact mod4_83
  · exact mod4_5503
  · exact mod4_7
  · exact mod4_15679
  · exact mod4_271
  · exact mod4_7
  · exact mod4_1399
  · exact mod4_31
  · exact mod4_7
  · exact mod4_719
  · exact mod4_1663
  · exact mod4_7
  · exact mod4_31
  · exact mod4_1307
  · exact mod4_7
  · exact mod4_12203
  · exact mod4_2207
  · exact mod4_7
  · exact mod4_5051
  · exact mod4_1571
  · exact mod4_739
  · exact mod4_3499
  · exact mod4_31
  · exact mod4_7
  · cases h_false

lemma blocking_prime_by_idx_29_3mod4 (idx : ℕ) : blocking_prime_by_idx_29 idx % 4 = 3 :=
  mod4_of_mem_blocking_primes_29 (getD_mem blocking_primes_29 (idx - 2900) 3)

def blocking_primes_30 : List ℕ := [3, 11, 31, 3, 107, 11, 3, 31, 19, 3, 11, 11, 3, 13399, 859, 3, 11, 19, 3, 43, 11, 3, 31, 83, 3, 11, 11, 3, 383, 2731, 3, 11, 31, 3, 2543, 19, 3, 31, 3547, 3, 3, 331, 167, 3, 6451, 8423, 3, 5927, 3307, 3, 179, 5519, 3, 683, 2423, 3, 331, 359, 3, 283, 9391, 3, 103, 6959, 3, 9887, 8539, 3, 179, 223, 3, 331, 17519, 3, 167, 683, 3, 3119, 4679, 3, 7, 8167, 3163, 7, 11, 14563, 7, 8599, 2791, 7, 3023, 7919, 10079, 15331, 11, 7, 1367, 10267, 7, 11]
def blocking_prime_by_idx_30 (idx : ℕ) : ℕ := blocking_primes_30.getD (idx - 3000) 3

lemma prime_of_mem_blocking_primes_30 {p : ℕ} (h : p ∈ 3 :: blocking_primes_30) : Nat.Prime p := by
  unfold blocking_primes_30 at h
  simp only [List.mem_cons] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | h_false
  · exact prime_3
  · exact prime_3
  · exact prime_11
  · exact prime_31
  · exact prime_3
  · exact prime_107
  · exact prime_11
  · exact prime_3
  · exact prime_31
  · exact prime_19
  · exact prime_3
  · exact prime_11
  · exact prime_11
  · exact prime_3
  · exact prime_13399
  · exact prime_859
  · exact prime_3
  · exact prime_11
  · exact prime_19
  · exact prime_3
  · exact prime_43
  · exact prime_11
  · exact prime_3
  · exact prime_31
  · exact prime_83
  · exact prime_3
  · exact prime_11
  · exact prime_11
  · exact prime_3
  · exact prime_383
  · exact prime_2731
  · exact prime_3
  · exact prime_11
  · exact prime_31
  · exact prime_3
  · exact prime_2543
  · exact prime_19
  · exact prime_3
  · exact prime_31
  · exact prime_3547
  · exact prime_3
  · exact prime_3
  · exact prime_331
  · exact prime_167
  · exact prime_3
  · exact prime_6451
  · exact prime_8423
  · exact prime_3
  · exact prime_5927
  · exact prime_3307
  · exact prime_3
  · exact prime_179
  · exact prime_5519
  · exact prime_3
  · exact prime_683
  · exact prime_2423
  · exact prime_3
  · exact prime_331
  · exact prime_359
  · exact prime_3
  · exact prime_283
  · exact prime_9391
  · exact prime_3
  · exact prime_103
  · exact prime_6959
  · exact prime_3
  · exact prime_9887
  · exact prime_8539
  · exact prime_3
  · exact prime_179
  · exact prime_223
  · exact prime_3
  · exact prime_331
  · exact prime_17519
  · exact prime_3
  · exact prime_167
  · exact prime_683
  · exact prime_3
  · exact prime_3119
  · exact prime_4679
  · exact prime_3
  · exact prime_7
  · exact prime_8167
  · exact prime_3163
  · exact prime_7
  · exact prime_11
  · exact prime_14563
  · exact prime_7
  · exact prime_8599
  · exact prime_2791
  · exact prime_7
  · exact prime_3023
  · exact prime_7919
  · exact prime_10079
  · exact prime_15331
  · exact prime_11
  · exact prime_7
  · exact prime_1367
  · exact prime_10267
  · exact prime_7
  · exact prime_11
  · cases h_false

lemma blocking_prime_by_idx_30_prime (idx : ℕ) : Nat.Prime (blocking_prime_by_idx_30 idx) :=
  prime_of_mem_blocking_primes_30 (getD_mem blocking_primes_30 (idx - 3000) 3)

lemma mod4_of_mem_blocking_primes_30 {p : ℕ} (h : p ∈ 3 :: blocking_primes_30) : p % 4 = 3 := by
  unfold blocking_primes_30 at h
  simp only [List.mem_cons] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | h_false
  · exact mod4_3
  · exact mod4_3
  · exact mod4_11
  · exact mod4_31
  · exact mod4_3
  · exact mod4_107
  · exact mod4_11
  · exact mod4_3
  · exact mod4_31
  · exact mod4_19
  · exact mod4_3
  · exact mod4_11
  · exact mod4_11
  · exact mod4_3
  · exact mod4_13399
  · exact mod4_859
  · exact mod4_3
  · exact mod4_11
  · exact mod4_19
  · exact mod4_3
  · exact mod4_43
  · exact mod4_11
  · exact mod4_3
  · exact mod4_31
  · exact mod4_83
  · exact mod4_3
  · exact mod4_11
  · exact mod4_11
  · exact mod4_3
  · exact mod4_383
  · exact mod4_2731
  · exact mod4_3
  · exact mod4_11
  · exact mod4_31
  · exact mod4_3
  · exact mod4_2543
  · exact mod4_19
  · exact mod4_3
  · exact mod4_31
  · exact mod4_3547
  · exact mod4_3
  · exact mod4_3
  · exact mod4_331
  · exact mod4_167
  · exact mod4_3
  · exact mod4_6451
  · exact mod4_8423
  · exact mod4_3
  · exact mod4_5927
  · exact mod4_3307
  · exact mod4_3
  · exact mod4_179
  · exact mod4_5519
  · exact mod4_3
  · exact mod4_683
  · exact mod4_2423
  · exact mod4_3
  · exact mod4_331
  · exact mod4_359
  · exact mod4_3
  · exact mod4_283
  · exact mod4_9391
  · exact mod4_3
  · exact mod4_103
  · exact mod4_6959
  · exact mod4_3
  · exact mod4_9887
  · exact mod4_8539
  · exact mod4_3
  · exact mod4_179
  · exact mod4_223
  · exact mod4_3
  · exact mod4_331
  · exact mod4_17519
  · exact mod4_3
  · exact mod4_167
  · exact mod4_683
  · exact mod4_3
  · exact mod4_3119
  · exact mod4_4679
  · exact mod4_3
  · exact mod4_7
  · exact mod4_8167
  · exact mod4_3163
  · exact mod4_7
  · exact mod4_11
  · exact mod4_14563
  · exact mod4_7
  · exact mod4_8599
  · exact mod4_2791
  · exact mod4_7
  · exact mod4_3023
  · exact mod4_7919
  · exact mod4_10079
  · exact mod4_15331
  · exact mod4_11
  · exact mod4_7
  · exact mod4_1367
  · exact mod4_10267
  · exact mod4_7
  · exact mod4_11
  · cases h_false

lemma blocking_prime_by_idx_30_3mod4 (idx : ℕ) : blocking_prime_by_idx_30 idx % 4 = 3 :=
  mod4_of_mem_blocking_primes_30 (getD_mem blocking_primes_30 (idx - 3000) 3)

def blocking_primes_31 : List ℕ := [107, 7, 67, 263, 7, 4363, 419, 7, 12119, 11, 7, 10163, 17807, 71, 11, 71, 7, 3923, 271, 7, 3, 11119, 43, 3, 127, 607, 3, 107, 5927, 3, 4111, 127, 3, 4799, 331, 3, 43, 8731, 3, 151, 2011, 3, 4943, 43, 3, 127, 2503, 3, 5419, 71, 3, 83, 127, 3, 151, 4679, 3, 43, 8171, 3, 3, 23, 1091, 3, 223, 6863, 3, 59, 31, 3, 127, 307, 3, 31, 6779, 3, 467, 127, 3, 239, 8191, 3, 16699, 31, 3, 8291, 103, 3, 31, 2687, 3, 127, 5179, 3, 23, 3583, 3, 3907, 31, 3]
def blocking_prime_by_idx_31 (idx : ℕ) : ℕ := blocking_primes_31.getD (idx - 3100) 3

lemma prime_of_mem_blocking_primes_31 {p : ℕ} (h : p ∈ 3 :: blocking_primes_31) : Nat.Prime p := by
  unfold blocking_primes_31 at h
  simp only [List.mem_cons] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | h_false
  · exact prime_3
  · exact prime_107
  · exact prime_7
  · exact prime_67
  · exact prime_263
  · exact prime_7
  · exact prime_4363
  · exact prime_419
  · exact prime_7
  · exact prime_12119
  · exact prime_11
  · exact prime_7
  · exact prime_10163
  · exact prime_17807
  · exact prime_71
  · exact prime_11
  · exact prime_71
  · exact prime_7
  · exact prime_3923
  · exact prime_271
  · exact prime_7
  · exact prime_3
  · exact prime_11119
  · exact prime_43
  · exact prime_3
  · exact prime_127
  · exact prime_607
  · exact prime_3
  · exact prime_107
  · exact prime_5927
  · exact prime_3
  · exact prime_4111
  · exact prime_127
  · exact prime_3
  · exact prime_4799
  · exact prime_331
  · exact prime_3
  · exact prime_43
  · exact prime_8731
  · exact prime_3
  · exact prime_151
  · exact prime_2011
  · exact prime_3
  · exact prime_4943
  · exact prime_43
  · exact prime_3
  · exact prime_127
  · exact prime_2503
  · exact prime_3
  · exact prime_5419
  · exact prime_71
  · exact prime_3
  · exact prime_83
  · exact prime_127
  · exact prime_3
  · exact prime_151
  · exact prime_4679
  · exact prime_3
  · exact prime_43
  · exact prime_8171
  · exact prime_3
  · exact prime_3
  · exact prime_23
  · exact prime_1091
  · exact prime_3
  · exact prime_223
  · exact prime_6863
  · exact prime_3
  · exact prime_59
  · exact prime_31
  · exact prime_3
  · exact prime_127
  · exact prime_307
  · exact prime_3
  · exact prime_31
  · exact prime_6779
  · exact prime_3
  · exact prime_467
  · exact prime_127
  · exact prime_3
  · exact prime_239
  · exact prime_8191
  · exact prime_3
  · exact prime_16699
  · exact prime_31
  · exact prime_3
  · exact prime_8291
  · exact prime_103
  · exact prime_3
  · exact prime_31
  · exact prime_2687
  · exact prime_3
  · exact prime_127
  · exact prime_5179
  · exact prime_3
  · exact prime_23
  · exact prime_3583
  · exact prime_3
  · exact prime_3907
  · exact prime_31
  · exact prime_3
  · cases h_false

lemma blocking_prime_by_idx_31_prime (idx : ℕ) : Nat.Prime (blocking_prime_by_idx_31 idx) :=
  prime_of_mem_blocking_primes_31 (getD_mem blocking_primes_31 (idx - 3100) 3)

lemma mod4_of_mem_blocking_primes_31 {p : ℕ} (h : p ∈ 3 :: blocking_primes_31) : p % 4 = 3 := by
  unfold blocking_primes_31 at h
  simp only [List.mem_cons] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | h_false
  · exact mod4_3
  · exact mod4_107
  · exact mod4_7
  · exact mod4_67
  · exact mod4_263
  · exact mod4_7
  · exact mod4_4363
  · exact mod4_419
  · exact mod4_7
  · exact mod4_12119
  · exact mod4_11
  · exact mod4_7
  · exact mod4_10163
  · exact mod4_17807
  · exact mod4_71
  · exact mod4_11
  · exact mod4_71
  · exact mod4_7
  · exact mod4_3923
  · exact mod4_271
  · exact mod4_7
  · exact mod4_3
  · exact mod4_11119
  · exact mod4_43
  · exact mod4_3
  · exact mod4_127
  · exact mod4_607
  · exact mod4_3
  · exact mod4_107
  · exact mod4_5927
  · exact mod4_3
  · exact mod4_4111
  · exact mod4_127
  · exact mod4_3
  · exact mod4_4799
  · exact mod4_331
  · exact mod4_3
  · exact mod4_43
  · exact mod4_8731
  · exact mod4_3
  · exact mod4_151
  · exact mod4_2011
  · exact mod4_3
  · exact mod4_4943
  · exact mod4_43
  · exact mod4_3
  · exact mod4_127
  · exact mod4_2503
  · exact mod4_3
  · exact mod4_5419
  · exact mod4_71
  · exact mod4_3
  · exact mod4_83
  · exact mod4_127
  · exact mod4_3
  · exact mod4_151
  · exact mod4_4679
  · exact mod4_3
  · exact mod4_43
  · exact mod4_8171
  · exact mod4_3
  · exact mod4_3
  · exact mod4_23
  · exact mod4_1091
  · exact mod4_3
  · exact mod4_223
  · exact mod4_6863
  · exact mod4_3
  · exact mod4_59
  · exact mod4_31
  · exact mod4_3
  · exact mod4_127
  · exact mod4_307
  · exact mod4_3
  · exact mod4_31
  · exact mod4_6779
  · exact mod4_3
  · exact mod4_467
  · exact mod4_127
  · exact mod4_3
  · exact mod4_239
  · exact mod4_8191
  · exact mod4_3
  · exact mod4_16699
  · exact mod4_31
  · exact mod4_3
  · exact mod4_8291
  · exact mod4_103
  · exact mod4_3
  · exact mod4_31
  · exact mod4_2687
  · exact mod4_3
  · exact mod4_127
  · exact mod4_5179
  · exact mod4_3
  · exact mod4_23
  · exact mod4_3583
  · exact mod4_3
  · exact mod4_3907
  · exact mod4_31
  · exact mod4_3
  · cases h_false

lemma blocking_prime_by_idx_31_3mod4 (idx : ℕ) : blocking_prime_by_idx_31 idx % 4 = 3 :=
  mod4_of_mem_blocking_primes_31 (getD_mem blocking_primes_31 (idx - 3100) 3)

def blocking_primes_32 : List ℕ := [7, 11, 31, 7, 571, 11, 7, 31, 79, 683, 11, 11, 7, 107, 2411, 7, 11, 31, 7, 8191, 11, 7, 31, 11519, 7, 11, 11, 7, 47, 5099, 31, 11, 31, 7, 919, 11, 7, 31, 3631, 7, 3, 1759, 5003, 3, 251, 9631, 3, 1999, 431, 3, 23, 179, 3, 71, 2111, 3, 2579, 8647, 3, 7703, 59, 3, 7723, 2731, 3, 2551, 6007, 3, 7699, 47, 3, 1579, 23, 3, 8231, 3931, 3, 7759, 307, 3, 3, 19, 2503, 3, 11, 43, 3, 4519, 7883, 3, 5827, 23, 3, 3691, 367, 3, 307, 23, 3, 11]
def blocking_prime_by_idx_32 (idx : ℕ) : ℕ := blocking_primes_32.getD (idx - 3200) 3

lemma prime_of_mem_blocking_primes_32 {p : ℕ} (h : p ∈ 3 :: blocking_primes_32) : Nat.Prime p := by
  unfold blocking_primes_32 at h
  simp only [List.mem_cons] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | h_false
  · exact prime_3
  · exact prime_7
  · exact prime_11
  · exact prime_31
  · exact prime_7
  · exact prime_571
  · exact prime_11
  · exact prime_7
  · exact prime_31
  · exact prime_79
  · exact prime_683
  · exact prime_11
  · exact prime_11
  · exact prime_7
  · exact prime_107
  · exact prime_2411
  · exact prime_7
  · exact prime_11
  · exact prime_31
  · exact prime_7
  · exact prime_8191
  · exact prime_11
  · exact prime_7
  · exact prime_31
  · exact prime_11519
  · exact prime_7
  · exact prime_11
  · exact prime_11
  · exact prime_7
  · exact prime_47
  · exact prime_5099
  · exact prime_31
  · exact prime_11
  · exact prime_31
  · exact prime_7
  · exact prime_919
  · exact prime_11
  · exact prime_7
  · exact prime_31
  · exact prime_3631
  · exact prime_7
  · exact prime_3
  · exact prime_1759
  · exact prime_5003
  · exact prime_3
  · exact prime_251
  · exact prime_9631
  · exact prime_3
  · exact prime_1999
  · exact prime_431
  · exact prime_3
  · exact prime_23
  · exact prime_179
  · exact prime_3
  · exact prime_71
  · exact prime_2111
  · exact prime_3
  · exact prime_2579
  · exact prime_8647
  · exact prime_3
  · exact prime_7703
  · exact prime_59
  · exact prime_3
  · exact prime_7723
  · exact prime_2731
  · exact prime_3
  · exact prime_2551
  · exact prime_6007
  · exact prime_3
  · exact prime_7699
  · exact prime_47
  · exact prime_3
  · exact prime_1579
  · exact prime_23
  · exact prime_3
  · exact prime_8231
  · exact prime_3931
  · exact prime_3
  · exact prime_7759
  · exact prime_307
  · exact prime_3
  · exact prime_3
  · exact prime_19
  · exact prime_2503
  · exact prime_3
  · exact prime_11
  · exact prime_43
  · exact prime_3
  · exact prime_4519
  · exact prime_7883
  · exact prime_3
  · exact prime_5827
  · exact prime_23
  · exact prime_3
  · exact prime_3691
  · exact prime_367
  · exact prime_3
  · exact prime_307
  · exact prime_23
  · exact prime_3
  · exact prime_11
  · cases h_false

lemma blocking_prime_by_idx_32_prime (idx : ℕ) : Nat.Prime (blocking_prime_by_idx_32 idx) :=
  prime_of_mem_blocking_primes_32 (getD_mem blocking_primes_32 (idx - 3200) 3)

lemma mod4_of_mem_blocking_primes_32 {p : ℕ} (h : p ∈ 3 :: blocking_primes_32) : p % 4 = 3 := by
  unfold blocking_primes_32 at h
  simp only [List.mem_cons] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | h_false
  · exact mod4_3
  · exact mod4_7
  · exact mod4_11
  · exact mod4_31
  · exact mod4_7
  · exact mod4_571
  · exact mod4_11
  · exact mod4_7
  · exact mod4_31
  · exact mod4_79
  · exact mod4_683
  · exact mod4_11
  · exact mod4_11
  · exact mod4_7
  · exact mod4_107
  · exact mod4_2411
  · exact mod4_7
  · exact mod4_11
  · exact mod4_31
  · exact mod4_7
  · exact mod4_8191
  · exact mod4_11
  · exact mod4_7
  · exact mod4_31
  · exact mod4_11519
  · exact mod4_7
  · exact mod4_11
  · exact mod4_11
  · exact mod4_7
  · exact mod4_47
  · exact mod4_5099
  · exact mod4_31
  · exact mod4_11
  · exact mod4_31
  · exact mod4_7
  · exact mod4_919
  · exact mod4_11
  · exact mod4_7
  · exact mod4_31
  · exact mod4_3631
  · exact mod4_7
  · exact mod4_3
  · exact mod4_1759
  · exact mod4_5003
  · exact mod4_3
  · exact mod4_251
  · exact mod4_9631
  · exact mod4_3
  · exact mod4_1999
  · exact mod4_431
  · exact mod4_3
  · exact mod4_23
  · exact mod4_179
  · exact mod4_3
  · exact mod4_71
  · exact mod4_2111
  · exact mod4_3
  · exact mod4_2579
  · exact mod4_8647
  · exact mod4_3
  · exact mod4_7703
  · exact mod4_59
  · exact mod4_3
  · exact mod4_7723
  · exact mod4_2731
  · exact mod4_3
  · exact mod4_2551
  · exact mod4_6007
  · exact mod4_3
  · exact mod4_7699
  · exact mod4_47
  · exact mod4_3
  · exact mod4_1579
  · exact mod4_23
  · exact mod4_3
  · exact mod4_8231
  · exact mod4_3931
  · exact mod4_3
  · exact mod4_7759
  · exact mod4_307
  · exact mod4_3
  · exact mod4_3
  · exact mod4_19
  · exact mod4_2503
  · exact mod4_3
  · exact mod4_11
  · exact mod4_43
  · exact mod4_3
  · exact mod4_4519
  · exact mod4_7883
  · exact mod4_3
  · exact mod4_5827
  · exact mod4_23
  · exact mod4_3
  · exact mod4_3691
  · exact mod4_367
  · exact mod4_3
  · exact mod4_307
  · exact mod4_23
  · exact mod4_3
  · exact mod4_11
  · cases h_false

lemma blocking_prime_by_idx_32_3mod4 (idx : ℕ) : blocking_prime_by_idx_32 idx % 4 = 3 :=
  mod4_of_mem_blocking_primes_32 (getD_mem blocking_primes_32 (idx - 3200) 3)

def blocking_primes_33 : List ℕ := [12203, 3, 5743, 419, 3, 347, 43, 3, 19, 11, 3, 6863, 2767, 3, 11, 4019, 3, 19, 8923, 3, 7, 79, 971, 7, 3407, 23, 5087, 12163, 83, 7, 1559, 1847, 7, 7219, 179, 7, 23, 1583, 7, 4271, 67, 7, 1327, 71, 7, 2467, 5807, 23, 4003, 59, 7, 4787, 691, 7, 59, 1231, 7, 2531, 23, 7, 3, 8111, 9203, 3, 5683, 179, 3, 4903, 19, 3, 4451, 6803, 3, 31, 739, 3, 6311, 19, 3, 6911, 1699, 3, 263, 31, 3, 8363, 19, 3, 31, 1171, 3, 8243, 1439, 3, 227, 19, 3, 8039, 31, 3]
def blocking_prime_by_idx_33 (idx : ℕ) : ℕ := blocking_primes_33.getD (idx - 3300) 3

lemma prime_of_mem_blocking_primes_33 {p : ℕ} (h : p ∈ 3 :: blocking_primes_33) : Nat.Prime p := by
  unfold blocking_primes_33 at h
  simp only [List.mem_cons] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | h_false
  · exact prime_3
  · exact prime_12203
  · exact prime_3
  · exact prime_5743
  · exact prime_419
  · exact prime_3
  · exact prime_347
  · exact prime_43
  · exact prime_3
  · exact prime_19
  · exact prime_11
  · exact prime_3
  · exact prime_6863
  · exact prime_2767
  · exact prime_3
  · exact prime_11
  · exact prime_4019
  · exact prime_3
  · exact prime_19
  · exact prime_8923
  · exact prime_3
  · exact prime_7
  · exact prime_79
  · exact prime_971
  · exact prime_7
  · exact prime_3407
  · exact prime_23
  · exact prime_5087
  · exact prime_12163
  · exact prime_83
  · exact prime_7
  · exact prime_1559
  · exact prime_1847
  · exact prime_7
  · exact prime_7219
  · exact prime_179
  · exact prime_7
  · exact prime_23
  · exact prime_1583
  · exact prime_7
  · exact prime_4271
  · exact prime_67
  · exact prime_7
  · exact prime_1327
  · exact prime_71
  · exact prime_7
  · exact prime_2467
  · exact prime_5807
  · exact prime_23
  · exact prime_4003
  · exact prime_59
  · exact prime_7
  · exact prime_4787
  · exact prime_691
  · exact prime_7
  · exact prime_59
  · exact prime_1231
  · exact prime_7
  · exact prime_2531
  · exact prime_23
  · exact prime_7
  · exact prime_3
  · exact prime_8111
  · exact prime_9203
  · exact prime_3
  · exact prime_5683
  · exact prime_179
  · exact prime_3
  · exact prime_4903
  · exact prime_19
  · exact prime_3
  · exact prime_4451
  · exact prime_6803
  · exact prime_3
  · exact prime_31
  · exact prime_739
  · exact prime_3
  · exact prime_6311
  · exact prime_19
  · exact prime_3
  · exact prime_6911
  · exact prime_1699
  · exact prime_3
  · exact prime_263
  · exact prime_31
  · exact prime_3
  · exact prime_8363
  · exact prime_19
  · exact prime_3
  · exact prime_31
  · exact prime_1171
  · exact prime_3
  · exact prime_8243
  · exact prime_1439
  · exact prime_3
  · exact prime_227
  · exact prime_19
  · exact prime_3
  · exact prime_8039
  · exact prime_31
  · exact prime_3
  · cases h_false

lemma blocking_prime_by_idx_33_prime (idx : ℕ) : Nat.Prime (blocking_prime_by_idx_33 idx) :=
  prime_of_mem_blocking_primes_33 (getD_mem blocking_primes_33 (idx - 3300) 3)

lemma mod4_of_mem_blocking_primes_33 {p : ℕ} (h : p ∈ 3 :: blocking_primes_33) : p % 4 = 3 := by
  unfold blocking_primes_33 at h
  simp only [List.mem_cons] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | h_false
  · exact mod4_3
  · exact mod4_12203
  · exact mod4_3
  · exact mod4_5743
  · exact mod4_419
  · exact mod4_3
  · exact mod4_347
  · exact mod4_43
  · exact mod4_3
  · exact mod4_19
  · exact mod4_11
  · exact mod4_3
  · exact mod4_6863
  · exact mod4_2767
  · exact mod4_3
  · exact mod4_11
  · exact mod4_4019
  · exact mod4_3
  · exact mod4_19
  · exact mod4_8923
  · exact mod4_3
  · exact mod4_7
  · exact mod4_79
  · exact mod4_971
  · exact mod4_7
  · exact mod4_3407
  · exact mod4_23
  · exact mod4_5087
  · exact mod4_12163
  · exact mod4_83
  · exact mod4_7
  · exact mod4_1559
  · exact mod4_1847
  · exact mod4_7
  · exact mod4_7219
  · exact mod4_179
  · exact mod4_7
  · exact mod4_23
  · exact mod4_1583
  · exact mod4_7
  · exact mod4_4271
  · exact mod4_67
  · exact mod4_7
  · exact mod4_1327
  · exact mod4_71
  · exact mod4_7
  · exact mod4_2467
  · exact mod4_5807
  · exact mod4_23
  · exact mod4_4003
  · exact mod4_59
  · exact mod4_7
  · exact mod4_4787
  · exact mod4_691
  · exact mod4_7
  · exact mod4_59
  · exact mod4_1231
  · exact mod4_7
  · exact mod4_2531
  · exact mod4_23
  · exact mod4_7
  · exact mod4_3
  · exact mod4_8111
  · exact mod4_9203
  · exact mod4_3
  · exact mod4_5683
  · exact mod4_179
  · exact mod4_3
  · exact mod4_4903
  · exact mod4_19
  · exact mod4_3
  · exact mod4_4451
  · exact mod4_6803
  · exact mod4_3
  · exact mod4_31
  · exact mod4_739
  · exact mod4_3
  · exact mod4_6311
  · exact mod4_19
  · exact mod4_3
  · exact mod4_6911
  · exact mod4_1699
  · exact mod4_3
  · exact mod4_263
  · exact mod4_31
  · exact mod4_3
  · exact mod4_8363
  · exact mod4_19
  · exact mod4_3
  · exact mod4_31
  · exact mod4_1171
  · exact mod4_3
  · exact mod4_8243
  · exact mod4_1439
  · exact mod4_3
  · exact mod4_227
  · exact mod4_19
  · exact mod4_3
  · exact mod4_8039
  · exact mod4_31
  · exact mod4_3
  · cases h_false

lemma blocking_prime_by_idx_33_3mod4 (idx : ℕ) : blocking_prime_by_idx_33 idx % 4 = 3 :=
  mod4_of_mem_blocking_primes_33 (getD_mem blocking_primes_33 (idx - 3300) 3)

def blocking_primes_34 : List ℕ := [3, 11, 31, 3, 47, 11, 3, 31, 59, 3, 11, 11, 3, 2351, 7459, 3, 11, 31, 3, 359, 11, 3, 31, 43, 3, 31, 11, 3, 1867, 3259, 3, 11, 31, 3, 3271, 11, 3, 31, 79, 3, 7, 11047, 18911, 127, 1471, 367, 7, 8783, 859, 7, 79, 151, 7, 907, 5743, 7, 6271, 127, 7, 6607, 11471, 7, 7591, 9719, 127, 751, 151, 7, 2591, 283, 7, 127, 2663, 7, 8707, 2671, 7, 19759, 127, 7, 3, 6883, 683, 3, 167, 5483, 3, 79, 12919, 3, 67, 7283, 3, 683, 11, 3, 107, 11299, 3, 11]
def blocking_prime_by_idx_34 (idx : ℕ) : ℕ := blocking_primes_34.getD (idx - 3400) 3

lemma prime_of_mem_blocking_primes_34 {p : ℕ} (h : p ∈ 3 :: blocking_primes_34) : Nat.Prime p := by
  unfold blocking_primes_34 at h
  simp only [List.mem_cons] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | h_false
  · exact prime_3
  · exact prime_3
  · exact prime_11
  · exact prime_31
  · exact prime_3
  · exact prime_47
  · exact prime_11
  · exact prime_3
  · exact prime_31
  · exact prime_59
  · exact prime_3
  · exact prime_11
  · exact prime_11
  · exact prime_3
  · exact prime_2351
  · exact prime_7459
  · exact prime_3
  · exact prime_11
  · exact prime_31
  · exact prime_3
  · exact prime_359
  · exact prime_11
  · exact prime_3
  · exact prime_31
  · exact prime_43
  · exact prime_3
  · exact prime_31
  · exact prime_11
  · exact prime_3
  · exact prime_1867
  · exact prime_3259
  · exact prime_3
  · exact prime_11
  · exact prime_31
  · exact prime_3
  · exact prime_3271
  · exact prime_11
  · exact prime_3
  · exact prime_31
  · exact prime_79
  · exact prime_3
  · exact prime_7
  · exact prime_11047
  · exact prime_18911
  · exact prime_127
  · exact prime_1471
  · exact prime_367
  · exact prime_7
  · exact prime_8783
  · exact prime_859
  · exact prime_7
  · exact prime_79
  · exact prime_151
  · exact prime_7
  · exact prime_907
  · exact prime_5743
  · exact prime_7
  · exact prime_6271
  · exact prime_127
  · exact prime_7
  · exact prime_6607
  · exact prime_11471
  · exact prime_7
  · exact prime_7591
  · exact prime_9719
  · exact prime_127
  · exact prime_751
  · exact prime_151
  · exact prime_7
  · exact prime_2591
  · exact prime_283
  · exact prime_7
  · exact prime_127
  · exact prime_2663
  · exact prime_7
  · exact prime_8707
  · exact prime_2671
  · exact prime_7
  · exact prime_19759
  · exact prime_127
  · exact prime_7
  · exact prime_3
  · exact prime_6883
  · exact prime_683
  · exact prime_3
  · exact prime_167
  · exact prime_5483
  · exact prime_3
  · exact prime_79
  · exact prime_12919
  · exact prime_3
  · exact prime_67
  · exact prime_7283
  · exact prime_3
  · exact prime_683
  · exact prime_11
  · exact prime_3
  · exact prime_107
  · exact prime_11299
  · exact prime_3
  · exact prime_11
  · cases h_false

lemma blocking_prime_by_idx_34_prime (idx : ℕ) : Nat.Prime (blocking_prime_by_idx_34 idx) :=
  prime_of_mem_blocking_primes_34 (getD_mem blocking_primes_34 (idx - 3400) 3)

lemma mod4_of_mem_blocking_primes_34 {p : ℕ} (h : p ∈ 3 :: blocking_primes_34) : p % 4 = 3 := by
  unfold blocking_primes_34 at h
  simp only [List.mem_cons] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | h_false
  · exact mod4_3
  · exact mod4_3
  · exact mod4_11
  · exact mod4_31
  · exact mod4_3
  · exact mod4_47
  · exact mod4_11
  · exact mod4_3
  · exact mod4_31
  · exact mod4_59
  · exact mod4_3
  · exact mod4_11
  · exact mod4_11
  · exact mod4_3
  · exact mod4_2351
  · exact mod4_7459
  · exact mod4_3
  · exact mod4_11
  · exact mod4_31
  · exact mod4_3
  · exact mod4_359
  · exact mod4_11
  · exact mod4_3
  · exact mod4_31
  · exact mod4_43
  · exact mod4_3
  · exact mod4_31
  · exact mod4_11
  · exact mod4_3
  · exact mod4_1867
  · exact mod4_3259
  · exact mod4_3
  · exact mod4_11
  · exact mod4_31
  · exact mod4_3
  · exact mod4_3271
  · exact mod4_11
  · exact mod4_3
  · exact mod4_31
  · exact mod4_79
  · exact mod4_3
  · exact mod4_7
  · exact mod4_11047
  · exact mod4_18911
  · exact mod4_127
  · exact mod4_1471
  · exact mod4_367
  · exact mod4_7
  · exact mod4_8783
  · exact mod4_859
  · exact mod4_7
  · exact mod4_79
  · exact mod4_151
  · exact mod4_7
  · exact mod4_907
  · exact mod4_5743
  · exact mod4_7
  · exact mod4_6271
  · exact mod4_127
  · exact mod4_7
  · exact mod4_6607
  · exact mod4_11471
  · exact mod4_7
  · exact mod4_7591
  · exact mod4_9719
  · exact mod4_127
  · exact mod4_751
  · exact mod4_151
  · exact mod4_7
  · exact mod4_2591
  · exact mod4_283
  · exact mod4_7
  · exact mod4_127
  · exact mod4_2663
  · exact mod4_7
  · exact mod4_8707
  · exact mod4_2671
  · exact mod4_7
  · exact mod4_19759
  · exact mod4_127
  · exact mod4_7
  · exact mod4_3
  · exact mod4_6883
  · exact mod4_683
  · exact mod4_3
  · exact mod4_167
  · exact mod4_5483
  · exact mod4_3
  · exact mod4_79
  · exact mod4_12919
  · exact mod4_3
  · exact mod4_67
  · exact mod4_7283
  · exact mod4_3
  · exact mod4_683
  · exact mod4_11
  · exact mod4_3
  · exact mod4_107
  · exact mod4_11299
  · exact mod4_3
  · exact mod4_11
  · cases h_false

lemma blocking_prime_by_idx_34_3mod4 (idx : ℕ) : blocking_prime_by_idx_34 idx % 4 = 3 :=
  mod4_of_mem_blocking_primes_34 (getD_mem blocking_primes_34 (idx - 3400) 3)

def blocking_primes_35 : List ℕ := [3191, 3, 311, 1171, 3, 14251, 59, 3, 191, 11, 3, 9227, 2539, 3, 11, 683, 3, 751, 8219, 3, 3, 163, 6691, 3, 1483, 4051, 3, 12379, 5099, 3, 2411, 67, 3, 10463, 10631, 3, 2731, 10271, 3, 4703, 3623, 3, 971, 1607, 3, 8819, 2803, 3, 4127, 383, 3, 271, 8963, 3, 1187, 1723, 3, 9631, 1831, 3, 271, 919, 3499, 7, 1319, 43, 7, 6043, 4787, 7, 547, 167, 7, 31, 1867, 7, 15259, 1723, 7, 43, 9719, 251, 7127, 31, 7, 947, 43, 7, 31, 14251, 7, 8263, 12503, 7, 2251, 5591, 7, 1187, 31, 7]
def blocking_prime_by_idx_35 (idx : ℕ) : ℕ := blocking_primes_35.getD (idx - 3500) 3

lemma prime_of_mem_blocking_primes_35 {p : ℕ} (h : p ∈ 3 :: blocking_primes_35) : Nat.Prime p := by
  unfold blocking_primes_35 at h
  simp only [List.mem_cons] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | h_false
  · exact prime_3
  · exact prime_3191
  · exact prime_3
  · exact prime_311
  · exact prime_1171
  · exact prime_3
  · exact prime_14251
  · exact prime_59
  · exact prime_3
  · exact prime_191
  · exact prime_11
  · exact prime_3
  · exact prime_9227
  · exact prime_2539
  · exact prime_3
  · exact prime_11
  · exact prime_683
  · exact prime_3
  · exact prime_751
  · exact prime_8219
  · exact prime_3
  · exact prime_3
  · exact prime_163
  · exact prime_6691
  · exact prime_3
  · exact prime_1483
  · exact prime_4051
  · exact prime_3
  · exact prime_12379
  · exact prime_5099
  · exact prime_3
  · exact prime_2411
  · exact prime_67
  · exact prime_3
  · exact prime_10463
  · exact prime_10631
  · exact prime_3
  · exact prime_2731
  · exact prime_10271
  · exact prime_3
  · exact prime_4703
  · exact prime_3623
  · exact prime_3
  · exact prime_971
  · exact prime_1607
  · exact prime_3
  · exact prime_8819
  · exact prime_2803
  · exact prime_3
  · exact prime_4127
  · exact prime_383
  · exact prime_3
  · exact prime_271
  · exact prime_8963
  · exact prime_3
  · exact prime_1187
  · exact prime_1723
  · exact prime_3
  · exact prime_9631
  · exact prime_1831
  · exact prime_3
  · exact prime_271
  · exact prime_919
  · exact prime_3499
  · exact prime_7
  · exact prime_1319
  · exact prime_43
  · exact prime_7
  · exact prime_6043
  · exact prime_4787
  · exact prime_7
  · exact prime_547
  · exact prime_167
  · exact prime_7
  · exact prime_31
  · exact prime_1867
  · exact prime_7
  · exact prime_15259
  · exact prime_1723
  · exact prime_7
  · exact prime_43
  · exact prime_9719
  · exact prime_251
  · exact prime_7127
  · exact prime_31
  · exact prime_7
  · exact prime_947
  · exact prime_43
  · exact prime_7
  · exact prime_31
  · exact prime_14251
  · exact prime_7
  · exact prime_8263
  · exact prime_12503
  · exact prime_7
  · exact prime_2251
  · exact prime_5591
  · exact prime_7
  · exact prime_1187
  · exact prime_31
  · exact prime_7
  · cases h_false

lemma blocking_prime_by_idx_35_prime (idx : ℕ) : Nat.Prime (blocking_prime_by_idx_35 idx) :=
  prime_of_mem_blocking_primes_35 (getD_mem blocking_primes_35 (idx - 3500) 3)

lemma mod4_of_mem_blocking_primes_35 {p : ℕ} (h : p ∈ 3 :: blocking_primes_35) : p % 4 = 3 := by
  unfold blocking_primes_35 at h
  simp only [List.mem_cons] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | h_false
  · exact mod4_3
  · exact mod4_3191
  · exact mod4_3
  · exact mod4_311
  · exact mod4_1171
  · exact mod4_3
  · exact mod4_14251
  · exact mod4_59
  · exact mod4_3
  · exact mod4_191
  · exact mod4_11
  · exact mod4_3
  · exact mod4_9227
  · exact mod4_2539
  · exact mod4_3
  · exact mod4_11
  · exact mod4_683
  · exact mod4_3
  · exact mod4_751
  · exact mod4_8219
  · exact mod4_3
  · exact mod4_3
  · exact mod4_163
  · exact mod4_6691
  · exact mod4_3
  · exact mod4_1483
  · exact mod4_4051
  · exact mod4_3
  · exact mod4_12379
  · exact mod4_5099
  · exact mod4_3
  · exact mod4_2411
  · exact mod4_67
  · exact mod4_3
  · exact mod4_10463
  · exact mod4_10631
  · exact mod4_3
  · exact mod4_2731
  · exact mod4_10271
  · exact mod4_3
  · exact mod4_4703
  · exact mod4_3623
  · exact mod4_3
  · exact mod4_971
  · exact mod4_1607
  · exact mod4_3
  · exact mod4_8819
  · exact mod4_2803
  · exact mod4_3
  · exact mod4_4127
  · exact mod4_383
  · exact mod4_3
  · exact mod4_271
  · exact mod4_8963
  · exact mod4_3
  · exact mod4_1187
  · exact mod4_1723
  · exact mod4_3
  · exact mod4_9631
  · exact mod4_1831
  · exact mod4_3
  · exact mod4_271
  · exact mod4_919
  · exact mod4_3499
  · exact mod4_7
  · exact mod4_1319
  · exact mod4_43
  · exact mod4_7
  · exact mod4_6043
  · exact mod4_4787
  · exact mod4_7
  · exact mod4_547
  · exact mod4_167
  · exact mod4_7
  · exact mod4_31
  · exact mod4_1867
  · exact mod4_7
  · exact mod4_15259
  · exact mod4_1723
  · exact mod4_7
  · exact mod4_43
  · exact mod4_9719
  · exact mod4_251
  · exact mod4_7127
  · exact mod4_31
  · exact mod4_7
  · exact mod4_947
  · exact mod4_43
  · exact mod4_7
  · exact mod4_31
  · exact mod4_14251
  · exact mod4_7
  · exact mod4_8263
  · exact mod4_12503
  · exact mod4_7
  · exact mod4_2251
  · exact mod4_5591
  · exact mod4_7
  · exact mod4_1187
  · exact mod4_31
  · exact mod4_7
  · cases h_false

lemma blocking_prime_by_idx_35_3mod4 (idx : ℕ) : blocking_prime_by_idx_35 idx % 4 = 3 :=
  mod4_of_mem_blocking_primes_35 (getD_mem blocking_primes_35 (idx - 3500) 3)

def blocking_primes_36 : List ℕ := [3, 11, 31, 3, 3359, 11, 3, 31, 347, 3, 11, 11, 3, 67, 307, 3, 11, 31, 3, 431, 31, 3, 31, 23, 3, 11, 11, 3, 8623, 743, 3, 11, 31, 3, 23, 11, 3, 31, 4423, 3, 3, 19, 1087, 3, 163, 6547, 3, 2003, 4583, 3, 19, 2687, 3, 9419, 17327, 3, 131, 5023, 3, 19, 683, 3, 211, 8423, 3, 443, 9479, 3, 19, 859, 3, 331, 167, 3, 1871, 2647, 3, 19, 2459, 3, 7, 2311, 43, 7, 11, 5683, 7, 8191, 9103, 7, 23, 127, 7, 1091, 11, 7, 43, 811, 127, 11]
def blocking_prime_by_idx_36 (idx : ℕ) : ℕ := blocking_primes_36.getD (idx - 3600) 3

lemma prime_of_mem_blocking_primes_36 {p : ℕ} (h : p ∈ 3 :: blocking_primes_36) : Nat.Prime p := by
  unfold blocking_primes_36 at h
  simp only [List.mem_cons] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | h_false
  · exact prime_3
  · exact prime_3
  · exact prime_11
  · exact prime_31
  · exact prime_3
  · exact prime_3359
  · exact prime_11
  · exact prime_3
  · exact prime_31
  · exact prime_347
  · exact prime_3
  · exact prime_11
  · exact prime_11
  · exact prime_3
  · exact prime_67
  · exact prime_307
  · exact prime_3
  · exact prime_11
  · exact prime_31
  · exact prime_3
  · exact prime_431
  · exact prime_31
  · exact prime_3
  · exact prime_31
  · exact prime_23
  · exact prime_3
  · exact prime_11
  · exact prime_11
  · exact prime_3
  · exact prime_8623
  · exact prime_743
  · exact prime_3
  · exact prime_11
  · exact prime_31
  · exact prime_3
  · exact prime_23
  · exact prime_11
  · exact prime_3
  · exact prime_31
  · exact prime_4423
  · exact prime_3
  · exact prime_3
  · exact prime_19
  · exact prime_1087
  · exact prime_3
  · exact prime_163
  · exact prime_6547
  · exact prime_3
  · exact prime_2003
  · exact prime_4583
  · exact prime_3
  · exact prime_19
  · exact prime_2687
  · exact prime_3
  · exact prime_9419
  · exact prime_17327
  · exact prime_3
  · exact prime_131
  · exact prime_5023
  · exact prime_3
  · exact prime_19
  · exact prime_683
  · exact prime_3
  · exact prime_211
  · exact prime_8423
  · exact prime_3
  · exact prime_443
  · exact prime_9479
  · exact prime_3
  · exact prime_19
  · exact prime_859
  · exact prime_3
  · exact prime_331
  · exact prime_167
  · exact prime_3
  · exact prime_1871
  · exact prime_2647
  · exact prime_3
  · exact prime_19
  · exact prime_2459
  · exact prime_3
  · exact prime_7
  · exact prime_2311
  · exact prime_43
  · exact prime_7
  · exact prime_11
  · exact prime_5683
  · exact prime_7
  · exact prime_8191
  · exact prime_9103
  · exact prime_7
  · exact prime_23
  · exact prime_127
  · exact prime_7
  · exact prime_1091
  · exact prime_11
  · exact prime_7
  · exact prime_43
  · exact prime_811
  · exact prime_127
  · exact prime_11
  · cases h_false

lemma blocking_prime_by_idx_36_prime (idx : ℕ) : Nat.Prime (blocking_prime_by_idx_36 idx) :=
  prime_of_mem_blocking_primes_36 (getD_mem blocking_primes_36 (idx - 3600) 3)

lemma mod4_of_mem_blocking_primes_36 {p : ℕ} (h : p ∈ 3 :: blocking_primes_36) : p % 4 = 3 := by
  unfold blocking_primes_36 at h
  simp only [List.mem_cons] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | h_false
  · exact mod4_3
  · exact mod4_3
  · exact mod4_11
  · exact mod4_31
  · exact mod4_3
  · exact mod4_3359
  · exact mod4_11
  · exact mod4_3
  · exact mod4_31
  · exact mod4_347
  · exact mod4_3
  · exact mod4_11
  · exact mod4_11
  · exact mod4_3
  · exact mod4_67
  · exact mod4_307
  · exact mod4_3
  · exact mod4_11
  · exact mod4_31
  · exact mod4_3
  · exact mod4_431
  · exact mod4_31
  · exact mod4_3
  · exact mod4_31
  · exact mod4_23
  · exact mod4_3
  · exact mod4_11
  · exact mod4_11
  · exact mod4_3
  · exact mod4_8623
  · exact mod4_743
  · exact mod4_3
  · exact mod4_11
  · exact mod4_31
  · exact mod4_3
  · exact mod4_23
  · exact mod4_11
  · exact mod4_3
  · exact mod4_31
  · exact mod4_4423
  · exact mod4_3
  · exact mod4_3
  · exact mod4_19
  · exact mod4_1087
  · exact mod4_3
  · exact mod4_163
  · exact mod4_6547
  · exact mod4_3
  · exact mod4_2003
  · exact mod4_4583
  · exact mod4_3
  · exact mod4_19
  · exact mod4_2687
  · exact mod4_3
  · exact mod4_9419
  · exact mod4_17327
  · exact mod4_3
  · exact mod4_131
  · exact mod4_5023
  · exact mod4_3
  · exact mod4_19
  · exact mod4_683
  · exact mod4_3
  · exact mod4_211
  · exact mod4_8423
  · exact mod4_3
  · exact mod4_443
  · exact mod4_9479
  · exact mod4_3
  · exact mod4_19
  · exact mod4_859
  · exact mod4_3
  · exact mod4_331
  · exact mod4_167
  · exact mod4_3
  · exact mod4_1871
  · exact mod4_2647
  · exact mod4_3
  · exact mod4_19
  · exact mod4_2459
  · exact mod4_3
  · exact mod4_7
  · exact mod4_2311
  · exact mod4_43
  · exact mod4_7
  · exact mod4_11
  · exact mod4_5683
  · exact mod4_7
  · exact mod4_8191
  · exact mod4_9103
  · exact mod4_7
  · exact mod4_23
  · exact mod4_127
  · exact mod4_7
  · exact mod4_1091
  · exact mod4_11
  · exact mod4_7
  · exact mod4_43
  · exact mod4_811
  · exact mod4_127
  · exact mod4_11
  · cases h_false

lemma blocking_prime_by_idx_36_3mod4 (idx : ℕ) : blocking_prime_by_idx_36 idx % 4 = 3 :=
  mod4_of_mem_blocking_primes_36 (getD_mem blocking_primes_36 (idx - 3600) 3)

def blocking_primes_37 : List ℕ := [8191, 7, 4903, 43, 7, 127, 199, 7, 59, 11, 7, 17327, 23, 7, 11, 5419, 7, 43, 59, 11, 3, 1447, 7151, 3, 151, 379, 3, 1451, 19, 3, 127, 4931, 3, 5867, 331, 3, 2939, 19, 3, 47, 367, 3, 23, 4783, 3, 10243, 19, 3, 23, 331, 3, 127, 8191, 3, 151, 19, 3, 9011, 127, 3, 3, 1439, 59, 3, 4703, 23, 3, 71, 31, 3, 2731, 2039, 3, 31, 5507, 3, 23, 5351, 3, 7499, 4091, 3, 7019, 31, 3, 47, 7451, 3, 31, 1811, 3, 59, 1607, 3, 2999, 15439, 3, 1103, 31, 3]
def blocking_prime_by_idx_37 (idx : ℕ) : ℕ := blocking_primes_37.getD (idx - 3700) 3

lemma prime_of_mem_blocking_primes_37 {p : ℕ} (h : p ∈ 3 :: blocking_primes_37) : Nat.Prime p := by
  unfold blocking_primes_37 at h
  simp only [List.mem_cons] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | h_false
  · exact prime_3
  · exact prime_8191
  · exact prime_7
  · exact prime_4903
  · exact prime_43
  · exact prime_7
  · exact prime_127
  · exact prime_199
  · exact prime_7
  · exact prime_59
  · exact prime_11
  · exact prime_7
  · exact prime_17327
  · exact prime_23
  · exact prime_7
  · exact prime_11
  · exact prime_5419
  · exact prime_7
  · exact prime_43
  · exact prime_59
  · exact prime_11
  · exact prime_3
  · exact prime_1447
  · exact prime_7151
  · exact prime_3
  · exact prime_151
  · exact prime_379
  · exact prime_3
  · exact prime_1451
  · exact prime_19
  · exact prime_3
  · exact prime_127
  · exact prime_4931
  · exact prime_3
  · exact prime_5867
  · exact prime_331
  · exact prime_3
  · exact prime_2939
  · exact prime_19
  · exact prime_3
  · exact prime_47
  · exact prime_367
  · exact prime_3
  · exact prime_23
  · exact prime_4783
  · exact prime_3
  · exact prime_10243
  · exact prime_19
  · exact prime_3
  · exact prime_23
  · exact prime_331
  · exact prime_3
  · exact prime_127
  · exact prime_8191
  · exact prime_3
  · exact prime_151
  · exact prime_19
  · exact prime_3
  · exact prime_9011
  · exact prime_127
  · exact prime_3
  · exact prime_3
  · exact prime_1439
  · exact prime_59
  · exact prime_3
  · exact prime_4703
  · exact prime_23
  · exact prime_3
  · exact prime_71
  · exact prime_31
  · exact prime_3
  · exact prime_2731
  · exact prime_2039
  · exact prime_3
  · exact prime_31
  · exact prime_5507
  · exact prime_3
  · exact prime_23
  · exact prime_5351
  · exact prime_3
  · exact prime_7499
  · exact prime_4091
  · exact prime_3
  · exact prime_7019
  · exact prime_31
  · exact prime_3
  · exact prime_47
  · exact prime_7451
  · exact prime_3
  · exact prime_31
  · exact prime_1811
  · exact prime_3
  · exact prime_59
  · exact prime_1607
  · exact prime_3
  · exact prime_2999
  · exact prime_15439
  · exact prime_3
  · exact prime_1103
  · exact prime_31
  · exact prime_3
  · cases h_false

lemma blocking_prime_by_idx_37_prime (idx : ℕ) : Nat.Prime (blocking_prime_by_idx_37 idx) :=
  prime_of_mem_blocking_primes_37 (getD_mem blocking_primes_37 (idx - 3700) 3)

lemma mod4_of_mem_blocking_primes_37 {p : ℕ} (h : p ∈ 3 :: blocking_primes_37) : p % 4 = 3 := by
  unfold blocking_primes_37 at h
  simp only [List.mem_cons] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | h_false
  · exact mod4_3
  · exact mod4_8191
  · exact mod4_7
  · exact mod4_4903
  · exact mod4_43
  · exact mod4_7
  · exact mod4_127
  · exact mod4_199
  · exact mod4_7
  · exact mod4_59
  · exact mod4_11
  · exact mod4_7
  · exact mod4_17327
  · exact mod4_23
  · exact mod4_7
  · exact mod4_11
  · exact mod4_5419
  · exact mod4_7
  · exact mod4_43
  · exact mod4_59
  · exact mod4_11
  · exact mod4_3
  · exact mod4_1447
  · exact mod4_7151
  · exact mod4_3
  · exact mod4_151
  · exact mod4_379
  · exact mod4_3
  · exact mod4_1451
  · exact mod4_19
  · exact mod4_3
  · exact mod4_127
  · exact mod4_4931
  · exact mod4_3
  · exact mod4_5867
  · exact mod4_331
  · exact mod4_3
  · exact mod4_2939
  · exact mod4_19
  · exact mod4_3
  · exact mod4_47
  · exact mod4_367
  · exact mod4_3
  · exact mod4_23
  · exact mod4_4783
  · exact mod4_3
  · exact mod4_10243
  · exact mod4_19
  · exact mod4_3
  · exact mod4_23
  · exact mod4_331
  · exact mod4_3
  · exact mod4_127
  · exact mod4_8191
  · exact mod4_3
  · exact mod4_151
  · exact mod4_19
  · exact mod4_3
  · exact mod4_9011
  · exact mod4_127
  · exact mod4_3
  · exact mod4_3
  · exact mod4_1439
  · exact mod4_59
  · exact mod4_3
  · exact mod4_4703
  · exact mod4_23
  · exact mod4_3
  · exact mod4_71
  · exact mod4_31
  · exact mod4_3
  · exact mod4_2731
  · exact mod4_2039
  · exact mod4_3
  · exact mod4_31
  · exact mod4_5507
  · exact mod4_3
  · exact mod4_23
  · exact mod4_5351
  · exact mod4_3
  · exact mod4_7499
  · exact mod4_4091
  · exact mod4_3
  · exact mod4_7019
  · exact mod4_31
  · exact mod4_3
  · exact mod4_47
  · exact mod4_7451
  · exact mod4_3
  · exact mod4_31
  · exact mod4_1811
  · exact mod4_3
  · exact mod4_59
  · exact mod4_1607
  · exact mod4_3
  · exact mod4_2999
  · exact mod4_15439
  · exact mod4_3
  · exact mod4_1103
  · exact mod4_31
  · exact mod4_3
  · cases h_false

lemma blocking_prime_by_idx_37_3mod4 (idx : ℕ) : blocking_prime_by_idx_37 idx % 4 = 3 :=
  mod4_of_mem_blocking_primes_37 (getD_mem blocking_primes_37 (idx - 3700) 3)

def blocking_primes_38 : List ℕ := [7, 11, 31, 7, 71, 11, 7, 31, 19319, 7, 11, 11, 7, 2791, 3691, 31, 11, 31, 7, 19183, 11, 7, 31, 3203, 7, 11, 11, 7, 479, 547, 7, 11, 31, 7, 8831, 11, 11, 31, 227, 7, 3, 7187, 12671, 3, 103, 43, 3, 223, 1187, 3, 3079, 6571, 3, 7351, 6947, 3, 3371, 7027, 3, 5843, 1483, 3, 163, 11119, 3, 6203, 43, 3, 6163, 83, 3, 79, 727, 3, 3943, 1291, 3, 5407, 16603, 3, 3, 3307, 1979, 3, 11, 6659, 3, 1579, 223, 3, 7907, 8443, 3, 967, 11, 3, 1471, 1163, 3, 11]
def blocking_prime_by_idx_38 (idx : ℕ) : ℕ := blocking_primes_38.getD (idx - 3800) 3

lemma prime_of_mem_blocking_primes_38 {p : ℕ} (h : p ∈ 3 :: blocking_primes_38) : Nat.Prime p := by
  unfold blocking_primes_38 at h
  simp only [List.mem_cons] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | h_false
  · exact prime_3
  · exact prime_7
  · exact prime_11
  · exact prime_31
  · exact prime_7
  · exact prime_71
  · exact prime_11
  · exact prime_7
  · exact prime_31
  · exact prime_19319
  · exact prime_7
  · exact prime_11
  · exact prime_11
  · exact prime_7
  · exact prime_2791
  · exact prime_3691
  · exact prime_31
  · exact prime_11
  · exact prime_31
  · exact prime_7
  · exact prime_19183
  · exact prime_11
  · exact prime_7
  · exact prime_31
  · exact prime_3203
  · exact prime_7
  · exact prime_11
  · exact prime_11
  · exact prime_7
  · exact prime_479
  · exact prime_547
  · exact prime_7
  · exact prime_11
  · exact prime_31
  · exact prime_7
  · exact prime_8831
  · exact prime_11
  · exact prime_11
  · exact prime_31
  · exact prime_227
  · exact prime_7
  · exact prime_3
  · exact prime_7187
  · exact prime_12671
  · exact prime_3
  · exact prime_103
  · exact prime_43
  · exact prime_3
  · exact prime_223
  · exact prime_1187
  · exact prime_3
  · exact prime_3079
  · exact prime_6571
  · exact prime_3
  · exact prime_7351
  · exact prime_6947
  · exact prime_3
  · exact prime_3371
  · exact prime_7027
  · exact prime_3
  · exact prime_5843
  · exact prime_1483
  · exact prime_3
  · exact prime_163
  · exact prime_11119
  · exact prime_3
  · exact prime_6203
  · exact prime_43
  · exact prime_3
  · exact prime_6163
  · exact prime_83
  · exact prime_3
  · exact prime_79
  · exact prime_727
  · exact prime_3
  · exact prime_3943
  · exact prime_1291
  · exact prime_3
  · exact prime_5407
  · exact prime_16603
  · exact prime_3
  · exact prime_3
  · exact prime_3307
  · exact prime_1979
  · exact prime_3
  · exact prime_11
  · exact prime_6659
  · exact prime_3
  · exact prime_1579
  · exact prime_223
  · exact prime_3
  · exact prime_7907
  · exact prime_8443
  · exact prime_3
  · exact prime_967
  · exact prime_11
  · exact prime_3
  · exact prime_1471
  · exact prime_1163
  · exact prime_3
  · exact prime_11
  · cases h_false

lemma blocking_prime_by_idx_38_prime (idx : ℕ) : Nat.Prime (blocking_prime_by_idx_38 idx) :=
  prime_of_mem_blocking_primes_38 (getD_mem blocking_primes_38 (idx - 3800) 3)

lemma mod4_of_mem_blocking_primes_38 {p : ℕ} (h : p ∈ 3 :: blocking_primes_38) : p % 4 = 3 := by
  unfold blocking_primes_38 at h
  simp only [List.mem_cons] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | h_false
  · exact mod4_3
  · exact mod4_7
  · exact mod4_11
  · exact mod4_31
  · exact mod4_7
  · exact mod4_71
  · exact mod4_11
  · exact mod4_7
  · exact mod4_31
  · exact mod4_19319
  · exact mod4_7
  · exact mod4_11
  · exact mod4_11
  · exact mod4_7
  · exact mod4_2791
  · exact mod4_3691
  · exact mod4_31
  · exact mod4_11
  · exact mod4_31
  · exact mod4_7
  · exact mod4_19183
  · exact mod4_11
  · exact mod4_7
  · exact mod4_31
  · exact mod4_3203
  · exact mod4_7
  · exact mod4_11
  · exact mod4_11
  · exact mod4_7
  · exact mod4_479
  · exact mod4_547
  · exact mod4_7
  · exact mod4_11
  · exact mod4_31
  · exact mod4_7
  · exact mod4_8831
  · exact mod4_11
  · exact mod4_11
  · exact mod4_31
  · exact mod4_227
  · exact mod4_7
  · exact mod4_3
  · exact mod4_7187
  · exact mod4_12671
  · exact mod4_3
  · exact mod4_103
  · exact mod4_43
  · exact mod4_3
  · exact mod4_223
  · exact mod4_1187
  · exact mod4_3
  · exact mod4_3079
  · exact mod4_6571
  · exact mod4_3
  · exact mod4_7351
  · exact mod4_6947
  · exact mod4_3
  · exact mod4_3371
  · exact mod4_7027
  · exact mod4_3
  · exact mod4_5843
  · exact mod4_1483
  · exact mod4_3
  · exact mod4_163
  · exact mod4_11119
  · exact mod4_3
  · exact mod4_6203
  · exact mod4_43
  · exact mod4_3
  · exact mod4_6163
  · exact mod4_83
  · exact mod4_3
  · exact mod4_79
  · exact mod4_727
  · exact mod4_3
  · exact mod4_3943
  · exact mod4_1291
  · exact mod4_3
  · exact mod4_5407
  · exact mod4_16603
  · exact mod4_3
  · exact mod4_3
  · exact mod4_3307
  · exact mod4_1979
  · exact mod4_3
  · exact mod4_11
  · exact mod4_6659
  · exact mod4_3
  · exact mod4_1579
  · exact mod4_223
  · exact mod4_3
  · exact mod4_7907
  · exact mod4_8443
  · exact mod4_3
  · exact mod4_967
  · exact mod4_11
  · exact mod4_3
  · exact mod4_1471
  · exact mod4_1163
  · exact mod4_3
  · exact mod4_11
  · cases h_false

lemma blocking_prime_by_idx_38_3mod4 (idx : ℕ) : blocking_prime_by_idx_38 idx % 4 = 3 :=
  mod4_of_mem_blocking_primes_38 (getD_mem blocking_primes_38 (idx - 3800) 3)

def blocking_primes_39 : List ℕ := [167, 3, 79, 3391, 3, 263, 163, 3, 1187, 11, 3, 2143, 4567, 3, 11, 431, 3, 10739, 8447, 3, 7, 751, 683, 7, 6287, 9923, 7, 467, 9967, 7, 1231, 1063, 9239, 683, 17107, 7, 3527, 8951, 7, 6047, 4051, 7, 4283, 7487, 7, 4463, 11027, 7, 5443, 2251, 7, 1559, 1063, 1427, 4651, 683, 7, 7307, 1123, 7, 3, 4219, 43, 3, 127, 9091, 3, 5419, 31, 3, 83, 127, 3, 31, 8803, 3, 43, 8387, 3, 1531, 1039, 3, 1823, 31, 3, 127, 2447, 3, 31, 2207, 3, 14251, 127, 3, 5711, 2971, 3, 43, 31, 3]
def blocking_prime_by_idx_39 (idx : ℕ) : ℕ := blocking_primes_39.getD (idx - 3900) 3

lemma prime_of_mem_blocking_primes_39 {p : ℕ} (h : p ∈ 3 :: blocking_primes_39) : Nat.Prime p := by
  unfold blocking_primes_39 at h
  simp only [List.mem_cons] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | h_false
  · exact prime_3
  · exact prime_167
  · exact prime_3
  · exact prime_79
  · exact prime_3391
  · exact prime_3
  · exact prime_263
  · exact prime_163
  · exact prime_3
  · exact prime_1187
  · exact prime_11
  · exact prime_3
  · exact prime_2143
  · exact prime_4567
  · exact prime_3
  · exact prime_11
  · exact prime_431
  · exact prime_3
  · exact prime_10739
  · exact prime_8447
  · exact prime_3
  · exact prime_7
  · exact prime_751
  · exact prime_683
  · exact prime_7
  · exact prime_6287
  · exact prime_9923
  · exact prime_7
  · exact prime_467
  · exact prime_9967
  · exact prime_7
  · exact prime_1231
  · exact prime_1063
  · exact prime_9239
  · exact prime_683
  · exact prime_17107
  · exact prime_7
  · exact prime_3527
  · exact prime_8951
  · exact prime_7
  · exact prime_6047
  · exact prime_4051
  · exact prime_7
  · exact prime_4283
  · exact prime_7487
  · exact prime_7
  · exact prime_4463
  · exact prime_11027
  · exact prime_7
  · exact prime_5443
  · exact prime_2251
  · exact prime_7
  · exact prime_1559
  · exact prime_1063
  · exact prime_1427
  · exact prime_4651
  · exact prime_683
  · exact prime_7
  · exact prime_7307
  · exact prime_1123
  · exact prime_7
  · exact prime_3
  · exact prime_4219
  · exact prime_43
  · exact prime_3
  · exact prime_127
  · exact prime_9091
  · exact prime_3
  · exact prime_5419
  · exact prime_31
  · exact prime_3
  · exact prime_83
  · exact prime_127
  · exact prime_3
  · exact prime_31
  · exact prime_8803
  · exact prime_3
  · exact prime_43
  · exact prime_8387
  · exact prime_3
  · exact prime_1531
  · exact prime_1039
  · exact prime_3
  · exact prime_1823
  · exact prime_31
  · exact prime_3
  · exact prime_127
  · exact prime_2447
  · exact prime_3
  · exact prime_31
  · exact prime_2207
  · exact prime_3
  · exact prime_14251
  · exact prime_127
  · exact prime_3
  · exact prime_5711
  · exact prime_2971
  · exact prime_3
  · exact prime_43
  · exact prime_31
  · exact prime_3
  · cases h_false

lemma blocking_prime_by_idx_39_prime (idx : ℕ) : Nat.Prime (blocking_prime_by_idx_39 idx) :=
  prime_of_mem_blocking_primes_39 (getD_mem blocking_primes_39 (idx - 3900) 3)

lemma mod4_of_mem_blocking_primes_39 {p : ℕ} (h : p ∈ 3 :: blocking_primes_39) : p % 4 = 3 := by
  unfold blocking_primes_39 at h
  simp only [List.mem_cons] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | h_false
  · exact mod4_3
  · exact mod4_167
  · exact mod4_3
  · exact mod4_79
  · exact mod4_3391
  · exact mod4_3
  · exact mod4_263
  · exact mod4_163
  · exact mod4_3
  · exact mod4_1187
  · exact mod4_11
  · exact mod4_3
  · exact mod4_2143
  · exact mod4_4567
  · exact mod4_3
  · exact mod4_11
  · exact mod4_431
  · exact mod4_3
  · exact mod4_10739
  · exact mod4_8447
  · exact mod4_3
  · exact mod4_7
  · exact mod4_751
  · exact mod4_683
  · exact mod4_7
  · exact mod4_6287
  · exact mod4_9923
  · exact mod4_7
  · exact mod4_467
  · exact mod4_9967
  · exact mod4_7
  · exact mod4_1231
  · exact mod4_1063
  · exact mod4_9239
  · exact mod4_683
  · exact mod4_17107
  · exact mod4_7
  · exact mod4_3527
  · exact mod4_8951
  · exact mod4_7
  · exact mod4_6047
  · exact mod4_4051
  · exact mod4_7
  · exact mod4_4283
  · exact mod4_7487
  · exact mod4_7
  · exact mod4_4463
  · exact mod4_11027
  · exact mod4_7
  · exact mod4_5443
  · exact mod4_2251
  · exact mod4_7
  · exact mod4_1559
  · exact mod4_1063
  · exact mod4_1427
  · exact mod4_4651
  · exact mod4_683
  · exact mod4_7
  · exact mod4_7307
  · exact mod4_1123
  · exact mod4_7
  · exact mod4_3
  · exact mod4_4219
  · exact mod4_43
  · exact mod4_3
  · exact mod4_127
  · exact mod4_9091
  · exact mod4_3
  · exact mod4_5419
  · exact mod4_31
  · exact mod4_3
  · exact mod4_83
  · exact mod4_127
  · exact mod4_3
  · exact mod4_31
  · exact mod4_8803
  · exact mod4_3
  · exact mod4_43
  · exact mod4_8387
  · exact mod4_3
  · exact mod4_1531
  · exact mod4_1039
  · exact mod4_3
  · exact mod4_1823
  · exact mod4_31
  · exact mod4_3
  · exact mod4_127
  · exact mod4_2447
  · exact mod4_3
  · exact mod4_31
  · exact mod4_2207
  · exact mod4_3
  · exact mod4_14251
  · exact mod4_127
  · exact mod4_3
  · exact mod4_5711
  · exact mod4_2971
  · exact mod4_3
  · exact mod4_43
  · exact mod4_31
  · exact mod4_3
  · cases h_false

lemma blocking_prime_by_idx_39_3mod4 (idx : ℕ) : blocking_prime_by_idx_39 idx % 4 = 3 :=
  mod4_of_mem_blocking_primes_39 (getD_mem blocking_primes_39 (idx - 3900) 3)

def blocking_primes_40 : List ℕ := [3, 11, 31, 3, 3923, 11, 3, 31, 1051, 3, 19, 5783, 3, 7283, 139, 3, 11, 31, 3, 19, 11, 3, 31, 16603, 3, 11, 11, 3, 19, 8291, 3, 11, 31, 3, 6343, 11, 3, 19, 127, 3, 7, 23, 1423, 7, 10223, 1543, 7, 12263, 12479, 947, 6287, 151, 7, 4243, 1279, 7, 2731, 1223, 7, 10531, 3779, 7, 3943, 23, 7, 1087, 151, 7, 467, 2731, 3803, 4111, 79, 7, 23, 11503, 7, 2131, 1571, 7, 3, 8087, 431, 3, 11, 2423, 3, 4507, 19, 3, 6619, 3407, 3, 839, 11, 3, 3019, 19, 3, 11]
def blocking_prime_by_idx_40 (idx : ℕ) : ℕ := blocking_primes_40.getD (idx - 4000) 3

lemma prime_of_mem_blocking_primes_40 {p : ℕ} (h : p ∈ 3 :: blocking_primes_40) : Nat.Prime p := by
  unfold blocking_primes_40 at h
  simp only [List.mem_cons] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | h_false
  · exact prime_3
  · exact prime_3
  · exact prime_11
  · exact prime_31
  · exact prime_3
  · exact prime_3923
  · exact prime_11
  · exact prime_3
  · exact prime_31
  · exact prime_1051
  · exact prime_3
  · exact prime_19
  · exact prime_5783
  · exact prime_3
  · exact prime_7283
  · exact prime_139
  · exact prime_3
  · exact prime_11
  · exact prime_31
  · exact prime_3
  · exact prime_19
  · exact prime_11
  · exact prime_3
  · exact prime_31
  · exact prime_16603
  · exact prime_3
  · exact prime_11
  · exact prime_11
  · exact prime_3
  · exact prime_19
  · exact prime_8291
  · exact prime_3
  · exact prime_11
  · exact prime_31
  · exact prime_3
  · exact prime_6343
  · exact prime_11
  · exact prime_3
  · exact prime_19
  · exact prime_127
  · exact prime_3
  · exact prime_7
  · exact prime_23
  · exact prime_1423
  · exact prime_7
  · exact prime_10223
  · exact prime_1543
  · exact prime_7
  · exact prime_12263
  · exact prime_12479
  · exact prime_947
  · exact prime_6287
  · exact prime_151
  · exact prime_7
  · exact prime_4243
  · exact prime_1279
  · exact prime_7
  · exact prime_2731
  · exact prime_1223
  · exact prime_7
  · exact prime_10531
  · exact prime_3779
  · exact prime_7
  · exact prime_3943
  · exact prime_23
  · exact prime_7
  · exact prime_1087
  · exact prime_151
  · exact prime_7
  · exact prime_467
  · exact prime_2731
  · exact prime_3803
  · exact prime_4111
  · exact prime_79
  · exact prime_7
  · exact prime_23
  · exact prime_11503
  · exact prime_7
  · exact prime_2131
  · exact prime_1571
  · exact prime_7
  · exact prime_3
  · exact prime_8087
  · exact prime_431
  · exact prime_3
  · exact prime_11
  · exact prime_2423
  · exact prime_3
  · exact prime_4507
  · exact prime_19
  · exact prime_3
  · exact prime_6619
  · exact prime_3407
  · exact prime_3
  · exact prime_839
  · exact prime_11
  · exact prime_3
  · exact prime_3019
  · exact prime_19
  · exact prime_3
  · exact prime_11
  · cases h_false

lemma blocking_prime_by_idx_40_prime (idx : ℕ) : Nat.Prime (blocking_prime_by_idx_40 idx) :=
  prime_of_mem_blocking_primes_40 (getD_mem blocking_primes_40 (idx - 4000) 3)

lemma mod4_of_mem_blocking_primes_40 {p : ℕ} (h : p ∈ 3 :: blocking_primes_40) : p % 4 = 3 := by
  unfold blocking_primes_40 at h
  simp only [List.mem_cons] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | h_false
  · exact mod4_3
  · exact mod4_3
  · exact mod4_11
  · exact mod4_31
  · exact mod4_3
  · exact mod4_3923
  · exact mod4_11
  · exact mod4_3
  · exact mod4_31
  · exact mod4_1051
  · exact mod4_3
  · exact mod4_19
  · exact mod4_5783
  · exact mod4_3
  · exact mod4_7283
  · exact mod4_139
  · exact mod4_3
  · exact mod4_11
  · exact mod4_31
  · exact mod4_3
  · exact mod4_19
  · exact mod4_11
  · exact mod4_3
  · exact mod4_31
  · exact mod4_16603
  · exact mod4_3
  · exact mod4_11
  · exact mod4_11
  · exact mod4_3
  · exact mod4_19
  · exact mod4_8291
  · exact mod4_3
  · exact mod4_11
  · exact mod4_31
  · exact mod4_3
  · exact mod4_6343
  · exact mod4_11
  · exact mod4_3
  · exact mod4_19
  · exact mod4_127
  · exact mod4_3
  · exact mod4_7
  · exact mod4_23
  · exact mod4_1423
  · exact mod4_7
  · exact mod4_10223
  · exact mod4_1543
  · exact mod4_7
  · exact mod4_12263
  · exact mod4_12479
  · exact mod4_947
  · exact mod4_6287
  · exact mod4_151
  · exact mod4_7
  · exact mod4_4243
  · exact mod4_1279
  · exact mod4_7
  · exact mod4_2731
  · exact mod4_1223
  · exact mod4_7
  · exact mod4_10531
  · exact mod4_3779
  · exact mod4_7
  · exact mod4_3943
  · exact mod4_23
  · exact mod4_7
  · exact mod4_1087
  · exact mod4_151
  · exact mod4_7
  · exact mod4_467
  · exact mod4_2731
  · exact mod4_3803
  · exact mod4_4111
  · exact mod4_79
  · exact mod4_7
  · exact mod4_23
  · exact mod4_11503
  · exact mod4_7
  · exact mod4_2131
  · exact mod4_1571
  · exact mod4_7
  · exact mod4_3
  · exact mod4_8087
  · exact mod4_431
  · exact mod4_3
  · exact mod4_11
  · exact mod4_2423
  · exact mod4_3
  · exact mod4_4507
  · exact mod4_19
  · exact mod4_3
  · exact mod4_6619
  · exact mod4_3407
  · exact mod4_3
  · exact mod4_839
  · exact mod4_11
  · exact mod4_3
  · exact mod4_3019
  · exact mod4_19
  · exact mod4_3
  · exact mod4_11
  · cases h_false

lemma blocking_prime_by_idx_40_3mod4 (idx : ℕ) : blocking_prime_by_idx_40 idx % 4 = 3 :=
  mod4_of_mem_blocking_primes_40 (getD_mem blocking_primes_40 (idx - 4000) 3)

def blocking_primes_41 : List ℕ := [683, 3, 14683, 2939, 3, 2591, 19, 3, 6547, 827, 3, 683, 1399, 3, 11, 19, 3, 3343, 4999, 3, 3, 67, 163, 3, 8167, 43, 3, 2851, 71, 3, 23, 239, 3, 2287, 3823, 3, 4679, 10223, 3, 43, 11491, 3, 17107, 7643, 3, 1307, 43, 3, 47, 3583, 3, 71, 23, 3, 67, 6131, 3, 14303, 191, 3, 7, 499, 6079, 7, 6427, 14939, 23, 1723, 31, 7, 107, 23, 7, 31, 9739, 7, 6163, 23, 7, 11287, 239, 7, 23, 31, 7, 6047, 15443, 4967, 31, 47, 7, 1627, 1259, 7, 2243, 827, 7, 887, 31, 7]
def blocking_prime_by_idx_41 (idx : ℕ) : ℕ := blocking_primes_41.getD (idx - 4100) 3

lemma prime_of_mem_blocking_primes_41 {p : ℕ} (h : p ∈ 3 :: blocking_primes_41) : Nat.Prime p := by
  unfold blocking_primes_41 at h
  simp only [List.mem_cons] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | h_false
  · exact prime_3
  · exact prime_683
  · exact prime_3
  · exact prime_14683
  · exact prime_2939
  · exact prime_3
  · exact prime_2591
  · exact prime_19
  · exact prime_3
  · exact prime_6547
  · exact prime_827
  · exact prime_3
  · exact prime_683
  · exact prime_1399
  · exact prime_3
  · exact prime_11
  · exact prime_19
  · exact prime_3
  · exact prime_3343
  · exact prime_4999
  · exact prime_3
  · exact prime_3
  · exact prime_67
  · exact prime_163
  · exact prime_3
  · exact prime_8167
  · exact prime_43
  · exact prime_3
  · exact prime_2851
  · exact prime_71
  · exact prime_3
  · exact prime_23
  · exact prime_239
  · exact prime_3
  · exact prime_2287
  · exact prime_3823
  · exact prime_3
  · exact prime_4679
  · exact prime_10223
  · exact prime_3
  · exact prime_43
  · exact prime_11491
  · exact prime_3
  · exact prime_17107
  · exact prime_7643
  · exact prime_3
  · exact prime_1307
  · exact prime_43
  · exact prime_3
  · exact prime_47
  · exact prime_3583
  · exact prime_3
  · exact prime_71
  · exact prime_23
  · exact prime_3
  · exact prime_67
  · exact prime_6131
  · exact prime_3
  · exact prime_14303
  · exact prime_191
  · exact prime_3
  · exact prime_7
  · exact prime_499
  · exact prime_6079
  · exact prime_7
  · exact prime_6427
  · exact prime_14939
  · exact prime_23
  · exact prime_1723
  · exact prime_31
  · exact prime_7
  · exact prime_107
  · exact prime_23
  · exact prime_7
  · exact prime_31
  · exact prime_9739
  · exact prime_7
  · exact prime_6163
  · exact prime_23
  · exact prime_7
  · exact prime_11287
  · exact prime_239
  · exact prime_7
  · exact prime_23
  · exact prime_31
  · exact prime_7
  · exact prime_6047
  · exact prime_15443
  · exact prime_4967
  · exact prime_31
  · exact prime_47
  · exact prime_7
  · exact prime_1627
  · exact prime_1259
  · exact prime_7
  · exact prime_2243
  · exact prime_827
  · exact prime_7
  · exact prime_887
  · exact prime_31
  · exact prime_7
  · cases h_false

lemma blocking_prime_by_idx_41_prime (idx : ℕ) : Nat.Prime (blocking_prime_by_idx_41 idx) :=
  prime_of_mem_blocking_primes_41 (getD_mem blocking_primes_41 (idx - 4100) 3)

lemma mod4_of_mem_blocking_primes_41 {p : ℕ} (h : p ∈ 3 :: blocking_primes_41) : p % 4 = 3 := by
  unfold blocking_primes_41 at h
  simp only [List.mem_cons] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | h_false
  · exact mod4_3
  · exact mod4_683
  · exact mod4_3
  · exact mod4_14683
  · exact mod4_2939
  · exact mod4_3
  · exact mod4_2591
  · exact mod4_19
  · exact mod4_3
  · exact mod4_6547
  · exact mod4_827
  · exact mod4_3
  · exact mod4_683
  · exact mod4_1399
  · exact mod4_3
  · exact mod4_11
  · exact mod4_19
  · exact mod4_3
  · exact mod4_3343
  · exact mod4_4999
  · exact mod4_3
  · exact mod4_3
  · exact mod4_67
  · exact mod4_163
  · exact mod4_3
  · exact mod4_8167
  · exact mod4_43
  · exact mod4_3
  · exact mod4_2851
  · exact mod4_71
  · exact mod4_3
  · exact mod4_23
  · exact mod4_239
  · exact mod4_3
  · exact mod4_2287
  · exact mod4_3823
  · exact mod4_3
  · exact mod4_4679
  · exact mod4_10223
  · exact mod4_3
  · exact mod4_43
  · exact mod4_11491
  · exact mod4_3
  · exact mod4_17107
  · exact mod4_7643
  · exact mod4_3
  · exact mod4_1307
  · exact mod4_43
  · exact mod4_3
  · exact mod4_47
  · exact mod4_3583
  · exact mod4_3
  · exact mod4_71
  · exact mod4_23
  · exact mod4_3
  · exact mod4_67
  · exact mod4_6131
  · exact mod4_3
  · exact mod4_14303
  · exact mod4_191
  · exact mod4_3
  · exact mod4_7
  · exact mod4_499
  · exact mod4_6079
  · exact mod4_7
  · exact mod4_6427
  · exact mod4_14939
  · exact mod4_23
  · exact mod4_1723
  · exact mod4_31
  · exact mod4_7
  · exact mod4_107
  · exact mod4_23
  · exact mod4_7
  · exact mod4_31
  · exact mod4_9739
  · exact mod4_7
  · exact mod4_6163
  · exact mod4_23
  · exact mod4_7
  · exact mod4_11287
  · exact mod4_239
  · exact mod4_7
  · exact mod4_23
  · exact mod4_31
  · exact mod4_7
  · exact mod4_6047
  · exact mod4_15443
  · exact mod4_4967
  · exact mod4_31
  · exact mod4_47
  · exact mod4_7
  · exact mod4_1627
  · exact mod4_1259
  · exact mod4_7
  · exact mod4_2243
  · exact mod4_827
  · exact mod4_7
  · exact mod4_887
  · exact mod4_31
  · exact mod4_7
  · cases h_false

lemma blocking_prime_by_idx_41_3mod4 (idx : ℕ) : blocking_prime_by_idx_41 idx % 4 = 3 :=
  mod4_of_mem_blocking_primes_41 (getD_mem blocking_primes_41 (idx - 4100) 3)

def blocking_primes_42 : List ℕ := [3, 11, 31, 3, 191, 31, 3, 31, 4651, 3, 11, 11, 3, 2963, 1499, 3, 11, 31, 3, 67, 11, 3, 31, 4007, 3, 11, 331, 3, 9923, 727, 3, 11, 31, 3, 16139, 11, 3, 31, 23, 3, 3, 331, 43, 3, 127, 4019, 3, 311, 191, 3, 1427, 127, 3, 307, 8011, 3, 43, 3907, 3, 8191, 227, 3, 2027, 43, 3, 83, 4643, 3, 6571, 79, 3, 331, 127, 3, 7487, 103, 3, 43, 6311, 3, 7, 14939, 3023, 127, 11, 439, 7, 1667, 3643, 7, 127, 8867, 7, 2011, 11, 7, 2083, 127, 7, 13367]
def blocking_prime_by_idx_42 (idx : ℕ) : ℕ := blocking_primes_42.getD (idx - 4200) 3

lemma prime_of_mem_blocking_primes_42 {p : ℕ} (h : p ∈ 3 :: blocking_primes_42) : Nat.Prime p := by
  unfold blocking_primes_42 at h
  simp only [List.mem_cons] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | h_false
  · exact prime_3
  · exact prime_3
  · exact prime_11
  · exact prime_31
  · exact prime_3
  · exact prime_191
  · exact prime_31
  · exact prime_3
  · exact prime_31
  · exact prime_4651
  · exact prime_3
  · exact prime_11
  · exact prime_11
  · exact prime_3
  · exact prime_2963
  · exact prime_1499
  · exact prime_3
  · exact prime_11
  · exact prime_31
  · exact prime_3
  · exact prime_67
  · exact prime_11
  · exact prime_3
  · exact prime_31
  · exact prime_4007
  · exact prime_3
  · exact prime_11
  · exact prime_331
  · exact prime_3
  · exact prime_9923
  · exact prime_727
  · exact prime_3
  · exact prime_11
  · exact prime_31
  · exact prime_3
  · exact prime_16139
  · exact prime_11
  · exact prime_3
  · exact prime_31
  · exact prime_23
  · exact prime_3
  · exact prime_3
  · exact prime_331
  · exact prime_43
  · exact prime_3
  · exact prime_127
  · exact prime_4019
  · exact prime_3
  · exact prime_311
  · exact prime_191
  · exact prime_3
  · exact prime_1427
  · exact prime_127
  · exact prime_3
  · exact prime_307
  · exact prime_8011
  · exact prime_3
  · exact prime_43
  · exact prime_3907
  · exact prime_3
  · exact prime_8191
  · exact prime_227
  · exact prime_3
  · exact prime_2027
  · exact prime_43
  · exact prime_3
  · exact prime_83
  · exact prime_4643
  · exact prime_3
  · exact prime_6571
  · exact prime_79
  · exact prime_3
  · exact prime_331
  · exact prime_127
  · exact prime_3
  · exact prime_7487
  · exact prime_103
  · exact prime_3
  · exact prime_43
  · exact prime_6311
  · exact prime_3
  · exact prime_7
  · exact prime_14939
  · exact prime_3023
  · exact prime_127
  · exact prime_11
  · exact prime_439
  · exact prime_7
  · exact prime_1667
  · exact prime_3643
  · exact prime_7
  · exact prime_127
  · exact prime_8867
  · exact prime_7
  · exact prime_2011
  · exact prime_11
  · exact prime_7
  · exact prime_2083
  · exact prime_127
  · exact prime_7
  · exact prime_13367
  · cases h_false

lemma blocking_prime_by_idx_42_prime (idx : ℕ) : Nat.Prime (blocking_prime_by_idx_42 idx) :=
  prime_of_mem_blocking_primes_42 (getD_mem blocking_primes_42 (idx - 4200) 3)

lemma mod4_of_mem_blocking_primes_42 {p : ℕ} (h : p ∈ 3 :: blocking_primes_42) : p % 4 = 3 := by
  unfold blocking_primes_42 at h
  simp only [List.mem_cons] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | h_false
  · exact mod4_3
  · exact mod4_3
  · exact mod4_11
  · exact mod4_31
  · exact mod4_3
  · exact mod4_191
  · exact mod4_31
  · exact mod4_3
  · exact mod4_31
  · exact mod4_4651
  · exact mod4_3
  · exact mod4_11
  · exact mod4_11
  · exact mod4_3
  · exact mod4_2963
  · exact mod4_1499
  · exact mod4_3
  · exact mod4_11
  · exact mod4_31
  · exact mod4_3
  · exact mod4_67
  · exact mod4_11
  · exact mod4_3
  · exact mod4_31
  · exact mod4_4007
  · exact mod4_3
  · exact mod4_11
  · exact mod4_331
  · exact mod4_3
  · exact mod4_9923
  · exact mod4_727
  · exact mod4_3
  · exact mod4_11
  · exact mod4_31
  · exact mod4_3
  · exact mod4_16139
  · exact mod4_11
  · exact mod4_3
  · exact mod4_31
  · exact mod4_23
  · exact mod4_3
  · exact mod4_3
  · exact mod4_331
  · exact mod4_43
  · exact mod4_3
  · exact mod4_127
  · exact mod4_4019
  · exact mod4_3
  · exact mod4_311
  · exact mod4_191
  · exact mod4_3
  · exact mod4_1427
  · exact mod4_127
  · exact mod4_3
  · exact mod4_307
  · exact mod4_8011
  · exact mod4_3
  · exact mod4_43
  · exact mod4_3907
  · exact mod4_3
  · exact mod4_8191
  · exact mod4_227
  · exact mod4_3
  · exact mod4_2027
  · exact mod4_43
  · exact mod4_3
  · exact mod4_83
  · exact mod4_4643
  · exact mod4_3
  · exact mod4_6571
  · exact mod4_79
  · exact mod4_3
  · exact mod4_331
  · exact mod4_127
  · exact mod4_3
  · exact mod4_7487
  · exact mod4_103
  · exact mod4_3
  · exact mod4_43
  · exact mod4_6311
  · exact mod4_3
  · exact mod4_7
  · exact mod4_14939
  · exact mod4_3023
  · exact mod4_127
  · exact mod4_11
  · exact mod4_439
  · exact mod4_7
  · exact mod4_1667
  · exact mod4_3643
  · exact mod4_7
  · exact mod4_127
  · exact mod4_8867
  · exact mod4_7
  · exact mod4_2011
  · exact mod4_11
  · exact mod4_7
  · exact mod4_2083
  · exact mod4_127
  · exact mod4_7
  · exact mod4_13367
  · cases h_false

lemma blocking_prime_by_idx_42_3mod4 (idx : ℕ) : blocking_prime_by_idx_42 idx % 4 = 3 :=
  mod4_of_mem_blocking_primes_42 (getD_mem blocking_primes_42 (idx - 4200) 3)

def blocking_primes_43 : List ℕ := [5519, 7, 71, 47, 11, 5639, 4211, 7, 7603, 11, 7, 127, 8839, 7, 11, 9743, 7, 1447, 127, 7, 3, 103, 71, 3, 47, 3371, 3, 59, 107, 3, 8443, 1439, 3, 1871, 331, 3, 3251, 1823, 3, 103, 2143, 3, 8779, 8887, 3, 19183, 2239, 3, 71, 331, 3, 2131, 2383, 3, 151, 4871, 3, 71, 1259, 3, 3, 19, 683, 3, 7043, 2663, 3, 3251, 31, 3, 19, 16699, 3, 31, 607, 3, 8059, 59, 3, 19, 947, 3, 4259, 31, 3, 1427, 9811, 3, 19, 367, 3, 2251, 2551, 3, 2239, 683, 3, 19, 31, 3]
def blocking_prime_by_idx_43 (idx : ℕ) : ℕ := blocking_primes_43.getD (idx - 4300) 3

lemma prime_of_mem_blocking_primes_43 {p : ℕ} (h : p ∈ 3 :: blocking_primes_43) : Nat.Prime p := by
  unfold blocking_primes_43 at h
  simp only [List.mem_cons] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | h_false
  · exact prime_3
  · exact prime_5519
  · exact prime_7
  · exact prime_71
  · exact prime_47
  · exact prime_11
  · exact prime_5639
  · exact prime_4211
  · exact prime_7
  · exact prime_7603
  · exact prime_11
  · exact prime_7
  · exact prime_127
  · exact prime_8839
  · exact prime_7
  · exact prime_11
  · exact prime_9743
  · exact prime_7
  · exact prime_1447
  · exact prime_127
  · exact prime_7
  · exact prime_3
  · exact prime_103
  · exact prime_71
  · exact prime_3
  · exact prime_47
  · exact prime_3371
  · exact prime_3
  · exact prime_59
  · exact prime_107
  · exact prime_3
  · exact prime_8443
  · exact prime_1439
  · exact prime_3
  · exact prime_1871
  · exact prime_331
  · exact prime_3
  · exact prime_3251
  · exact prime_1823
  · exact prime_3
  · exact prime_103
  · exact prime_2143
  · exact prime_3
  · exact prime_8779
  · exact prime_8887
  · exact prime_3
  · exact prime_19183
  · exact prime_2239
  · exact prime_3
  · exact prime_71
  · exact prime_331
  · exact prime_3
  · exact prime_2131
  · exact prime_2383
  · exact prime_3
  · exact prime_151
  · exact prime_4871
  · exact prime_3
  · exact prime_71
  · exact prime_1259
  · exact prime_3
  · exact prime_3
  · exact prime_19
  · exact prime_683
  · exact prime_3
  · exact prime_7043
  · exact prime_2663
  · exact prime_3
  · exact prime_3251
  · exact prime_31
  · exact prime_3
  · exact prime_19
  · exact prime_16699
  · exact prime_3
  · exact prime_31
  · exact prime_607
  · exact prime_3
  · exact prime_8059
  · exact prime_59
  · exact prime_3
  · exact prime_19
  · exact prime_947
  · exact prime_3
  · exact prime_4259
  · exact prime_31
  · exact prime_3
  · exact prime_1427
  · exact prime_9811
  · exact prime_3
  · exact prime_19
  · exact prime_367
  · exact prime_3
  · exact prime_2251
  · exact prime_2551
  · exact prime_3
  · exact prime_2239
  · exact prime_683
  · exact prime_3
  · exact prime_19
  · exact prime_31
  · exact prime_3
  · cases h_false

lemma blocking_prime_by_idx_43_prime (idx : ℕ) : Nat.Prime (blocking_prime_by_idx_43 idx) :=
  prime_of_mem_blocking_primes_43 (getD_mem blocking_primes_43 (idx - 4300) 3)

lemma mod4_of_mem_blocking_primes_43 {p : ℕ} (h : p ∈ 3 :: blocking_primes_43) : p % 4 = 3 := by
  unfold blocking_primes_43 at h
  simp only [List.mem_cons] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | h_false
  · exact mod4_3
  · exact mod4_5519
  · exact mod4_7
  · exact mod4_71
  · exact mod4_47
  · exact mod4_11
  · exact mod4_5639
  · exact mod4_4211
  · exact mod4_7
  · exact mod4_7603
  · exact mod4_11
  · exact mod4_7
  · exact mod4_127
  · exact mod4_8839
  · exact mod4_7
  · exact mod4_11
  · exact mod4_9743
  · exact mod4_7
  · exact mod4_1447
  · exact mod4_127
  · exact mod4_7
  · exact mod4_3
  · exact mod4_103
  · exact mod4_71
  · exact mod4_3
  · exact mod4_47
  · exact mod4_3371
  · exact mod4_3
  · exact mod4_59
  · exact mod4_107
  · exact mod4_3
  · exact mod4_8443
  · exact mod4_1439
  · exact mod4_3
  · exact mod4_1871
  · exact mod4_331
  · exact mod4_3
  · exact mod4_3251
  · exact mod4_1823
  · exact mod4_3
  · exact mod4_103
  · exact mod4_2143
  · exact mod4_3
  · exact mod4_8779
  · exact mod4_8887
  · exact mod4_3
  · exact mod4_19183
  · exact mod4_2239
  · exact mod4_3
  · exact mod4_71
  · exact mod4_331
  · exact mod4_3
  · exact mod4_2131
  · exact mod4_2383
  · exact mod4_3
  · exact mod4_151
  · exact mod4_4871
  · exact mod4_3
  · exact mod4_71
  · exact mod4_1259
  · exact mod4_3
  · exact mod4_3
  · exact mod4_19
  · exact mod4_683
  · exact mod4_3
  · exact mod4_7043
  · exact mod4_2663
  · exact mod4_3
  · exact mod4_3251
  · exact mod4_31
  · exact mod4_3
  · exact mod4_19
  · exact mod4_16699
  · exact mod4_3
  · exact mod4_31
  · exact mod4_607
  · exact mod4_3
  · exact mod4_8059
  · exact mod4_59
  · exact mod4_3
  · exact mod4_19
  · exact mod4_947
  · exact mod4_3
  · exact mod4_4259
  · exact mod4_31
  · exact mod4_3
  · exact mod4_1427
  · exact mod4_9811
  · exact mod4_3
  · exact mod4_19
  · exact mod4_367
  · exact mod4_3
  · exact mod4_2251
  · exact mod4_2551
  · exact mod4_3
  · exact mod4_2239
  · exact mod4_683
  · exact mod4_3
  · exact mod4_19
  · exact mod4_31
  · exact mod4_3
  · cases h_false

lemma blocking_prime_by_idx_43_3mod4 (idx : ℕ) : blocking_prime_by_idx_43 idx % 4 = 3 :=
  mod4_of_mem_blocking_primes_43 (getD_mem blocking_primes_43 (idx - 4300) 3)

def blocking_primes_44 : List ℕ := [31, 11, 107, 7, 1627, 11, 7, 31, 10531, 7, 11, 11, 7, 139, 67, 7, 11, 31, 7, 43, 11, 11, 31, 12763, 7, 11, 11, 7, 6983, 751, 7, 11, 31, 7, 1231, 11, 7, 31, 6803, 7, 3, 3947, 3067, 3, 3187, 10067, 3, 103, 19, 3, 223, 8419, 3, 1367, 9371, 3, 2671, 19, 3, 3911, 2083, 3, 1171, 1823, 3, 5351, 2843, 3, 5923, 5323, 3, 2591, 1531, 3, 2351, 19, 3, 8467, 1223, 3, 3, 23, 1951, 3, 11, 59, 3, 1307, 1951, 3, 9151, 4759, 3, 3251, 11, 3, 1259, 5347, 3, 11]
def blocking_prime_by_idx_44 (idx : ℕ) : ℕ := blocking_primes_44.getD (idx - 4400) 3

lemma prime_of_mem_blocking_primes_44 {p : ℕ} (h : p ∈ 3 :: blocking_primes_44) : Nat.Prime p := by
  unfold blocking_primes_44 at h
  simp only [List.mem_cons] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | h_false
  · exact prime_3
  · exact prime_31
  · exact prime_11
  · exact prime_107
  · exact prime_7
  · exact prime_1627
  · exact prime_11
  · exact prime_7
  · exact prime_31
  · exact prime_10531
  · exact prime_7
  · exact prime_11
  · exact prime_11
  · exact prime_7
  · exact prime_139
  · exact prime_67
  · exact prime_7
  · exact prime_11
  · exact prime_31
  · exact prime_7
  · exact prime_43
  · exact prime_11
  · exact prime_11
  · exact prime_31
  · exact prime_12763
  · exact prime_7
  · exact prime_11
  · exact prime_11
  · exact prime_7
  · exact prime_6983
  · exact prime_751
  · exact prime_7
  · exact prime_11
  · exact prime_31
  · exact prime_7
  · exact prime_1231
  · exact prime_11
  · exact prime_7
  · exact prime_31
  · exact prime_6803
  · exact prime_7
  · exact prime_3
  · exact prime_3947
  · exact prime_3067
  · exact prime_3
  · exact prime_3187
  · exact prime_10067
  · exact prime_3
  · exact prime_103
  · exact prime_19
  · exact prime_3
  · exact prime_223
  · exact prime_8419
  · exact prime_3
  · exact prime_1367
  · exact prime_9371
  · exact prime_3
  · exact prime_2671
  · exact prime_19
  · exact prime_3
  · exact prime_3911
  · exact prime_2083
  · exact prime_3
  · exact prime_1171
  · exact prime_1823
  · exact prime_3
  · exact prime_5351
  · exact prime_2843
  · exact prime_3
  · exact prime_5923
  · exact prime_5323
  · exact prime_3
  · exact prime_2591
  · exact prime_1531
  · exact prime_3
  · exact prime_2351
  · exact prime_19
  · exact prime_3
  · exact prime_8467
  · exact prime_1223
  · exact prime_3
  · exact prime_3
  · exact prime_23
  · exact prime_1951
  · exact prime_3
  · exact prime_11
  · exact prime_59
  · exact prime_3
  · exact prime_1307
  · exact prime_1951
  · exact prime_3
  · exact prime_9151
  · exact prime_4759
  · exact prime_3
  · exact prime_3251
  · exact prime_11
  · exact prime_3
  · exact prime_1259
  · exact prime_5347
  · exact prime_3
  · exact prime_11
  · cases h_false

lemma blocking_prime_by_idx_44_prime (idx : ℕ) : Nat.Prime (blocking_prime_by_idx_44 idx) :=
  prime_of_mem_blocking_primes_44 (getD_mem blocking_primes_44 (idx - 4400) 3)

lemma mod4_of_mem_blocking_primes_44 {p : ℕ} (h : p ∈ 3 :: blocking_primes_44) : p % 4 = 3 := by
  unfold blocking_primes_44 at h
  simp only [List.mem_cons] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | h_false
  · exact mod4_3
  · exact mod4_31
  · exact mod4_11
  · exact mod4_107
  · exact mod4_7
  · exact mod4_1627
  · exact mod4_11
  · exact mod4_7
  · exact mod4_31
  · exact mod4_10531
  · exact mod4_7
  · exact mod4_11
  · exact mod4_11
  · exact mod4_7
  · exact mod4_139
  · exact mod4_67
  · exact mod4_7
  · exact mod4_11
  · exact mod4_31
  · exact mod4_7
  · exact mod4_43
  · exact mod4_11
  · exact mod4_11
  · exact mod4_31
  · exact mod4_12763
  · exact mod4_7
  · exact mod4_11
  · exact mod4_11
  · exact mod4_7
  · exact mod4_6983
  · exact mod4_751
  · exact mod4_7
  · exact mod4_11
  · exact mod4_31
  · exact mod4_7
  · exact mod4_1231
  · exact mod4_11
  · exact mod4_7
  · exact mod4_31
  · exact mod4_6803
  · exact mod4_7
  · exact mod4_3
  · exact mod4_3947
  · exact mod4_3067
  · exact mod4_3
  · exact mod4_3187
  · exact mod4_10067
  · exact mod4_3
  · exact mod4_103
  · exact mod4_19
  · exact mod4_3
  · exact mod4_223
  · exact mod4_8419
  · exact mod4_3
  · exact mod4_1367
  · exact mod4_9371
  · exact mod4_3
  · exact mod4_2671
  · exact mod4_19
  · exact mod4_3
  · exact mod4_3911
  · exact mod4_2083
  · exact mod4_3
  · exact mod4_1171
  · exact mod4_1823
  · exact mod4_3
  · exact mod4_5351
  · exact mod4_2843
  · exact mod4_3
  · exact mod4_5923
  · exact mod4_5323
  · exact mod4_3
  · exact mod4_2591
  · exact mod4_1531
  · exact mod4_3
  · exact mod4_2351
  · exact mod4_19
  · exact mod4_3
  · exact mod4_8467
  · exact mod4_1223
  · exact mod4_3
  · exact mod4_3
  · exact mod4_23
  · exact mod4_1951
  · exact mod4_3
  · exact mod4_11
  · exact mod4_59
  · exact mod4_3
  · exact mod4_1307
  · exact mod4_1951
  · exact mod4_3
  · exact mod4_9151
  · exact mod4_4759
  · exact mod4_3
  · exact mod4_3251
  · exact mod4_11
  · exact mod4_3
  · exact mod4_1259
  · exact mod4_5347
  · exact mod4_3
  · exact mod4_11
  · cases h_false

lemma blocking_prime_by_idx_44_3mod4 (idx : ℕ) : blocking_prime_by_idx_44 idx % 4 = 3 :=
  mod4_of_mem_blocking_primes_44 (getD_mem blocking_primes_44 (idx - 4400) 3)

def blocking_primes_45 : List ℕ := [1307, 3, 967, 23, 3, 17539, 1759, 3, 103, 11, 3, 4139, 3079, 3, 11, 71, 3, 15647, 9067, 3, 7, 83, 43, 7, 127, 4051, 7, 10739, 2423, 7, 10691, 127, 7, 571, 5419, 7, 43, 1831, 47, 307, 683, 7, 2311, 43, 7, 127, 4567, 7, 1019, 71, 7, 683, 127, 7, 8431, 5419, 7, 43, 2903, 127, 3, 1867, 631, 3, 1187, 983, 3, 17807, 31, 3, 23, 4951, 3, 31, 1151, 3, 2731, 127, 3, 463, 2971, 3, 7039, 31, 3, 431, 12263, 3, 31, 2731, 3, 127, 23, 3, 1283, 307, 3, 59, 31, 3]
def blocking_prime_by_idx_45 (idx : ℕ) : ℕ := blocking_primes_45.getD (idx - 4500) 3

lemma prime_of_mem_blocking_primes_45 {p : ℕ} (h : p ∈ 3 :: blocking_primes_45) : Nat.Prime p := by
  unfold blocking_primes_45 at h
  simp only [List.mem_cons] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | h_false
  · exact prime_3
  · exact prime_1307
  · exact prime_3
  · exact prime_967
  · exact prime_23
  · exact prime_3
  · exact prime_17539
  · exact prime_1759
  · exact prime_3
  · exact prime_103
  · exact prime_11
  · exact prime_3
  · exact prime_4139
  · exact prime_3079
  · exact prime_3
  · exact prime_11
  · exact prime_71
  · exact prime_3
  · exact prime_15647
  · exact prime_9067
  · exact prime_3
  · exact prime_7
  · exact prime_83
  · exact prime_43
  · exact prime_7
  · exact prime_127
  · exact prime_4051
  · exact prime_7
  · exact prime_10739
  · exact prime_2423
  · exact prime_7
  · exact prime_10691
  · exact prime_127
  · exact prime_7
  · exact prime_571
  · exact prime_5419
  · exact prime_7
  · exact prime_43
  · exact prime_1831
  · exact prime_47
  · exact prime_307
  · exact prime_683
  · exact prime_7
  · exact prime_2311
  · exact prime_43
  · exact prime_7
  · exact prime_127
  · exact prime_4567
  · exact prime_7
  · exact prime_1019
  · exact prime_71
  · exact prime_7
  · exact prime_683
  · exact prime_127
  · exact prime_7
  · exact prime_8431
  · exact prime_5419
  · exact prime_7
  · exact prime_43
  · exact prime_2903
  · exact prime_127
  · exact prime_3
  · exact prime_1867
  · exact prime_631
  · exact prime_3
  · exact prime_1187
  · exact prime_983
  · exact prime_3
  · exact prime_17807
  · exact prime_31
  · exact prime_3
  · exact prime_23
  · exact prime_4951
  · exact prime_3
  · exact prime_31
  · exact prime_1151
  · exact prime_3
  · exact prime_2731
  · exact prime_127
  · exact prime_3
  · exact prime_463
  · exact prime_2971
  · exact prime_3
  · exact prime_7039
  · exact prime_31
  · exact prime_3
  · exact prime_431
  · exact prime_12263
  · exact prime_3
  · exact prime_31
  · exact prime_2731
  · exact prime_3
  · exact prime_127
  · exact prime_23
  · exact prime_3
  · exact prime_1283
  · exact prime_307
  · exact prime_3
  · exact prime_59
  · exact prime_31
  · exact prime_3
  · cases h_false

lemma blocking_prime_by_idx_45_prime (idx : ℕ) : Nat.Prime (blocking_prime_by_idx_45 idx) :=
  prime_of_mem_blocking_primes_45 (getD_mem blocking_primes_45 (idx - 4500) 3)

lemma mod4_of_mem_blocking_primes_45 {p : ℕ} (h : p ∈ 3 :: blocking_primes_45) : p % 4 = 3 := by
  unfold blocking_primes_45 at h
  simp only [List.mem_cons] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | h_false
  · exact mod4_3
  · exact mod4_1307
  · exact mod4_3
  · exact mod4_967
  · exact mod4_23
  · exact mod4_3
  · exact mod4_17539
  · exact mod4_1759
  · exact mod4_3
  · exact mod4_103
  · exact mod4_11
  · exact mod4_3
  · exact mod4_4139
  · exact mod4_3079
  · exact mod4_3
  · exact mod4_11
  · exact mod4_71
  · exact mod4_3
  · exact mod4_15647
  · exact mod4_9067
  · exact mod4_3
  · exact mod4_7
  · exact mod4_83
  · exact mod4_43
  · exact mod4_7
  · exact mod4_127
  · exact mod4_4051
  · exact mod4_7
  · exact mod4_10739
  · exact mod4_2423
  · exact mod4_7
  · exact mod4_10691
  · exact mod4_127
  · exact mod4_7
  · exact mod4_571
  · exact mod4_5419
  · exact mod4_7
  · exact mod4_43
  · exact mod4_1831
  · exact mod4_47
  · exact mod4_307
  · exact mod4_683
  · exact mod4_7
  · exact mod4_2311
  · exact mod4_43
  · exact mod4_7
  · exact mod4_127
  · exact mod4_4567
  · exact mod4_7
  · exact mod4_1019
  · exact mod4_71
  · exact mod4_7
  · exact mod4_683
  · exact mod4_127
  · exact mod4_7
  · exact mod4_8431
  · exact mod4_5419
  · exact mod4_7
  · exact mod4_43
  · exact mod4_2903
  · exact mod4_127
  · exact mod4_3
  · exact mod4_1867
  · exact mod4_631
  · exact mod4_3
  · exact mod4_1187
  · exact mod4_983
  · exact mod4_3
  · exact mod4_17807
  · exact mod4_31
  · exact mod4_3
  · exact mod4_23
  · exact mod4_4951
  · exact mod4_3
  · exact mod4_31
  · exact mod4_1151
  · exact mod4_3
  · exact mod4_2731
  · exact mod4_127
  · exact mod4_3
  · exact mod4_463
  · exact mod4_2971
  · exact mod4_3
  · exact mod4_7039
  · exact mod4_31
  · exact mod4_3
  · exact mod4_431
  · exact mod4_12263
  · exact mod4_3
  · exact mod4_31
  · exact mod4_2731
  · exact mod4_3
  · exact mod4_127
  · exact mod4_23
  · exact mod4_3
  · exact mod4_1283
  · exact mod4_307
  · exact mod4_3
  · exact mod4_59
  · exact mod4_31
  · exact mod4_3
  · cases h_false

lemma blocking_prime_by_idx_45_3mod4 (idx : ℕ) : blocking_prime_by_idx_45 idx % 4 = 3 :=
  mod4_of_mem_blocking_primes_45 (getD_mem blocking_primes_45 (idx - 4500) 3)

def blocking_primes_46 : List ℕ := [3, 3803, 31, 3, 2003, 11, 3, 31, 4091, 3, 11, 11, 3, 3391, 7583, 3, 11, 31, 3, 1423, 11, 3, 31, 1543, 3, 11, 11, 3, 23, 4507, 3, 11, 31, 3, 3539, 11, 3, 31, 1019, 3, 7, 307, 2819, 7, 131, 23, 7, 10771, 167, 7, 139, 151, 7, 71, 523, 4643, 23, 47, 7, 47, 67, 7, 6551, 83, 7, 7823, 59, 7, 9587, 1699, 7, 191, 9403, 7, 5659, 211, 5507, 5323, 23, 7, 3, 19759, 47, 3, 11, 43, 3, 11299, 691, 3, 3559, 6091, 3, 6551, 11, 3, 2647, 12343, 3, 11]
def blocking_prime_by_idx_46 (idx : ℕ) : ℕ := blocking_primes_46.getD (idx - 4600) 3

lemma prime_of_mem_blocking_primes_46 {p : ℕ} (h : p ∈ 3 :: blocking_primes_46) : Nat.Prime p := by
  unfold blocking_primes_46 at h
  simp only [List.mem_cons] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | h_false
  · exact prime_3
  · exact prime_3
  · exact prime_3803
  · exact prime_31
  · exact prime_3
  · exact prime_2003
  · exact prime_11
  · exact prime_3
  · exact prime_31
  · exact prime_4091
  · exact prime_3
  · exact prime_11
  · exact prime_11
  · exact prime_3
  · exact prime_3391
  · exact prime_7583
  · exact prime_3
  · exact prime_11
  · exact prime_31
  · exact prime_3
  · exact prime_1423
  · exact prime_11
  · exact prime_3
  · exact prime_31
  · exact prime_1543
  · exact prime_3
  · exact prime_11
  · exact prime_11
  · exact prime_3
  · exact prime_23
  · exact prime_4507
  · exact prime_3
  · exact prime_11
  · exact prime_31
  · exact prime_3
  · exact prime_3539
  · exact prime_11
  · exact prime_3
  · exact prime_31
  · exact prime_1019
  · exact prime_3
  · exact prime_7
  · exact prime_307
  · exact prime_2819
  · exact prime_7
  · exact prime_131
  · exact prime_23
  · exact prime_7
  · exact prime_10771
  · exact prime_167
  · exact prime_7
  · exact prime_139
  · exact prime_151
  · exact prime_7
  · exact prime_71
  · exact prime_523
  · exact prime_4643
  · exact prime_23
  · exact prime_47
  · exact prime_7
  · exact prime_47
  · exact prime_67
  · exact prime_7
  · exact prime_6551
  · exact prime_83
  · exact prime_7
  · exact prime_7823
  · exact prime_59
  · exact prime_7
  · exact prime_9587
  · exact prime_1699
  · exact prime_7
  · exact prime_191
  · exact prime_9403
  · exact prime_7
  · exact prime_5659
  · exact prime_211
  · exact prime_5507
  · exact prime_5323
  · exact prime_23
  · exact prime_7
  · exact prime_3
  · exact prime_19759
  · exact prime_47
  · exact prime_3
  · exact prime_11
  · exact prime_43
  · exact prime_3
  · exact prime_11299
  · exact prime_691
  · exact prime_3
  · exact prime_3559
  · exact prime_6091
  · exact prime_3
  · exact prime_6551
  · exact prime_11
  · exact prime_3
  · exact prime_2647
  · exact prime_12343
  · exact prime_3
  · exact prime_11
  · cases h_false

lemma blocking_prime_by_idx_46_prime (idx : ℕ) : Nat.Prime (blocking_prime_by_idx_46 idx) :=
  prime_of_mem_blocking_primes_46 (getD_mem blocking_primes_46 (idx - 4600) 3)

lemma mod4_of_mem_blocking_primes_46 {p : ℕ} (h : p ∈ 3 :: blocking_primes_46) : p % 4 = 3 := by
  unfold blocking_primes_46 at h
  simp only [List.mem_cons] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | h_false
  · exact mod4_3
  · exact mod4_3
  · exact mod4_3803
  · exact mod4_31
  · exact mod4_3
  · exact mod4_2003
  · exact mod4_11
  · exact mod4_3
  · exact mod4_31
  · exact mod4_4091
  · exact mod4_3
  · exact mod4_11
  · exact mod4_11
  · exact mod4_3
  · exact mod4_3391
  · exact mod4_7583
  · exact mod4_3
  · exact mod4_11
  · exact mod4_31
  · exact mod4_3
  · exact mod4_1423
  · exact mod4_11
  · exact mod4_3
  · exact mod4_31
  · exact mod4_1543
  · exact mod4_3
  · exact mod4_11
  · exact mod4_11
  · exact mod4_3
  · exact mod4_23
  · exact mod4_4507
  · exact mod4_3
  · exact mod4_11
  · exact mod4_31
  · exact mod4_3
  · exact mod4_3539
  · exact mod4_11
  · exact mod4_3
  · exact mod4_31
  · exact mod4_1019
  · exact mod4_3
  · exact mod4_7
  · exact mod4_307
  · exact mod4_2819
  · exact mod4_7
  · exact mod4_131
  · exact mod4_23
  · exact mod4_7
  · exact mod4_10771
  · exact mod4_167
  · exact mod4_7
  · exact mod4_139
  · exact mod4_151
  · exact mod4_7
  · exact mod4_71
  · exact mod4_523
  · exact mod4_4643
  · exact mod4_23
  · exact mod4_47
  · exact mod4_7
  · exact mod4_47
  · exact mod4_67
  · exact mod4_7
  · exact mod4_6551
  · exact mod4_83
  · exact mod4_7
  · exact mod4_7823
  · exact mod4_59
  · exact mod4_7
  · exact mod4_9587
  · exact mod4_1699
  · exact mod4_7
  · exact mod4_191
  · exact mod4_9403
  · exact mod4_7
  · exact mod4_5659
  · exact mod4_211
  · exact mod4_5507
  · exact mod4_5323
  · exact mod4_23
  · exact mod4_7
  · exact mod4_3
  · exact mod4_19759
  · exact mod4_47
  · exact mod4_3
  · exact mod4_11
  · exact mod4_43
  · exact mod4_3
  · exact mod4_11299
  · exact mod4_691
  · exact mod4_3
  · exact mod4_3559
  · exact mod4_6091
  · exact mod4_3
  · exact mod4_6551
  · exact mod4_11
  · exact mod4_3
  · exact mod4_2647
  · exact mod4_12343
  · exact mod4_3
  · exact mod4_11
  · cases h_false

lemma blocking_prime_by_idx_46_3mod4 (idx : ℕ) : blocking_prime_by_idx_46 idx % 4 = 3 :=
  mod4_of_mem_blocking_primes_46 (getD_mem blocking_primes_46 (idx - 4600) 3)

def blocking_primes_47 : List ℕ := [8123, 3, 9343, 103, 3, 47, 43, 3, 4919, 11, 3, 167, 3343, 3, 11, 5527, 3, 6907, 727, 3, 3, 19, 911, 3, 5563, 2131, 3, 8191, 103, 3, 19, 10079, 3, 7243, 971, 3, 7027, 2179, 3, 19, 8191, 3, 7607, 71, 3, 6359, 9439, 3, 19, 487, 3, 8867, 863, 3, 983, 83, 3, 19, 7523, 3, 7, 59, 883, 7, 5879, 463, 7, 211, 31, 7, 6043, 7723, 839, 31, 9319, 7, 5171, 1543, 7, 8191, 6571, 7, 11027, 31, 7, 8011, 6203, 7, 31, 14303, 7, 83, 8191, 31, 9511, 359, 7, 107, 31, 7]
def blocking_prime_by_idx_47 (idx : ℕ) : ℕ := blocking_primes_47.getD (idx - 4700) 3

lemma prime_of_mem_blocking_primes_47 {p : ℕ} (h : p ∈ 3 :: blocking_primes_47) : Nat.Prime p := by
  unfold blocking_primes_47 at h
  simp only [List.mem_cons] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | h_false
  · exact prime_3
  · exact prime_8123
  · exact prime_3
  · exact prime_9343
  · exact prime_103
  · exact prime_3
  · exact prime_47
  · exact prime_43
  · exact prime_3
  · exact prime_4919
  · exact prime_11
  · exact prime_3
  · exact prime_167
  · exact prime_3343
  · exact prime_3
  · exact prime_11
  · exact prime_5527
  · exact prime_3
  · exact prime_6907
  · exact prime_727
  · exact prime_3
  · exact prime_3
  · exact prime_19
  · exact prime_911
  · exact prime_3
  · exact prime_5563
  · exact prime_2131
  · exact prime_3
  · exact prime_8191
  · exact prime_103
  · exact prime_3
  · exact prime_19
  · exact prime_10079
  · exact prime_3
  · exact prime_7243
  · exact prime_971
  · exact prime_3
  · exact prime_7027
  · exact prime_2179
  · exact prime_3
  · exact prime_19
  · exact prime_8191
  · exact prime_3
  · exact prime_7607
  · exact prime_71
  · exact prime_3
  · exact prime_6359
  · exact prime_9439
  · exact prime_3
  · exact prime_19
  · exact prime_487
  · exact prime_3
  · exact prime_8867
  · exact prime_863
  · exact prime_3
  · exact prime_983
  · exact prime_83
  · exact prime_3
  · exact prime_19
  · exact prime_7523
  · exact prime_3
  · exact prime_7
  · exact prime_59
  · exact prime_883
  · exact prime_7
  · exact prime_5879
  · exact prime_463
  · exact prime_7
  · exact prime_211
  · exact prime_31
  · exact prime_7
  · exact prime_6043
  · exact prime_7723
  · exact prime_839
  · exact prime_31
  · exact prime_9319
  · exact prime_7
  · exact prime_5171
  · exact prime_1543
  · exact prime_7
  · exact prime_8191
  · exact prime_6571
  · exact prime_7
  · exact prime_11027
  · exact prime_31
  · exact prime_7
  · exact prime_8011
  · exact prime_6203
  · exact prime_7
  · exact prime_31
  · exact prime_14303
  · exact prime_7
  · exact prime_83
  · exact prime_8191
  · exact prime_31
  · exact prime_9511
  · exact prime_359
  · exact prime_7
  · exact prime_107
  · exact prime_31
  · exact prime_7
  · cases h_false

lemma blocking_prime_by_idx_47_prime (idx : ℕ) : Nat.Prime (blocking_prime_by_idx_47 idx) :=
  prime_of_mem_blocking_primes_47 (getD_mem blocking_primes_47 (idx - 4700) 3)

lemma mod4_of_mem_blocking_primes_47 {p : ℕ} (h : p ∈ 3 :: blocking_primes_47) : p % 4 = 3 := by
  unfold blocking_primes_47 at h
  simp only [List.mem_cons] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | h_false
  · exact mod4_3
  · exact mod4_8123
  · exact mod4_3
  · exact mod4_9343
  · exact mod4_103
  · exact mod4_3
  · exact mod4_47
  · exact mod4_43
  · exact mod4_3
  · exact mod4_4919
  · exact mod4_11
  · exact mod4_3
  · exact mod4_167
  · exact mod4_3343
  · exact mod4_3
  · exact mod4_11
  · exact mod4_5527
  · exact mod4_3
  · exact mod4_6907
  · exact mod4_727
  · exact mod4_3
  · exact mod4_3
  · exact mod4_19
  · exact mod4_911
  · exact mod4_3
  · exact mod4_5563
  · exact mod4_2131
  · exact mod4_3
  · exact mod4_8191
  · exact mod4_103
  · exact mod4_3
  · exact mod4_19
  · exact mod4_10079
  · exact mod4_3
  · exact mod4_7243
  · exact mod4_971
  · exact mod4_3
  · exact mod4_7027
  · exact mod4_2179
  · exact mod4_3
  · exact mod4_19
  · exact mod4_8191
  · exact mod4_3
  · exact mod4_7607
  · exact mod4_71
  · exact mod4_3
  · exact mod4_6359
  · exact mod4_9439
  · exact mod4_3
  · exact mod4_19
  · exact mod4_487
  · exact mod4_3
  · exact mod4_8867
  · exact mod4_863
  · exact mod4_3
  · exact mod4_983
  · exact mod4_83
  · exact mod4_3
  · exact mod4_19
  · exact mod4_7523
  · exact mod4_3
  · exact mod4_7
  · exact mod4_59
  · exact mod4_883
  · exact mod4_7
  · exact mod4_5879
  · exact mod4_463
  · exact mod4_7
  · exact mod4_211
  · exact mod4_31
  · exact mod4_7
  · exact mod4_6043
  · exact mod4_7723
  · exact mod4_839
  · exact mod4_31
  · exact mod4_9319
  · exact mod4_7
  · exact mod4_5171
  · exact mod4_1543
  · exact mod4_7
  · exact mod4_8191
  · exact mod4_6571
  · exact mod4_7
  · exact mod4_11027
  · exact mod4_31
  · exact mod4_7
  · exact mod4_8011
  · exact mod4_6203
  · exact mod4_7
  · exact mod4_31
  · exact mod4_14303
  · exact mod4_7
  · exact mod4_83
  · exact mod4_8191
  · exact mod4_31
  · exact mod4_9511
  · exact mod4_359
  · exact mod4_7
  · exact mod4_107
  · exact mod4_31
  · exact mod4_7
  · cases h_false

lemma blocking_prime_by_idx_47_3mod4 (idx : ℕ) : blocking_prime_by_idx_47 idx % 4 = 3 :=
  mod4_of_mem_blocking_primes_47 (getD_mem blocking_primes_47 (idx - 4700) 3)

def blocking_primes_48 : List ℕ := [3, 11, 31, 3, 127, 11, 3, 31, 19, 3, 11, 11, 3, 683, 10243, 3, 43, 19, 3, 19759, 11, 3, 10567, 43, 3, 11, 11, 3, 5419, 103, 3, 11, 31, 3, 131, 11, 3, 31, 239, 3, 3, 331, 4967, 3, 3463, 83, 3, 4943, 1847, 3, 127, 67, 3, 2207, 8527, 3, 331, 127, 3, 9007, 17327, 3, 6763, 619, 3, 12763, 211, 3, 59, 191, 3, 127, 1283, 3, 163, 4987, 3, 8087, 59, 3, 7, 79, 3343, 7, 11, 11279, 7, 1303, 4231, 11, 4663, 5479, 7, 8803, 11, 7, 3931, 107, 7, 11]
def blocking_prime_by_idx_48 (idx : ℕ) : ℕ := blocking_primes_48.getD (idx - 4800) 3

lemma prime_of_mem_blocking_primes_48 {p : ℕ} (h : p ∈ 3 :: blocking_primes_48) : Nat.Prime p := by
  unfold blocking_primes_48 at h
  simp only [List.mem_cons] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | h_false
  · exact prime_3
  · exact prime_3
  · exact prime_11
  · exact prime_31
  · exact prime_3
  · exact prime_127
  · exact prime_11
  · exact prime_3
  · exact prime_31
  · exact prime_19
  · exact prime_3
  · exact prime_11
  · exact prime_11
  · exact prime_3
  · exact prime_683
  · exact prime_10243
  · exact prime_3
  · exact prime_43
  · exact prime_19
  · exact prime_3
  · exact prime_19759
  · exact prime_11
  · exact prime_3
  · exact prime_10567
  · exact prime_43
  · exact prime_3
  · exact prime_11
  · exact prime_11
  · exact prime_3
  · exact prime_5419
  · exact prime_103
  · exact prime_3
  · exact prime_11
  · exact prime_31
  · exact prime_3
  · exact prime_131
  · exact prime_11
  · exact prime_3
  · exact prime_31
  · exact prime_239
  · exact prime_3
  · exact prime_3
  · exact prime_331
  · exact prime_4967
  · exact prime_3
  · exact prime_3463
  · exact prime_83
  · exact prime_3
  · exact prime_4943
  · exact prime_1847
  · exact prime_3
  · exact prime_127
  · exact prime_67
  · exact prime_3
  · exact prime_2207
  · exact prime_8527
  · exact prime_3
  · exact prime_331
  · exact prime_127
  · exact prime_3
  · exact prime_9007
  · exact prime_17327
  · exact prime_3
  · exact prime_6763
  · exact prime_619
  · exact prime_3
  · exact prime_12763
  · exact prime_211
  · exact prime_3
  · exact prime_59
  · exact prime_191
  · exact prime_3
  · exact prime_127
  · exact prime_1283
  · exact prime_3
  · exact prime_163
  · exact prime_4987
  · exact prime_3
  · exact prime_8087
  · exact prime_59
  · exact prime_3
  · exact prime_7
  · exact prime_79
  · exact prime_3343
  · exact prime_7
  · exact prime_11
  · exact prime_11279
  · exact prime_7
  · exact prime_1303
  · exact prime_4231
  · exact prime_11
  · exact prime_4663
  · exact prime_5479
  · exact prime_7
  · exact prime_8803
  · exact prime_11
  · exact prime_7
  · exact prime_3931
  · exact prime_107
  · exact prime_7
  · exact prime_11
  · cases h_false

lemma blocking_prime_by_idx_48_prime (idx : ℕ) : Nat.Prime (blocking_prime_by_idx_48 idx) :=
  prime_of_mem_blocking_primes_48 (getD_mem blocking_primes_48 (idx - 4800) 3)

lemma mod4_of_mem_blocking_primes_48 {p : ℕ} (h : p ∈ 3 :: blocking_primes_48) : p % 4 = 3 := by
  unfold blocking_primes_48 at h
  simp only [List.mem_cons] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | h_false
  · exact mod4_3
  · exact mod4_3
  · exact mod4_11
  · exact mod4_31
  · exact mod4_3
  · exact mod4_127
  · exact mod4_11
  · exact mod4_3
  · exact mod4_31
  · exact mod4_19
  · exact mod4_3
  · exact mod4_11
  · exact mod4_11
  · exact mod4_3
  · exact mod4_683
  · exact mod4_10243
  · exact mod4_3
  · exact mod4_43
  · exact mod4_19
  · exact mod4_3
  · exact mod4_19759
  · exact mod4_11
  · exact mod4_3
  · exact mod4_10567
  · exact mod4_43
  · exact mod4_3
  · exact mod4_11
  · exact mod4_11
  · exact mod4_3
  · exact mod4_5419
  · exact mod4_103
  · exact mod4_3
  · exact mod4_11
  · exact mod4_31
  · exact mod4_3
  · exact mod4_131
  · exact mod4_11
  · exact mod4_3
  · exact mod4_31
  · exact mod4_239
  · exact mod4_3
  · exact mod4_3
  · exact mod4_331
  · exact mod4_4967
  · exact mod4_3
  · exact mod4_3463
  · exact mod4_83
  · exact mod4_3
  · exact mod4_4943
  · exact mod4_1847
  · exact mod4_3
  · exact mod4_127
  · exact mod4_67
  · exact mod4_3
  · exact mod4_2207
  · exact mod4_8527
  · exact mod4_3
  · exact mod4_331
  · exact mod4_127
  · exact mod4_3
  · exact mod4_9007
  · exact mod4_17327
  · exact mod4_3
  · exact mod4_6763
  · exact mod4_619
  · exact mod4_3
  · exact mod4_12763
  · exact mod4_211
  · exact mod4_3
  · exact mod4_59
  · exact mod4_191
  · exact mod4_3
  · exact mod4_127
  · exact mod4_1283
  · exact mod4_3
  · exact mod4_163
  · exact mod4_4987
  · exact mod4_3
  · exact mod4_8087
  · exact mod4_59
  · exact mod4_3
  · exact mod4_7
  · exact mod4_79
  · exact mod4_3343
  · exact mod4_7
  · exact mod4_11
  · exact mod4_11279
  · exact mod4_7
  · exact mod4_1303
  · exact mod4_4231
  · exact mod4_11
  · exact mod4_4663
  · exact mod4_5479
  · exact mod4_7
  · exact mod4_8803
  · exact mod4_11
  · exact mod4_7
  · exact mod4_3931
  · exact mod4_107
  · exact mod4_7
  · exact mod4_11
  · cases h_false

lemma blocking_prime_by_idx_48_3mod4 (idx : ℕ) : blocking_prime_by_idx_48 idx % 4 = 3 :=
  mod4_of_mem_blocking_primes_48 (getD_mem blocking_primes_48 (idx - 4800) 3)

def blocking_primes_49 : List ℕ := [191, 7, 59, 2659, 7, 1123, 1259, 7, 5683, 11, 15443, 499, 11351, 7, 11, 7247, 7, 3571, 359, 7, 3, 2999, 59, 3, 83, 8807, 3, 4919, 1103, 3, 823, 4327, 3, 67, 331, 3, 6563, 12203, 3, 151, 4051, 3, 7307, 23, 3, 3011, 15107, 3, 6967, 331, 3, 59, 4691, 3, 23, 1063, 3, 1103, 563, 3, 3, 227, 8623, 3, 619, 43, 3, 4451, 31, 3, 619, 9491, 3, 31, 9787, 3, 227, 9679, 3, 43, 683, 3, 823, 31, 3, 9283, 43, 3, 31, 5231, 3, 683, 163, 3, 5003, 131, 3, 1123, 31, 3]
def blocking_prime_by_idx_49 (idx : ℕ) : ℕ := blocking_primes_49.getD (idx - 4900) 3

lemma prime_of_mem_blocking_primes_49 {p : ℕ} (h : p ∈ 3 :: blocking_primes_49) : Nat.Prime p := by
  unfold blocking_primes_49 at h
  simp only [List.mem_cons] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | h_false
  · exact prime_3
  · exact prime_191
  · exact prime_7
  · exact prime_59
  · exact prime_2659
  · exact prime_7
  · exact prime_1123
  · exact prime_1259
  · exact prime_7
  · exact prime_5683
  · exact prime_11
  · exact prime_15443
  · exact prime_499
  · exact prime_11351
  · exact prime_7
  · exact prime_11
  · exact prime_7247
  · exact prime_7
  · exact prime_3571
  · exact prime_359
  · exact prime_7
  · exact prime_3
  · exact prime_2999
  · exact prime_59
  · exact prime_3
  · exact prime_83
  · exact prime_8807
  · exact prime_3
  · exact prime_4919
  · exact prime_1103
  · exact prime_3
  · exact prime_823
  · exact prime_4327
  · exact prime_3
  · exact prime_67
  · exact prime_331
  · exact prime_3
  · exact prime_6563
  · exact prime_12203
  · exact prime_3
  · exact prime_151
  · exact prime_4051
  · exact prime_3
  · exact prime_7307
  · exact prime_23
  · exact prime_3
  · exact prime_3011
  · exact prime_15107
  · exact prime_3
  · exact prime_6967
  · exact prime_331
  · exact prime_3
  · exact prime_59
  · exact prime_4691
  · exact prime_3
  · exact prime_23
  · exact prime_1063
  · exact prime_3
  · exact prime_1103
  · exact prime_563
  · exact prime_3
  · exact prime_3
  · exact prime_227
  · exact prime_8623
  · exact prime_3
  · exact prime_619
  · exact prime_43
  · exact prime_3
  · exact prime_4451
  · exact prime_31
  · exact prime_3
  · exact prime_619
  · exact prime_9491
  · exact prime_3
  · exact prime_31
  · exact prime_9787
  · exact prime_3
  · exact prime_227
  · exact prime_9679
  · exact prime_3
  · exact prime_43
  · exact prime_683
  · exact prime_3
  · exact prime_823
  · exact prime_31
  · exact prime_3
  · exact prime_9283
  · exact prime_43
  · exact prime_3
  · exact prime_31
  · exact prime_5231
  · exact prime_3
  · exact prime_683
  · exact prime_163
  · exact prime_3
  · exact prime_5003
  · exact prime_131
  · exact prime_3
  · exact prime_1123
  · exact prime_31
  · exact prime_3
  · cases h_false

lemma blocking_prime_by_idx_49_prime (idx : ℕ) : Nat.Prime (blocking_prime_by_idx_49 idx) :=
  prime_of_mem_blocking_primes_49 (getD_mem blocking_primes_49 (idx - 4900) 3)

lemma mod4_of_mem_blocking_primes_49 {p : ℕ} (h : p ∈ 3 :: blocking_primes_49) : p % 4 = 3 := by
  unfold blocking_primes_49 at h
  simp only [List.mem_cons] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | h_false
  · exact mod4_3
  · exact mod4_191
  · exact mod4_7
  · exact mod4_59
  · exact mod4_2659
  · exact mod4_7
  · exact mod4_1123
  · exact mod4_1259
  · exact mod4_7
  · exact mod4_5683
  · exact mod4_11
  · exact mod4_15443
  · exact mod4_499
  · exact mod4_11351
  · exact mod4_7
  · exact mod4_11
  · exact mod4_7247
  · exact mod4_7
  · exact mod4_3571
  · exact mod4_359
  · exact mod4_7
  · exact mod4_3
  · exact mod4_2999
  · exact mod4_59
  · exact mod4_3
  · exact mod4_83
  · exact mod4_8807
  · exact mod4_3
  · exact mod4_4919
  · exact mod4_1103
  · exact mod4_3
  · exact mod4_823
  · exact mod4_4327
  · exact mod4_3
  · exact mod4_67
  · exact mod4_331
  · exact mod4_3
  · exact mod4_6563
  · exact mod4_12203
  · exact mod4_3
  · exact mod4_151
  · exact mod4_4051
  · exact mod4_3
  · exact mod4_7307
  · exact mod4_23
  · exact mod4_3
  · exact mod4_3011
  · exact mod4_15107
  · exact mod4_3
  · exact mod4_6967
  · exact mod4_331
  · exact mod4_3
  · exact mod4_59
  · exact mod4_4691
  · exact mod4_3
  · exact mod4_23
  · exact mod4_1063
  · exact mod4_3
  · exact mod4_1103
  · exact mod4_563
  · exact mod4_3
  · exact mod4_3
  · exact mod4_227
  · exact mod4_8623
  · exact mod4_3
  · exact mod4_619
  · exact mod4_43
  · exact mod4_3
  · exact mod4_4451
  · exact mod4_31
  · exact mod4_3
  · exact mod4_619
  · exact mod4_9491
  · exact mod4_3
  · exact mod4_31
  · exact mod4_9787
  · exact mod4_3
  · exact mod4_227
  · exact mod4_9679
  · exact mod4_3
  · exact mod4_43
  · exact mod4_683
  · exact mod4_3
  · exact mod4_823
  · exact mod4_31
  · exact mod4_3
  · exact mod4_9283
  · exact mod4_43
  · exact mod4_3
  · exact mod4_31
  · exact mod4_5231
  · exact mod4_3
  · exact mod4_683
  · exact mod4_163
  · exact mod4_3
  · exact mod4_5003
  · exact mod4_131
  · exact mod4_3
  · exact mod4_1123
  · exact mod4_31
  · exact mod4_3
  · cases h_false

lemma blocking_prime_by_idx_49_3mod4 (idx : ℕ) : blocking_prime_by_idx_49 idx % 4 = 3 :=
  mod4_of_mem_blocking_primes_49 (getD_mem blocking_primes_49 (idx - 4900) 3)

def blocking_primes_50 : List ℕ := [7, 11, 31, 7, 4999, 11, 11, 31, 3299, 7, 11, 11, 7, 1723, 2663, 7, 11, 31, 7, 9539, 11, 7, 31, 3019, 7, 11, 11, 31, 11287, 3023, 7, 3847, 23, 7, 4723, 11, 7, 31, 1459, 7, 3, 1307, 12379, 3, 5227, 47, 3, 79, 2039, 3, 9619, 23, 3, 8563, 5519, 3, 199, 23, 3, 2099, 1487, 3, 23, 787, 3, 3671, 2339, 3, 23, 983, 3, 14627, 211, 3, 5839, 15991, 3, 2999, 5659, 3, 3, 19, 43, 3, 11, 23, 3, 167, 11491, 3, 19, 127, 3, 911, 11, 3, 23, 2551, 3, 11]
def blocking_prime_by_idx_50 (idx : ℕ) : ℕ := blocking_primes_50.getD (idx - 5000) 3

lemma prime_of_mem_blocking_primes_50 {p : ℕ} (h : p ∈ 3 :: blocking_primes_50) : Nat.Prime p := by
  unfold blocking_primes_50 at h
  simp only [List.mem_cons] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | h_false
  · exact prime_3
  · exact prime_7
  · exact prime_11
  · exact prime_31
  · exact prime_7
  · exact prime_4999
  · exact prime_11
  · exact prime_11
  · exact prime_31
  · exact prime_3299
  · exact prime_7
  · exact prime_11
  · exact prime_11
  · exact prime_7
  · exact prime_1723
  · exact prime_2663
  · exact prime_7
  · exact prime_11
  · exact prime_31
  · exact prime_7
  · exact prime_9539
  · exact prime_11
  · exact prime_7
  · exact prime_31
  · exact prime_3019
  · exact prime_7
  · exact prime_11
  · exact prime_11
  · exact prime_31
  · exact prime_11287
  · exact prime_3023
  · exact prime_7
  · exact prime_3847
  · exact prime_23
  · exact prime_7
  · exact prime_4723
  · exact prime_11
  · exact prime_7
  · exact prime_31
  · exact prime_1459
  · exact prime_7
  · exact prime_3
  · exact prime_1307
  · exact prime_12379
  · exact prime_3
  · exact prime_5227
  · exact prime_47
  · exact prime_3
  · exact prime_79
  · exact prime_2039
  · exact prime_3
  · exact prime_9619
  · exact prime_23
  · exact prime_3
  · exact prime_8563
  · exact prime_5519
  · exact prime_3
  · exact prime_199
  · exact prime_23
  · exact prime_3
  · exact prime_2099
  · exact prime_1487
  · exact prime_3
  · exact prime_23
  · exact prime_787
  · exact prime_3
  · exact prime_3671
  · exact prime_2339
  · exact prime_3
  · exact prime_23
  · exact prime_983
  · exact prime_3
  · exact prime_14627
  · exact prime_211
  · exact prime_3
  · exact prime_5839
  · exact prime_15991
  · exact prime_3
  · exact prime_2999
  · exact prime_5659
  · exact prime_3
  · exact prime_3
  · exact prime_19
  · exact prime_43
  · exact prime_3
  · exact prime_11
  · exact prime_23
  · exact prime_3
  · exact prime_167
  · exact prime_11491
  · exact prime_3
  · exact prime_19
  · exact prime_127
  · exact prime_3
  · exact prime_911
  · exact prime_11
  · exact prime_3
  · exact prime_23
  · exact prime_2551
  · exact prime_3
  · exact prime_11
  · cases h_false

lemma blocking_prime_by_idx_50_prime (idx : ℕ) : Nat.Prime (blocking_prime_by_idx_50 idx) :=
  prime_of_mem_blocking_primes_50 (getD_mem blocking_primes_50 (idx - 5000) 3)

lemma mod4_of_mem_blocking_primes_50 {p : ℕ} (h : p ∈ 3 :: blocking_primes_50) : p % 4 = 3 := by
  unfold blocking_primes_50 at h
  simp only [List.mem_cons] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | h_false
  · exact mod4_3
  · exact mod4_7
  · exact mod4_11
  · exact mod4_31
  · exact mod4_7
  · exact mod4_4999
  · exact mod4_11
  · exact mod4_11
  · exact mod4_31
  · exact mod4_3299
  · exact mod4_7
  · exact mod4_11
  · exact mod4_11
  · exact mod4_7
  · exact mod4_1723
  · exact mod4_2663
  · exact mod4_7
  · exact mod4_11
  · exact mod4_31
  · exact mod4_7
  · exact mod4_9539
  · exact mod4_11
  · exact mod4_7
  · exact mod4_31
  · exact mod4_3019
  · exact mod4_7
  · exact mod4_11
  · exact mod4_11
  · exact mod4_31
  · exact mod4_11287
  · exact mod4_3023
  · exact mod4_7
  · exact mod4_3847
  · exact mod4_23
  · exact mod4_7
  · exact mod4_4723
  · exact mod4_11
  · exact mod4_7
  · exact mod4_31
  · exact mod4_1459
  · exact mod4_7
  · exact mod4_3
  · exact mod4_1307
  · exact mod4_12379
  · exact mod4_3
  · exact mod4_5227
  · exact mod4_47
  · exact mod4_3
  · exact mod4_79
  · exact mod4_2039
  · exact mod4_3
  · exact mod4_9619
  · exact mod4_23
  · exact mod4_3
  · exact mod4_8563
  · exact mod4_5519
  · exact mod4_3
  · exact mod4_199
  · exact mod4_23
  · exact mod4_3
  · exact mod4_2099
  · exact mod4_1487
  · exact mod4_3
  · exact mod4_23
  · exact mod4_787
  · exact mod4_3
  · exact mod4_3671
  · exact mod4_2339
  · exact mod4_3
  · exact mod4_23
  · exact mod4_983
  · exact mod4_3
  · exact mod4_14627
  · exact mod4_211
  · exact mod4_3
  · exact mod4_5839
  · exact mod4_15991
  · exact mod4_3
  · exact mod4_2999
  · exact mod4_5659
  · exact mod4_3
  · exact mod4_3
  · exact mod4_19
  · exact mod4_43
  · exact mod4_3
  · exact mod4_11
  · exact mod4_23
  · exact mod4_3
  · exact mod4_167
  · exact mod4_11491
  · exact mod4_3
  · exact mod4_19
  · exact mod4_127
  · exact mod4_3
  · exact mod4_911
  · exact mod4_11
  · exact mod4_3
  · exact mod4_23
  · exact mod4_2551
  · exact mod4_3
  · exact mod4_11
  · cases h_false

lemma blocking_prime_by_idx_50_3mod4 (idx : ℕ) : blocking_prime_by_idx_50 idx % 4 = 3 :=
  mod4_of_mem_blocking_primes_50 (getD_mem blocking_primes_50 (idx - 5000) 3)

def blocking_primes_51 : List ℕ := [311, 3, 103, 43, 3, 127, 659, 3, 13691, 11, 3, 7451, 127, 3, 331, 3191, 3, 19, 23, 3, 7, 8387, 227, 127, 107, 2711, 7, 7879, 4283, 7, 127, 1979, 7, 179, 11131, 7, 3719, 127, 7, 4931, 1583, 7, 5003, 9811, 127, 487, 1091, 7, 523, 1499, 7, 127, 479, 7, 2683, 3947, 7, 1051, 127, 7, 3, 11119, 9623, 3, 7127, 7159, 3, 71, 19, 3, 1031, 1867, 3, 31, 1091, 3, 4547, 19, 3, 587, 6143, 3, 2371, 9719, 3, 6871, 19, 3, 31, 1487, 3, 3323, 2239, 3, 4451, 19, 3, 1663, 31, 3]
def blocking_prime_by_idx_51 (idx : ℕ) : ℕ := blocking_primes_51.getD (idx - 5100) 3

lemma prime_of_mem_blocking_primes_51 {p : ℕ} (h : p ∈ 3 :: blocking_primes_51) : Nat.Prime p := by
  unfold blocking_primes_51 at h
  simp only [List.mem_cons] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | h_false
  · exact prime_3
  · exact prime_311
  · exact prime_3
  · exact prime_103
  · exact prime_43
  · exact prime_3
  · exact prime_127
  · exact prime_659
  · exact prime_3
  · exact prime_13691
  · exact prime_11
  · exact prime_3
  · exact prime_7451
  · exact prime_127
  · exact prime_3
  · exact prime_331
  · exact prime_3191
  · exact prime_3
  · exact prime_19
  · exact prime_23
  · exact prime_3
  · exact prime_7
  · exact prime_8387
  · exact prime_227
  · exact prime_127
  · exact prime_107
  · exact prime_2711
  · exact prime_7
  · exact prime_7879
  · exact prime_4283
  · exact prime_7
  · exact prime_127
  · exact prime_1979
  · exact prime_7
  · exact prime_179
  · exact prime_11131
  · exact prime_7
  · exact prime_3719
  · exact prime_127
  · exact prime_7
  · exact prime_4931
  · exact prime_1583
  · exact prime_7
  · exact prime_5003
  · exact prime_9811
  · exact prime_127
  · exact prime_487
  · exact prime_1091
  · exact prime_7
  · exact prime_523
  · exact prime_1499
  · exact prime_7
  · exact prime_127
  · exact prime_479
  · exact prime_7
  · exact prime_2683
  · exact prime_3947
  · exact prime_7
  · exact prime_1051
  · exact prime_127
  · exact prime_7
  · exact prime_3
  · exact prime_11119
  · exact prime_9623
  · exact prime_3
  · exact prime_7127
  · exact prime_7159
  · exact prime_3
  · exact prime_71
  · exact prime_19
  · exact prime_3
  · exact prime_1031
  · exact prime_1867
  · exact prime_3
  · exact prime_31
  · exact prime_1091
  · exact prime_3
  · exact prime_4547
  · exact prime_19
  · exact prime_3
  · exact prime_587
  · exact prime_6143
  · exact prime_3
  · exact prime_2371
  · exact prime_9719
  · exact prime_3
  · exact prime_6871
  · exact prime_19
  · exact prime_3
  · exact prime_31
  · exact prime_1487
  · exact prime_3
  · exact prime_3323
  · exact prime_2239
  · exact prime_3
  · exact prime_4451
  · exact prime_19
  · exact prime_3
  · exact prime_1663
  · exact prime_31
  · exact prime_3
  · cases h_false

lemma blocking_prime_by_idx_51_prime (idx : ℕ) : Nat.Prime (blocking_prime_by_idx_51 idx) :=
  prime_of_mem_blocking_primes_51 (getD_mem blocking_primes_51 (idx - 5100) 3)

lemma mod4_of_mem_blocking_primes_51 {p : ℕ} (h : p ∈ 3 :: blocking_primes_51) : p % 4 = 3 := by
  unfold blocking_primes_51 at h
  simp only [List.mem_cons] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | h_false
  · exact mod4_3
  · exact mod4_311
  · exact mod4_3
  · exact mod4_103
  · exact mod4_43
  · exact mod4_3
  · exact mod4_127
  · exact mod4_659
  · exact mod4_3
  · exact mod4_13691
  · exact mod4_11
  · exact mod4_3
  · exact mod4_7451
  · exact mod4_127
  · exact mod4_3
  · exact mod4_331
  · exact mod4_3191
  · exact mod4_3
  · exact mod4_19
  · exact mod4_23
  · exact mod4_3
  · exact mod4_7
  · exact mod4_8387
  · exact mod4_227
  · exact mod4_127
  · exact mod4_107
  · exact mod4_2711
  · exact mod4_7
  · exact mod4_7879
  · exact mod4_4283
  · exact mod4_7
  · exact mod4_127
  · exact mod4_1979
  · exact mod4_7
  · exact mod4_179
  · exact mod4_11131
  · exact mod4_7
  · exact mod4_3719
  · exact mod4_127
  · exact mod4_7
  · exact mod4_4931
  · exact mod4_1583
  · exact mod4_7
  · exact mod4_5003
  · exact mod4_9811
  · exact mod4_127
  · exact mod4_487
  · exact mod4_1091
  · exact mod4_7
  · exact mod4_523
  · exact mod4_1499
  · exact mod4_7
  · exact mod4_127
  · exact mod4_479
  · exact mod4_7
  · exact mod4_2683
  · exact mod4_3947
  · exact mod4_7
  · exact mod4_1051
  · exact mod4_127
  · exact mod4_7
  · exact mod4_3
  · exact mod4_11119
  · exact mod4_9623
  · exact mod4_3
  · exact mod4_7127
  · exact mod4_7159
  · exact mod4_3
  · exact mod4_71
  · exact mod4_19
  · exact mod4_3
  · exact mod4_1031
  · exact mod4_1867
  · exact mod4_3
  · exact mod4_31
  · exact mod4_1091
  · exact mod4_3
  · exact mod4_4547
  · exact mod4_19
  · exact mod4_3
  · exact mod4_587
  · exact mod4_6143
  · exact mod4_3
  · exact mod4_2371
  · exact mod4_9719
  · exact mod4_3
  · exact mod4_6871
  · exact mod4_19
  · exact mod4_3
  · exact mod4_31
  · exact mod4_1487
  · exact mod4_3
  · exact mod4_3323
  · exact mod4_2239
  · exact mod4_3
  · exact mod4_4451
  · exact mod4_19
  · exact mod4_3
  · exact mod4_1663
  · exact mod4_31
  · exact mod4_3
  · cases h_false

lemma blocking_prime_by_idx_51_3mod4 (idx : ℕ) : blocking_prime_by_idx_51 idx % 4 = 3 :=
  mod4_of_mem_blocking_primes_51 (getD_mem blocking_primes_51 (idx - 5100) 3)

def blocking_primes_52 : List ℕ := [3, 11, 31, 3, 71, 11, 3, 31, 15679, 3, 11, 11, 3, 15107, 6899, 3, 11, 31, 3, 17471, 11, 3, 31, 47, 3, 11, 11, 3, 14699, 9887, 3, 11, 31, 3, 739, 31, 3, 31, 6011, 3, 167, 15391, 683, 7, 47, 43, 7, 107, 1151, 7, 1811, 151, 7, 683, 6959, 7, 1039, 4003, 7, 43, 8191, 6143, 6599, 1123, 7, 103, 43, 7, 1759, 251, 7, 7639, 16139, 7, 2719, 683, 7, 83, 787, 7, 3, 5987, 239, 3, 11, 4451, 3, 5039, 3251, 3, 1091, 8231, 3, 2351, 11, 3, 3631, 8087, 3, 11]
def blocking_prime_by_idx_52 (idx : ℕ) : ℕ := blocking_primes_52.getD (idx - 5200) 3

lemma prime_of_mem_blocking_primes_52 {p : ℕ} (h : p ∈ 3 :: blocking_primes_52) : Nat.Prime p := by
  unfold blocking_primes_52 at h
  simp only [List.mem_cons] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | h_false
  · exact prime_3
  · exact prime_3
  · exact prime_11
  · exact prime_31
  · exact prime_3
  · exact prime_71
  · exact prime_11
  · exact prime_3
  · exact prime_31
  · exact prime_15679
  · exact prime_3
  · exact prime_11
  · exact prime_11
  · exact prime_3
  · exact prime_15107
  · exact prime_6899
  · exact prime_3
  · exact prime_11
  · exact prime_31
  · exact prime_3
  · exact prime_17471
  · exact prime_11
  · exact prime_3
  · exact prime_31
  · exact prime_47
  · exact prime_3
  · exact prime_11
  · exact prime_11
  · exact prime_3
  · exact prime_14699
  · exact prime_9887
  · exact prime_3
  · exact prime_11
  · exact prime_31
  · exact prime_3
  · exact prime_739
  · exact prime_31
  · exact prime_3
  · exact prime_31
  · exact prime_6011
  · exact prime_3
  · exact prime_167
  · exact prime_15391
  · exact prime_683
  · exact prime_7
  · exact prime_47
  · exact prime_43
  · exact prime_7
  · exact prime_107
  · exact prime_1151
  · exact prime_7
  · exact prime_1811
  · exact prime_151
  · exact prime_7
  · exact prime_683
  · exact prime_6959
  · exact prime_7
  · exact prime_1039
  · exact prime_4003
  · exact prime_7
  · exact prime_43
  · exact prime_8191
  · exact prime_6143
  · exact prime_6599
  · exact prime_1123
  · exact prime_7
  · exact prime_103
  · exact prime_43
  · exact prime_7
  · exact prime_1759
  · exact prime_251
  · exact prime_7
  · exact prime_7639
  · exact prime_16139
  · exact prime_7
  · exact prime_2719
  · exact prime_683
  · exact prime_7
  · exact prime_83
  · exact prime_787
  · exact prime_7
  · exact prime_3
  · exact prime_5987
  · exact prime_239
  · exact prime_3
  · exact prime_11
  · exact prime_4451
  · exact prime_3
  · exact prime_5039
  · exact prime_3251
  · exact prime_3
  · exact prime_1091
  · exact prime_8231
  · exact prime_3
  · exact prime_2351
  · exact prime_11
  · exact prime_3
  · exact prime_3631
  · exact prime_8087
  · exact prime_3
  · exact prime_11
  · cases h_false

lemma blocking_prime_by_idx_52_prime (idx : ℕ) : Nat.Prime (blocking_prime_by_idx_52 idx) :=
  prime_of_mem_blocking_primes_52 (getD_mem blocking_primes_52 (idx - 5200) 3)

lemma mod4_of_mem_blocking_primes_52 {p : ℕ} (h : p ∈ 3 :: blocking_primes_52) : p % 4 = 3 := by
  unfold blocking_primes_52 at h
  simp only [List.mem_cons] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | h_false
  · exact mod4_3
  · exact mod4_3
  · exact mod4_11
  · exact mod4_31
  · exact mod4_3
  · exact mod4_71
  · exact mod4_11
  · exact mod4_3
  · exact mod4_31
  · exact mod4_15679
  · exact mod4_3
  · exact mod4_11
  · exact mod4_11
  · exact mod4_3
  · exact mod4_15107
  · exact mod4_6899
  · exact mod4_3
  · exact mod4_11
  · exact mod4_31
  · exact mod4_3
  · exact mod4_17471
  · exact mod4_11
  · exact mod4_3
  · exact mod4_31
  · exact mod4_47
  · exact mod4_3
  · exact mod4_11
  · exact mod4_11
  · exact mod4_3
  · exact mod4_14699
  · exact mod4_9887
  · exact mod4_3
  · exact mod4_11
  · exact mod4_31
  · exact mod4_3
  · exact mod4_739
  · exact mod4_31
  · exact mod4_3
  · exact mod4_31
  · exact mod4_6011
  · exact mod4_3
  · exact mod4_167
  · exact mod4_15391
  · exact mod4_683
  · exact mod4_7
  · exact mod4_47
  · exact mod4_43
  · exact mod4_7
  · exact mod4_107
  · exact mod4_1151
  · exact mod4_7
  · exact mod4_1811
  · exact mod4_151
  · exact mod4_7
  · exact mod4_683
  · exact mod4_6959
  · exact mod4_7
  · exact mod4_1039
  · exact mod4_4003
  · exact mod4_7
  · exact mod4_43
  · exact mod4_8191
  · exact mod4_6143
  · exact mod4_6599
  · exact mod4_1123
  · exact mod4_7
  · exact mod4_103
  · exact mod4_43
  · exact mod4_7
  · exact mod4_1759
  · exact mod4_251
  · exact mod4_7
  · exact mod4_7639
  · exact mod4_16139
  · exact mod4_7
  · exact mod4_2719
  · exact mod4_683
  · exact mod4_7
  · exact mod4_83
  · exact mod4_787
  · exact mod4_7
  · exact mod4_3
  · exact mod4_5987
  · exact mod4_239
  · exact mod4_3
  · exact mod4_11
  · exact mod4_4451
  · exact mod4_3
  · exact mod4_5039
  · exact mod4_3251
  · exact mod4_3
  · exact mod4_1091
  · exact mod4_8231
  · exact mod4_3
  · exact mod4_2351
  · exact mod4_11
  · exact mod4_3
  · exact mod4_3631
  · exact mod4_8087
  · exact mod4_3
  · exact mod4_11
  · cases h_false

lemma blocking_prime_by_idx_52_3mod4 (idx : ℕ) : blocking_prime_by_idx_52 idx % 4 = 3 :=
  mod4_of_mem_blocking_primes_52 (getD_mem blocking_primes_52 (idx - 5200) 3)

def blocking_primes_53 : List ℕ := [9719, 3, 2647, 6311, 3, 3863, 14951, 3, 7607, 11, 3, 19183, 8191, 3, 11, 2203, 3, 4931, 307, 3, 3, 643, 19739, 3, 439, 6079, 3, 223, 9767, 3, 2731, 4799, 3, 107, 1423, 3, 307, 4463, 3, 431, 2063, 3, 6091, 2731, 3, 199, 11423, 3, 2003, 283, 3, 1019, 11239, 3, 4663, 2287, 3, 2267, 5639, 3, 7, 23, 43, 7, 127, 2027, 7, 14699, 31, 7, 659, 127, 7, 31, 5419, 7, 43, 4231, 31, 7411, 13619, 7, 3691, 31, 7, 127, 8819, 7, 31, 4903, 7, 647, 127, 7, 23, 5419, 7, 43, 31, 127]
def blocking_prime_by_idx_53 (idx : ℕ) : ℕ := blocking_primes_53.getD (idx - 5300) 3

lemma prime_of_mem_blocking_primes_53 {p : ℕ} (h : p ∈ 3 :: blocking_primes_53) : Nat.Prime p := by
  unfold blocking_primes_53 at h
  simp only [List.mem_cons] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | h_false
  · exact prime_3
  · exact prime_9719
  · exact prime_3
  · exact prime_2647
  · exact prime_6311
  · exact prime_3
  · exact prime_3863
  · exact prime_14951
  · exact prime_3
  · exact prime_7607
  · exact prime_11
  · exact prime_3
  · exact prime_19183
  · exact prime_8191
  · exact prime_3
  · exact prime_11
  · exact prime_2203
  · exact prime_3
  · exact prime_4931
  · exact prime_307
  · exact prime_3
  · exact prime_3
  · exact prime_643
  · exact prime_19739
  · exact prime_3
  · exact prime_439
  · exact prime_6079
  · exact prime_3
  · exact prime_223
  · exact prime_9767
  · exact prime_3
  · exact prime_2731
  · exact prime_4799
  · exact prime_3
  · exact prime_107
  · exact prime_1423
  · exact prime_3
  · exact prime_307
  · exact prime_4463
  · exact prime_3
  · exact prime_431
  · exact prime_2063
  · exact prime_3
  · exact prime_6091
  · exact prime_2731
  · exact prime_3
  · exact prime_199
  · exact prime_11423
  · exact prime_3
  · exact prime_2003
  · exact prime_283
  · exact prime_3
  · exact prime_1019
  · exact prime_11239
  · exact prime_3
  · exact prime_4663
  · exact prime_2287
  · exact prime_3
  · exact prime_2267
  · exact prime_5639
  · exact prime_3
  · exact prime_7
  · exact prime_23
  · exact prime_43
  · exact prime_7
  · exact prime_127
  · exact prime_2027
  · exact prime_7
  · exact prime_14699
  · exact prime_31
  · exact prime_7
  · exact prime_659
  · exact prime_127
  · exact prime_7
  · exact prime_31
  · exact prime_5419
  · exact prime_7
  · exact prime_43
  · exact prime_4231
  · exact prime_31
  · exact prime_7411
  · exact prime_13619
  · exact prime_7
  · exact prime_3691
  · exact prime_31
  · exact prime_7
  · exact prime_127
  · exact prime_8819
  · exact prime_7
  · exact prime_31
  · exact prime_4903
  · exact prime_7
  · exact prime_647
  · exact prime_127
  · exact prime_7
  · exact prime_23
  · exact prime_5419
  · exact prime_7
  · exact prime_43
  · exact prime_31
  · exact prime_127
  · cases h_false

lemma blocking_prime_by_idx_53_prime (idx : ℕ) : Nat.Prime (blocking_prime_by_idx_53 idx) :=
  prime_of_mem_blocking_primes_53 (getD_mem blocking_primes_53 (idx - 5300) 3)

lemma mod4_of_mem_blocking_primes_53 {p : ℕ} (h : p ∈ 3 :: blocking_primes_53) : p % 4 = 3 := by
  unfold blocking_primes_53 at h
  simp only [List.mem_cons] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | h_false
  · exact mod4_3
  · exact mod4_9719
  · exact mod4_3
  · exact mod4_2647
  · exact mod4_6311
  · exact mod4_3
  · exact mod4_3863
  · exact mod4_14951
  · exact mod4_3
  · exact mod4_7607
  · exact mod4_11
  · exact mod4_3
  · exact mod4_19183
  · exact mod4_8191
  · exact mod4_3
  · exact mod4_11
  · exact mod4_2203
  · exact mod4_3
  · exact mod4_4931
  · exact mod4_307
  · exact mod4_3
  · exact mod4_3
  · exact mod4_643
  · exact mod4_19739
  · exact mod4_3
  · exact mod4_439
  · exact mod4_6079
  · exact mod4_3
  · exact mod4_223
  · exact mod4_9767
  · exact mod4_3
  · exact mod4_2731
  · exact mod4_4799
  · exact mod4_3
  · exact mod4_107
  · exact mod4_1423
  · exact mod4_3
  · exact mod4_307
  · exact mod4_4463
  · exact mod4_3
  · exact mod4_431
  · exact mod4_2063
  · exact mod4_3
  · exact mod4_6091
  · exact mod4_2731
  · exact mod4_3
  · exact mod4_199
  · exact mod4_11423
  · exact mod4_3
  · exact mod4_2003
  · exact mod4_283
  · exact mod4_3
  · exact mod4_1019
  · exact mod4_11239
  · exact mod4_3
  · exact mod4_4663
  · exact mod4_2287
  · exact mod4_3
  · exact mod4_2267
  · exact mod4_5639
  · exact mod4_3
  · exact mod4_7
  · exact mod4_23
  · exact mod4_43
  · exact mod4_7
  · exact mod4_127
  · exact mod4_2027
  · exact mod4_7
  · exact mod4_14699
  · exact mod4_31
  · exact mod4_7
  · exact mod4_659
  · exact mod4_127
  · exact mod4_7
  · exact mod4_31
  · exact mod4_5419
  · exact mod4_7
  · exact mod4_43
  · exact mod4_4231
  · exact mod4_31
  · exact mod4_7411
  · exact mod4_13619
  · exact mod4_7
  · exact mod4_3691
  · exact mod4_31
  · exact mod4_7
  · exact mod4_127
  · exact mod4_8819
  · exact mod4_7
  · exact mod4_31
  · exact mod4_4903
  · exact mod4_7
  · exact mod4_647
  · exact mod4_127
  · exact mod4_7
  · exact mod4_23
  · exact mod4_5419
  · exact mod4_7
  · exact mod4_43
  · exact mod4_31
  · exact mod4_127
  · cases h_false

lemma blocking_prime_by_idx_53_3mod4 (idx : ℕ) : blocking_prime_by_idx_53 idx % 4 = 3 :=
  mod4_of_mem_blocking_primes_53 (getD_mem blocking_primes_53 (idx - 5300) 3)

def blocking_primes_54 : List ℕ := [3, 11, 31, 3, 5851, 11, 3, 31, 4643, 3, 11, 11, 3, 12763, 5387, 3, 11, 31, 3, 11863, 11, 3, 31, 691, 3, 11, 11, 3, 1051, 1327, 3, 11, 31, 3, 991, 11, 3, 31, 127, 3, 3, 19, 131, 3, 4099, 15859, 3, 1663, 1747, 3, 19, 6271, 3, 7187, 9923, 3, 331, 1327, 3, 19, 971, 3, 79, 4391, 3, 907, 863, 3, 19, 5167, 3, 331, 23, 3, 67, 1447, 3, 19, 199, 3, 7, 3083, 4219, 7, 11, 347, 7, 59, 1663, 7, 7043, 23, 7, 3331, 8123, 3259, 1583, 23, 7, 11]
def blocking_prime_by_idx_54 (idx : ℕ) : ℕ := blocking_primes_54.getD (idx - 5400) 3

lemma prime_of_mem_blocking_primes_54 {p : ℕ} (h : p ∈ 3 :: blocking_primes_54) : Nat.Prime p := by
  unfold blocking_primes_54 at h
  simp only [List.mem_cons] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | h_false
  · exact prime_3
  · exact prime_3
  · exact prime_11
  · exact prime_31
  · exact prime_3
  · exact prime_5851
  · exact prime_11
  · exact prime_3
  · exact prime_31
  · exact prime_4643
  · exact prime_3
  · exact prime_11
  · exact prime_11
  · exact prime_3
  · exact prime_12763
  · exact prime_5387
  · exact prime_3
  · exact prime_11
  · exact prime_31
  · exact prime_3
  · exact prime_11863
  · exact prime_11
  · exact prime_3
  · exact prime_31
  · exact prime_691
  · exact prime_3
  · exact prime_11
  · exact prime_11
  · exact prime_3
  · exact prime_1051
  · exact prime_1327
  · exact prime_3
  · exact prime_11
  · exact prime_31
  · exact prime_3
  · exact prime_991
  · exact prime_11
  · exact prime_3
  · exact prime_31
  · exact prime_127
  · exact prime_3
  · exact prime_3
  · exact prime_19
  · exact prime_131
  · exact prime_3
  · exact prime_4099
  · exact prime_15859
  · exact prime_3
  · exact prime_1663
  · exact prime_1747
  · exact prime_3
  · exact prime_19
  · exact prime_6271
  · exact prime_3
  · exact prime_7187
  · exact prime_9923
  · exact prime_3
  · exact prime_331
  · exact prime_1327
  · exact prime_3
  · exact prime_19
  · exact prime_971
  · exact prime_3
  · exact prime_79
  · exact prime_4391
  · exact prime_3
  · exact prime_907
  · exact prime_863
  · exact prime_3
  · exact prime_19
  · exact prime_5167
  · exact prime_3
  · exact prime_331
  · exact prime_23
  · exact prime_3
  · exact prime_67
  · exact prime_1447
  · exact prime_3
  · exact prime_19
  · exact prime_199
  · exact prime_3
  · exact prime_7
  · exact prime_3083
  · exact prime_4219
  · exact prime_7
  · exact prime_11
  · exact prime_347
  · exact prime_7
  · exact prime_59
  · exact prime_1663
  · exact prime_7
  · exact prime_7043
  · exact prime_23
  · exact prime_7
  · exact prime_3331
  · exact prime_8123
  · exact prime_3259
  · exact prime_1583
  · exact prime_23
  · exact prime_7
  · exact prime_11
  · cases h_false

lemma blocking_prime_by_idx_54_prime (idx : ℕ) : Nat.Prime (blocking_prime_by_idx_54 idx) :=
  prime_of_mem_blocking_primes_54 (getD_mem blocking_primes_54 (idx - 5400) 3)

lemma mod4_of_mem_blocking_primes_54 {p : ℕ} (h : p ∈ 3 :: blocking_primes_54) : p % 4 = 3 := by
  unfold blocking_primes_54 at h
  simp only [List.mem_cons] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | h_false
  · exact mod4_3
  · exact mod4_3
  · exact mod4_11
  · exact mod4_31
  · exact mod4_3
  · exact mod4_5851
  · exact mod4_11
  · exact mod4_3
  · exact mod4_31
  · exact mod4_4643
  · exact mod4_3
  · exact mod4_11
  · exact mod4_11
  · exact mod4_3
  · exact mod4_12763
  · exact mod4_5387
  · exact mod4_3
  · exact mod4_11
  · exact mod4_31
  · exact mod4_3
  · exact mod4_11863
  · exact mod4_11
  · exact mod4_3
  · exact mod4_31
  · exact mod4_691
  · exact mod4_3
  · exact mod4_11
  · exact mod4_11
  · exact mod4_3
  · exact mod4_1051
  · exact mod4_1327
  · exact mod4_3
  · exact mod4_11
  · exact mod4_31
  · exact mod4_3
  · exact mod4_991
  · exact mod4_11
  · exact mod4_3
  · exact mod4_31
  · exact mod4_127
  · exact mod4_3
  · exact mod4_3
  · exact mod4_19
  · exact mod4_131
  · exact mod4_3
  · exact mod4_4099
  · exact mod4_15859
  · exact mod4_3
  · exact mod4_1663
  · exact mod4_1747
  · exact mod4_3
  · exact mod4_19
  · exact mod4_6271
  · exact mod4_3
  · exact mod4_7187
  · exact mod4_9923
  · exact mod4_3
  · exact mod4_331
  · exact mod4_1327
  · exact mod4_3
  · exact mod4_19
  · exact mod4_971
  · exact mod4_3
  · exact mod4_79
  · exact mod4_4391
  · exact mod4_3
  · exact mod4_907
  · exact mod4_863
  · exact mod4_3
  · exact mod4_19
  · exact mod4_5167
  · exact mod4_3
  · exact mod4_331
  · exact mod4_23
  · exact mod4_3
  · exact mod4_67
  · exact mod4_1447
  · exact mod4_3
  · exact mod4_19
  · exact mod4_199
  · exact mod4_3
  · exact mod4_7
  · exact mod4_3083
  · exact mod4_4219
  · exact mod4_7
  · exact mod4_11
  · exact mod4_347
  · exact mod4_7
  · exact mod4_59
  · exact mod4_1663
  · exact mod4_7
  · exact mod4_7043
  · exact mod4_23
  · exact mod4_7
  · exact mod4_3331
  · exact mod4_8123
  · exact mod4_3259
  · exact mod4_1583
  · exact mod4_23
  · exact mod4_7
  · exact mod4_11
  · cases h_false

lemma blocking_prime_by_idx_54_3mod4 (idx : ℕ) : blocking_prime_by_idx_54 idx % 4 = 3 :=
  mod4_of_mem_blocking_primes_54 (getD_mem blocking_primes_54 (idx - 5400) 3)

def blocking_primes_55 : List ℕ := [1451, 7, 23, 6323, 7, 1367, 2383, 7, 23, 11, 7, 691, 4111, 7, 11, 4283, 59, 9539, 2203, 7, 3, 1987, 1747, 3, 151, 23, 3, 8719, 19, 3, 191, 6367, 3, 4363, 331, 3, 23, 19, 3, 43, 7703, 3, 131, 163, 3, 5807, 19, 3, 691, 331, 3, 71, 67, 3, 151, 19, 3, 6563, 23, 3, 3, 2459, 4423, 3, 5231, 7079, 3, 271, 31, 3, 2467, 71, 3, 31, 3863, 3, 523, 47, 3, 47, 59, 3, 13399, 31, 3, 15439, 10343, 3, 31, 13807, 3, 1531, 59, 3, 3299, 1523, 3, 2707, 31, 3]
def blocking_prime_by_idx_55 (idx : ℕ) : ℕ := blocking_primes_55.getD (idx - 5500) 3

lemma prime_of_mem_blocking_primes_55 {p : ℕ} (h : p ∈ 3 :: blocking_primes_55) : Nat.Prime p := by
  unfold blocking_primes_55 at h
  simp only [List.mem_cons] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | h_false
  · exact prime_3
  · exact prime_1451
  · exact prime_7
  · exact prime_23
  · exact prime_6323
  · exact prime_7
  · exact prime_1367
  · exact prime_2383
  · exact prime_7
  · exact prime_23
  · exact prime_11
  · exact prime_7
  · exact prime_691
  · exact prime_4111
  · exact prime_7
  · exact prime_11
  · exact prime_4283
  · exact prime_59
  · exact prime_9539
  · exact prime_2203
  · exact prime_7
  · exact prime_3
  · exact prime_1987
  · exact prime_1747
  · exact prime_3
  · exact prime_151
  · exact prime_23
  · exact prime_3
  · exact prime_8719
  · exact prime_19
  · exact prime_3
  · exact prime_191
  · exact prime_6367
  · exact prime_3
  · exact prime_4363
  · exact prime_331
  · exact prime_3
  · exact prime_23
  · exact prime_19
  · exact prime_3
  · exact prime_43
  · exact prime_7703
  · exact prime_3
  · exact prime_131
  · exact prime_163
  · exact prime_3
  · exact prime_5807
  · exact prime_19
  · exact prime_3
  · exact prime_691
  · exact prime_331
  · exact prime_3
  · exact prime_71
  · exact prime_67
  · exact prime_3
  · exact prime_151
  · exact prime_19
  · exact prime_3
  · exact prime_6563
  · exact prime_23
  · exact prime_3
  · exact prime_3
  · exact prime_2459
  · exact prime_4423
  · exact prime_3
  · exact prime_5231
  · exact prime_7079
  · exact prime_3
  · exact prime_271
  · exact prime_31
  · exact prime_3
  · exact prime_2467
  · exact prime_71
  · exact prime_3
  · exact prime_31
  · exact prime_3863
  · exact prime_3
  · exact prime_523
  · exact prime_47
  · exact prime_3
  · exact prime_47
  · exact prime_59
  · exact prime_3
  · exact prime_13399
  · exact prime_31
  · exact prime_3
  · exact prime_15439
  · exact prime_10343
  · exact prime_3
  · exact prime_31
  · exact prime_13807
  · exact prime_3
  · exact prime_1531
  · exact prime_59
  · exact prime_3
  · exact prime_3299
  · exact prime_1523
  · exact prime_3
  · exact prime_2707
  · exact prime_31
  · exact prime_3
  · cases h_false

lemma blocking_prime_by_idx_55_prime (idx : ℕ) : Nat.Prime (blocking_prime_by_idx_55 idx) :=
  prime_of_mem_blocking_primes_55 (getD_mem blocking_primes_55 (idx - 5500) 3)

lemma mod4_of_mem_blocking_primes_55 {p : ℕ} (h : p ∈ 3 :: blocking_primes_55) : p % 4 = 3 := by
  unfold blocking_primes_55 at h
  simp only [List.mem_cons] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | h_false
  · exact mod4_3
  · exact mod4_1451
  · exact mod4_7
  · exact mod4_23
  · exact mod4_6323
  · exact mod4_7
  · exact mod4_1367
  · exact mod4_2383
  · exact mod4_7
  · exact mod4_23
  · exact mod4_11
  · exact mod4_7
  · exact mod4_691
  · exact mod4_4111
  · exact mod4_7
  · exact mod4_11
  · exact mod4_4283
  · exact mod4_59
  · exact mod4_9539
  · exact mod4_2203
  · exact mod4_7
  · exact mod4_3
  · exact mod4_1987
  · exact mod4_1747
  · exact mod4_3
  · exact mod4_151
  · exact mod4_23
  · exact mod4_3
  · exact mod4_8719
  · exact mod4_19
  · exact mod4_3
  · exact mod4_191
  · exact mod4_6367
  · exact mod4_3
  · exact mod4_4363
  · exact mod4_331
  · exact mod4_3
  · exact mod4_23
  · exact mod4_19
  · exact mod4_3
  · exact mod4_43
  · exact mod4_7703
  · exact mod4_3
  · exact mod4_131
  · exact mod4_163
  · exact mod4_3
  · exact mod4_5807
  · exact mod4_19
  · exact mod4_3
  · exact mod4_691
  · exact mod4_331
  · exact mod4_3
  · exact mod4_71
  · exact mod4_67
  · exact mod4_3
  · exact mod4_151
  · exact mod4_19
  · exact mod4_3
  · exact mod4_6563
  · exact mod4_23
  · exact mod4_3
  · exact mod4_3
  · exact mod4_2459
  · exact mod4_4423
  · exact mod4_3
  · exact mod4_5231
  · exact mod4_7079
  · exact mod4_3
  · exact mod4_271
  · exact mod4_31
  · exact mod4_3
  · exact mod4_2467
  · exact mod4_71
  · exact mod4_3
  · exact mod4_31
  · exact mod4_3863
  · exact mod4_3
  · exact mod4_523
  · exact mod4_47
  · exact mod4_3
  · exact mod4_47
  · exact mod4_59
  · exact mod4_3
  · exact mod4_13399
  · exact mod4_31
  · exact mod4_3
  · exact mod4_15439
  · exact mod4_10343
  · exact mod4_3
  · exact mod4_31
  · exact mod4_13807
  · exact mod4_3
  · exact mod4_1531
  · exact mod4_59
  · exact mod4_3
  · exact mod4_3299
  · exact mod4_1523
  · exact mod4_3
  · exact mod4_2707
  · exact mod4_31
  · exact mod4_3
  · cases h_false

lemma blocking_prime_by_idx_55_3mod4 (idx : ℕ) : blocking_prime_by_idx_55 idx % 4 = 3 :=
  mod4_of_mem_blocking_primes_55 (getD_mem blocking_primes_55 (idx - 5500) 3)

def blocking_primes_56 : List ℕ := [7, 11, 31, 7, 3019, 11, 7, 31, 131, 7, 11, 11, 31, 163, 9199, 7, 11, 31, 7, 4127, 11, 7, 31, 67, 7, 31, 11, 7, 5743, 2731, 7, 11, 31, 83, 7207, 11, 7, 31, 139, 7, 3, 2819, 43, 3, 127, 59, 3, 5419, 823, 3, 1699, 127, 3, 8231, 307, 3, 43, 79, 3, 10303, 9151, 3, 3571, 43, 3, 127, 3511, 3, 5419, 59, 3, 3463, 127, 3, 59, 271, 3, 43, 5279, 3, 3, 12119, 683, 3, 331, 1579, 3, 743, 1063, 3, 127, 379, 3, 683, 11, 3, 2803, 127, 3, 11]
def blocking_prime_by_idx_56 (idx : ℕ) : ℕ := blocking_primes_56.getD (idx - 5600) 3

lemma prime_of_mem_blocking_primes_56 {p : ℕ} (h : p ∈ 3 :: blocking_primes_56) : Nat.Prime p := by
  unfold blocking_primes_56 at h
  simp only [List.mem_cons] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | h_false
  · exact prime_3
  · exact prime_7
  · exact prime_11
  · exact prime_31
  · exact prime_7
  · exact prime_3019
  · exact prime_11
  · exact prime_7
  · exact prime_31
  · exact prime_131
  · exact prime_7
  · exact prime_11
  · exact prime_11
  · exact prime_31
  · exact prime_163
  · exact prime_9199
  · exact prime_7
  · exact prime_11
  · exact prime_31
  · exact prime_7
  · exact prime_4127
  · exact prime_11
  · exact prime_7
  · exact prime_31
  · exact prime_67
  · exact prime_7
  · exact prime_31
  · exact prime_11
  · exact prime_7
  · exact prime_5743
  · exact prime_2731
  · exact prime_7
  · exact prime_11
  · exact prime_31
  · exact prime_83
  · exact prime_7207
  · exact prime_11
  · exact prime_7
  · exact prime_31
  · exact prime_139
  · exact prime_7
  · exact prime_3
  · exact prime_2819
  · exact prime_43
  · exact prime_3
  · exact prime_127
  · exact prime_59
  · exact prime_3
  · exact prime_5419
  · exact prime_823
  · exact prime_3
  · exact prime_1699
  · exact prime_127
  · exact prime_3
  · exact prime_8231
  · exact prime_307
  · exact prime_3
  · exact prime_43
  · exact prime_79
  · exact prime_3
  · exact prime_10303
  · exact prime_9151
  · exact prime_3
  · exact prime_3571
  · exact prime_43
  · exact prime_3
  · exact prime_127
  · exact prime_3511
  · exact prime_3
  · exact prime_5419
  · exact prime_59
  · exact prime_3
  · exact prime_3463
  · exact prime_127
  · exact prime_3
  · exact prime_59
  · exact prime_271
  · exact prime_3
  · exact prime_43
  · exact prime_5279
  · exact prime_3
  · exact prime_3
  · exact prime_12119
  · exact prime_683
  · exact prime_3
  · exact prime_331
  · exact prime_1579
  · exact prime_3
  · exact prime_743
  · exact prime_1063
  · exact prime_3
  · exact prime_127
  · exact prime_379
  · exact prime_3
  · exact prime_683
  · exact prime_11
  · exact prime_3
  · exact prime_2803
  · exact prime_127
  · exact prime_3
  · exact prime_11
  · cases h_false

lemma blocking_prime_by_idx_56_prime (idx : ℕ) : Nat.Prime (blocking_prime_by_idx_56 idx) :=
  prime_of_mem_blocking_primes_56 (getD_mem blocking_primes_56 (idx - 5600) 3)

lemma mod4_of_mem_blocking_primes_56 {p : ℕ} (h : p ∈ 3 :: blocking_primes_56) : p % 4 = 3 := by
  unfold blocking_primes_56 at h
  simp only [List.mem_cons] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | h_false
  · exact mod4_3
  · exact mod4_7
  · exact mod4_11
  · exact mod4_31
  · exact mod4_7
  · exact mod4_3019
  · exact mod4_11
  · exact mod4_7
  · exact mod4_31
  · exact mod4_131
  · exact mod4_7
  · exact mod4_11
  · exact mod4_11
  · exact mod4_31
  · exact mod4_163
  · exact mod4_9199
  · exact mod4_7
  · exact mod4_11
  · exact mod4_31
  · exact mod4_7
  · exact mod4_4127
  · exact mod4_11
  · exact mod4_7
  · exact mod4_31
  · exact mod4_67
  · exact mod4_7
  · exact mod4_31
  · exact mod4_11
  · exact mod4_7
  · exact mod4_5743
  · exact mod4_2731
  · exact mod4_7
  · exact mod4_11
  · exact mod4_31
  · exact mod4_83
  · exact mod4_7207
  · exact mod4_11
  · exact mod4_7
  · exact mod4_31
  · exact mod4_139
  · exact mod4_7
  · exact mod4_3
  · exact mod4_2819
  · exact mod4_43
  · exact mod4_3
  · exact mod4_127
  · exact mod4_59
  · exact mod4_3
  · exact mod4_5419
  · exact mod4_823
  · exact mod4_3
  · exact mod4_1699
  · exact mod4_127
  · exact mod4_3
  · exact mod4_8231
  · exact mod4_307
  · exact mod4_3
  · exact mod4_43
  · exact mod4_79
  · exact mod4_3
  · exact mod4_10303
  · exact mod4_9151
  · exact mod4_3
  · exact mod4_3571
  · exact mod4_43
  · exact mod4_3
  · exact mod4_127
  · exact mod4_3511
  · exact mod4_3
  · exact mod4_5419
  · exact mod4_59
  · exact mod4_3
  · exact mod4_3463
  · exact mod4_127
  · exact mod4_3
  · exact mod4_59
  · exact mod4_271
  · exact mod4_3
  · exact mod4_43
  · exact mod4_5279
  · exact mod4_3
  · exact mod4_3
  · exact mod4_12119
  · exact mod4_683
  · exact mod4_3
  · exact mod4_331
  · exact mod4_1579
  · exact mod4_3
  · exact mod4_743
  · exact mod4_1063
  · exact mod4_3
  · exact mod4_127
  · exact mod4_379
  · exact mod4_3
  · exact mod4_683
  · exact mod4_11
  · exact mod4_3
  · exact mod4_2803
  · exact mod4_127
  · exact mod4_3
  · exact mod4_11
  · cases h_false

lemma blocking_prime_by_idx_56_3mod4 (idx : ℕ) : blocking_prime_by_idx_56 idx % 4 = 3 :=
  mod4_of_mem_blocking_primes_56 (getD_mem blocking_primes_56 (idx - 5600) 3)

def blocking_primes_57 : List ℕ := [3191, 3, 71, 1447, 3, 1163, 2267, 3, 11119, 11, 3, 127, 1907, 3, 11, 683, 3, 4519, 127, 3, 7, 263, 71, 7, 14411, 2467, 7, 419, 59, 8087, 10607, 9551, 7, 1979, 67, 7, 1931, 191, 7, 6091, 14951, 7, 67, 1031, 7, 131, 1579, 7, 71, 4391, 283, 211, 311, 7, 1031, 4703, 7, 59, 9439, 7, 3, 5683, 859, 3, 12959, 811, 3, 8191, 31, 3, 787, 823, 3, 31, 5923, 3, 719, 10859, 3, 4483, 8191, 3, 9431, 31, 3, 2659, 11131, 3, 31, 7547, 3, 3559, 1427, 3, 691, 487, 3, 647, 31, 3]
def blocking_prime_by_idx_57 (idx : ℕ) : ℕ := blocking_primes_57.getD (idx - 5700) 3

lemma prime_of_mem_blocking_primes_57 {p : ℕ} (h : p ∈ 3 :: blocking_primes_57) : Nat.Prime p := by
  unfold blocking_primes_57 at h
  simp only [List.mem_cons] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | h_false
  · exact prime_3
  · exact prime_3191
  · exact prime_3
  · exact prime_71
  · exact prime_1447
  · exact prime_3
  · exact prime_1163
  · exact prime_2267
  · exact prime_3
  · exact prime_11119
  · exact prime_11
  · exact prime_3
  · exact prime_127
  · exact prime_1907
  · exact prime_3
  · exact prime_11
  · exact prime_683
  · exact prime_3
  · exact prime_4519
  · exact prime_127
  · exact prime_3
  · exact prime_7
  · exact prime_263
  · exact prime_71
  · exact prime_7
  · exact prime_14411
  · exact prime_2467
  · exact prime_7
  · exact prime_419
  · exact prime_59
  · exact prime_8087
  · exact prime_10607
  · exact prime_9551
  · exact prime_7
  · exact prime_1979
  · exact prime_67
  · exact prime_7
  · exact prime_1931
  · exact prime_191
  · exact prime_7
  · exact prime_6091
  · exact prime_14951
  · exact prime_7
  · exact prime_67
  · exact prime_1031
  · exact prime_7
  · exact prime_131
  · exact prime_1579
  · exact prime_7
  · exact prime_71
  · exact prime_4391
  · exact prime_283
  · exact prime_211
  · exact prime_311
  · exact prime_7
  · exact prime_1031
  · exact prime_4703
  · exact prime_7
  · exact prime_59
  · exact prime_9439
  · exact prime_7
  · exact prime_3
  · exact prime_5683
  · exact prime_859
  · exact prime_3
  · exact prime_12959
  · exact prime_811
  · exact prime_3
  · exact prime_8191
  · exact prime_31
  · exact prime_3
  · exact prime_787
  · exact prime_823
  · exact prime_3
  · exact prime_31
  · exact prime_5923
  · exact prime_3
  · exact prime_719
  · exact prime_10859
  · exact prime_3
  · exact prime_4483
  · exact prime_8191
  · exact prime_3
  · exact prime_9431
  · exact prime_31
  · exact prime_3
  · exact prime_2659
  · exact prime_11131
  · exact prime_3
  · exact prime_31
  · exact prime_7547
  · exact prime_3
  · exact prime_3559
  · exact prime_1427
  · exact prime_3
  · exact prime_691
  · exact prime_487
  · exact prime_3
  · exact prime_647
  · exact prime_31
  · exact prime_3
  · cases h_false

lemma blocking_prime_by_idx_57_prime (idx : ℕ) : Nat.Prime (blocking_prime_by_idx_57 idx) :=
  prime_of_mem_blocking_primes_57 (getD_mem blocking_primes_57 (idx - 5700) 3)

lemma mod4_of_mem_blocking_primes_57 {p : ℕ} (h : p ∈ 3 :: blocking_primes_57) : p % 4 = 3 := by
  unfold blocking_primes_57 at h
  simp only [List.mem_cons] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | h_false
  · exact mod4_3
  · exact mod4_3191
  · exact mod4_3
  · exact mod4_71
  · exact mod4_1447
  · exact mod4_3
  · exact mod4_1163
  · exact mod4_2267
  · exact mod4_3
  · exact mod4_11119
  · exact mod4_11
  · exact mod4_3
  · exact mod4_127
  · exact mod4_1907
  · exact mod4_3
  · exact mod4_11
  · exact mod4_683
  · exact mod4_3
  · exact mod4_4519
  · exact mod4_127
  · exact mod4_3
  · exact mod4_7
  · exact mod4_263
  · exact mod4_71
  · exact mod4_7
  · exact mod4_14411
  · exact mod4_2467
  · exact mod4_7
  · exact mod4_419
  · exact mod4_59
  · exact mod4_8087
  · exact mod4_10607
  · exact mod4_9551
  · exact mod4_7
  · exact mod4_1979
  · exact mod4_67
  · exact mod4_7
  · exact mod4_1931
  · exact mod4_191
  · exact mod4_7
  · exact mod4_6091
  · exact mod4_14951
  · exact mod4_7
  · exact mod4_67
  · exact mod4_1031
  · exact mod4_7
  · exact mod4_131
  · exact mod4_1579
  · exact mod4_7
  · exact mod4_71
  · exact mod4_4391
  · exact mod4_283
  · exact mod4_211
  · exact mod4_311
  · exact mod4_7
  · exact mod4_1031
  · exact mod4_4703
  · exact mod4_7
  · exact mod4_59
  · exact mod4_9439
  · exact mod4_7
  · exact mod4_3
  · exact mod4_5683
  · exact mod4_859
  · exact mod4_3
  · exact mod4_12959
  · exact mod4_811
  · exact mod4_3
  · exact mod4_8191
  · exact mod4_31
  · exact mod4_3
  · exact mod4_787
  · exact mod4_823
  · exact mod4_3
  · exact mod4_31
  · exact mod4_5923
  · exact mod4_3
  · exact mod4_719
  · exact mod4_10859
  · exact mod4_3
  · exact mod4_4483
  · exact mod4_8191
  · exact mod4_3
  · exact mod4_9431
  · exact mod4_31
  · exact mod4_3
  · exact mod4_2659
  · exact mod4_11131
  · exact mod4_3
  · exact mod4_31
  · exact mod4_7547
  · exact mod4_3
  · exact mod4_3559
  · exact mod4_1427
  · exact mod4_3
  · exact mod4_691
  · exact mod4_487
  · exact mod4_3
  · exact mod4_647
  · exact mod4_31
  · exact mod4_3
  · cases h_false

lemma blocking_prime_by_idx_57_3mod4 (idx : ℕ) : blocking_prime_by_idx_57 idx % 4 = 3 :=
  mod4_of_mem_blocking_primes_57 (getD_mem blocking_primes_57 (idx - 5700) 3)

def blocking_primes_58 : List ℕ := [3, 11, 31, 3, 2963, 11, 3, 31, 11351, 3, 11, 11, 3, 1783, 4423, 3, 11, 31, 3, 19, 31, 3, 31, 23, 3, 11, 11, 3, 19, 79, 3, 11, 31, 3, 23, 11, 3, 19, 1787, 3, 7, 3739, 10139, 7, 4219, 5867, 463, 8263, 5659, 7, 2731, 151, 7, 167, 4663, 7, 9547, 1667, 7, 1567, 683, 7, 8527, 2731, 7, 359, 151, 839, 1487, 5303, 7, 683, 103, 7, 12959, 7559, 7, 6899, 10627, 7, 3, 5407, 139, 3, 11, 2399, 3, 3067, 19, 3, 5051, 1787, 3, 5939, 11, 3, 739, 19, 3, 11]
def blocking_prime_by_idx_58 (idx : ℕ) : ℕ := blocking_primes_58.getD (idx - 5800) 3

lemma prime_of_mem_blocking_primes_58 {p : ℕ} (h : p ∈ 3 :: blocking_primes_58) : Nat.Prime p := by
  unfold blocking_primes_58 at h
  simp only [List.mem_cons] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | h_false
  · exact prime_3
  · exact prime_3
  · exact prime_11
  · exact prime_31
  · exact prime_3
  · exact prime_2963
  · exact prime_11
  · exact prime_3
  · exact prime_31
  · exact prime_11351
  · exact prime_3
  · exact prime_11
  · exact prime_11
  · exact prime_3
  · exact prime_1783
  · exact prime_4423
  · exact prime_3
  · exact prime_11
  · exact prime_31
  · exact prime_3
  · exact prime_19
  · exact prime_31
  · exact prime_3
  · exact prime_31
  · exact prime_23
  · exact prime_3
  · exact prime_11
  · exact prime_11
  · exact prime_3
  · exact prime_19
  · exact prime_79
  · exact prime_3
  · exact prime_11
  · exact prime_31
  · exact prime_3
  · exact prime_23
  · exact prime_11
  · exact prime_3
  · exact prime_19
  · exact prime_1787
  · exact prime_3
  · exact prime_7
  · exact prime_3739
  · exact prime_10139
  · exact prime_7
  · exact prime_4219
  · exact prime_5867
  · exact prime_463
  · exact prime_8263
  · exact prime_5659
  · exact prime_7
  · exact prime_2731
  · exact prime_151
  · exact prime_7
  · exact prime_167
  · exact prime_4663
  · exact prime_7
  · exact prime_9547
  · exact prime_1667
  · exact prime_7
  · exact prime_1567
  · exact prime_683
  · exact prime_7
  · exact prime_8527
  · exact prime_2731
  · exact prime_7
  · exact prime_359
  · exact prime_151
  · exact prime_839
  · exact prime_1487
  · exact prime_5303
  · exact prime_7
  · exact prime_683
  · exact prime_103
  · exact prime_7
  · exact prime_12959
  · exact prime_7559
  · exact prime_7
  · exact prime_6899
  · exact prime_10627
  · exact prime_7
  · exact prime_3
  · exact prime_5407
  · exact prime_139
  · exact prime_3
  · exact prime_11
  · exact prime_2399
  · exact prime_3
  · exact prime_3067
  · exact prime_19
  · exact prime_3
  · exact prime_5051
  · exact prime_1787
  · exact prime_3
  · exact prime_5939
  · exact prime_11
  · exact prime_3
  · exact prime_739
  · exact prime_19
  · exact prime_3
  · exact prime_11
  · cases h_false

lemma blocking_prime_by_idx_58_prime (idx : ℕ) : Nat.Prime (blocking_prime_by_idx_58 idx) :=
  prime_of_mem_blocking_primes_58 (getD_mem blocking_primes_58 (idx - 5800) 3)

lemma mod4_of_mem_blocking_primes_58 {p : ℕ} (h : p ∈ 3 :: blocking_primes_58) : p % 4 = 3 := by
  unfold blocking_primes_58 at h
  simp only [List.mem_cons] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | h_false
  · exact mod4_3
  · exact mod4_3
  · exact mod4_11
  · exact mod4_31
  · exact mod4_3
  · exact mod4_2963
  · exact mod4_11
  · exact mod4_3
  · exact mod4_31
  · exact mod4_11351
  · exact mod4_3
  · exact mod4_11
  · exact mod4_11
  · exact mod4_3
  · exact mod4_1783
  · exact mod4_4423
  · exact mod4_3
  · exact mod4_11
  · exact mod4_31
  · exact mod4_3
  · exact mod4_19
  · exact mod4_31
  · exact mod4_3
  · exact mod4_31
  · exact mod4_23
  · exact mod4_3
  · exact mod4_11
  · exact mod4_11
  · exact mod4_3
  · exact mod4_19
  · exact mod4_79
  · exact mod4_3
  · exact mod4_11
  · exact mod4_31
  · exact mod4_3
  · exact mod4_23
  · exact mod4_11
  · exact mod4_3
  · exact mod4_19
  · exact mod4_1787
  · exact mod4_3
  · exact mod4_7
  · exact mod4_3739
  · exact mod4_10139
  · exact mod4_7
  · exact mod4_4219
  · exact mod4_5867
  · exact mod4_463
  · exact mod4_8263
  · exact mod4_5659
  · exact mod4_7
  · exact mod4_2731
  · exact mod4_151
  · exact mod4_7
  · exact mod4_167
  · exact mod4_4663
  · exact mod4_7
  · exact mod4_9547
  · exact mod4_1667
  · exact mod4_7
  · exact mod4_1567
  · exact mod4_683
  · exact mod4_7
  · exact mod4_8527
  · exact mod4_2731
  · exact mod4_7
  · exact mod4_359
  · exact mod4_151
  · exact mod4_839
  · exact mod4_1487
  · exact mod4_5303
  · exact mod4_7
  · exact mod4_683
  · exact mod4_103
  · exact mod4_7
  · exact mod4_12959
  · exact mod4_7559
  · exact mod4_7
  · exact mod4_6899
  · exact mod4_10627
  · exact mod4_7
  · exact mod4_3
  · exact mod4_5407
  · exact mod4_139
  · exact mod4_3
  · exact mod4_11
  · exact mod4_2399
  · exact mod4_3
  · exact mod4_3067
  · exact mod4_19
  · exact mod4_3
  · exact mod4_5051
  · exact mod4_1787
  · exact mod4_3
  · exact mod4_5939
  · exact mod4_11
  · exact mod4_3
  · exact mod4_739
  · exact mod4_19
  · exact mod4_3
  · exact mod4_11
  · cases h_false

lemma blocking_prime_by_idx_58_3mod4 (idx : ℕ) : blocking_prime_by_idx_58 idx % 4 = 3 :=
  mod4_of_mem_blocking_primes_58 (getD_mem blocking_primes_58 (idx - 5800) 3)

def blocking_primes_59 : List ℕ := [7283, 3, 2447, 11119, 3, 83, 19, 3, 239, 11, 3, 139, 23, 3, 11, 19, 3, 227, 6151, 3, 3, 59, 43, 3, 127, 5387, 3, 1607, 887, 3, 223, 23, 3, 6679, 1559, 3, 43, 23, 3, 13367, 4051, 3, 23, 43, 3, 127, 743, 3, 23, 71, 3, 2143, 127, 3, 5791, 2963, 3, 43, 131, 3, 7, 7687, 5639, 31, 5023, 23, 7, 18911, 31, 7, 127, 491, 7, 31, 3847, 7, 23, 127, 7, 1663, 67, 7, 347, 31, 127, 17471, 131, 7, 31, 2447, 7, 127, 3823, 7, 15671, 8179, 7, 3823, 31, 7]
def blocking_prime_by_idx_59 (idx : ℕ) : ℕ := blocking_primes_59.getD (idx - 5900) 3

lemma prime_of_mem_blocking_primes_59 {p : ℕ} (h : p ∈ 3 :: blocking_primes_59) : Nat.Prime p := by
  unfold blocking_primes_59 at h
  simp only [List.mem_cons] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | h_false
  · exact prime_3
  · exact prime_7283
  · exact prime_3
  · exact prime_2447
  · exact prime_11119
  · exact prime_3
  · exact prime_83
  · exact prime_19
  · exact prime_3
  · exact prime_239
  · exact prime_11
  · exact prime_3
  · exact prime_139
  · exact prime_23
  · exact prime_3
  · exact prime_11
  · exact prime_19
  · exact prime_3
  · exact prime_227
  · exact prime_6151
  · exact prime_3
  · exact prime_3
  · exact prime_59
  · exact prime_43
  · exact prime_3
  · exact prime_127
  · exact prime_5387
  · exact prime_3
  · exact prime_1607
  · exact prime_887
  · exact prime_3
  · exact prime_223
  · exact prime_23
  · exact prime_3
  · exact prime_6679
  · exact prime_1559
  · exact prime_3
  · exact prime_43
  · exact prime_23
  · exact prime_3
  · exact prime_13367
  · exact prime_4051
  · exact prime_3
  · exact prime_23
  · exact prime_43
  · exact prime_3
  · exact prime_127
  · exact prime_743
  · exact prime_3
  · exact prime_23
  · exact prime_71
  · exact prime_3
  · exact prime_2143
  · exact prime_127
  · exact prime_3
  · exact prime_5791
  · exact prime_2963
  · exact prime_3
  · exact prime_43
  · exact prime_131
  · exact prime_3
  · exact prime_7
  · exact prime_7687
  · exact prime_5639
  · exact prime_31
  · exact prime_5023
  · exact prime_23
  · exact prime_7
  · exact prime_18911
  · exact prime_31
  · exact prime_7
  · exact prime_127
  · exact prime_491
  · exact prime_7
  · exact prime_31
  · exact prime_3847
  · exact prime_7
  · exact prime_23
  · exact prime_127
  · exact prime_7
  · exact prime_1663
  · exact prime_67
  · exact prime_7
  · exact prime_347
  · exact prime_31
  · exact prime_127
  · exact prime_17471
  · exact prime_131
  · exact prime_7
  · exact prime_31
  · exact prime_2447
  · exact prime_7
  · exact prime_127
  · exact prime_3823
  · exact prime_7
  · exact prime_15671
  · exact prime_8179
  · exact prime_7
  · exact prime_3823
  · exact prime_31
  · exact prime_7
  · cases h_false

lemma blocking_prime_by_idx_59_prime (idx : ℕ) : Nat.Prime (blocking_prime_by_idx_59 idx) :=
  prime_of_mem_blocking_primes_59 (getD_mem blocking_primes_59 (idx - 5900) 3)

lemma mod4_of_mem_blocking_primes_59 {p : ℕ} (h : p ∈ 3 :: blocking_primes_59) : p % 4 = 3 := by
  unfold blocking_primes_59 at h
  simp only [List.mem_cons] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | h_false
  · exact mod4_3
  · exact mod4_7283
  · exact mod4_3
  · exact mod4_2447
  · exact mod4_11119
  · exact mod4_3
  · exact mod4_83
  · exact mod4_19
  · exact mod4_3
  · exact mod4_239
  · exact mod4_11
  · exact mod4_3
  · exact mod4_139
  · exact mod4_23
  · exact mod4_3
  · exact mod4_11
  · exact mod4_19
  · exact mod4_3
  · exact mod4_227
  · exact mod4_6151
  · exact mod4_3
  · exact mod4_3
  · exact mod4_59
  · exact mod4_43
  · exact mod4_3
  · exact mod4_127
  · exact mod4_5387
  · exact mod4_3
  · exact mod4_1607
  · exact mod4_887
  · exact mod4_3
  · exact mod4_223
  · exact mod4_23
  · exact mod4_3
  · exact mod4_6679
  · exact mod4_1559
  · exact mod4_3
  · exact mod4_43
  · exact mod4_23
  · exact mod4_3
  · exact mod4_13367
  · exact mod4_4051
  · exact mod4_3
  · exact mod4_23
  · exact mod4_43
  · exact mod4_3
  · exact mod4_127
  · exact mod4_743
  · exact mod4_3
  · exact mod4_23
  · exact mod4_71
  · exact mod4_3
  · exact mod4_2143
  · exact mod4_127
  · exact mod4_3
  · exact mod4_5791
  · exact mod4_2963
  · exact mod4_3
  · exact mod4_43
  · exact mod4_131
  · exact mod4_3
  · exact mod4_7
  · exact mod4_7687
  · exact mod4_5639
  · exact mod4_31
  · exact mod4_5023
  · exact mod4_23
  · exact mod4_7
  · exact mod4_18911
  · exact mod4_31
  · exact mod4_7
  · exact mod4_127
  · exact mod4_491
  · exact mod4_7
  · exact mod4_31
  · exact mod4_3847
  · exact mod4_7
  · exact mod4_23
  · exact mod4_127
  · exact mod4_7
  · exact mod4_1663
  · exact mod4_67
  · exact mod4_7
  · exact mod4_347
  · exact mod4_31
  · exact mod4_127
  · exact mod4_17471
  · exact mod4_131
  · exact mod4_7
  · exact mod4_31
  · exact mod4_2447
  · exact mod4_7
  · exact mod4_127
  · exact mod4_3823
  · exact mod4_7
  · exact mod4_15671
  · exact mod4_8179
  · exact mod4_7
  · exact mod4_3823
  · exact mod4_31
  · exact mod4_7
  · cases h_false

lemma blocking_prime_by_idx_59_3mod4 (idx : ℕ) : blocking_prime_by_idx_59 idx % 4 = 3 :=
  mod4_of_mem_blocking_primes_59 (getD_mem blocking_primes_59 (idx - 5900) 3)

def blocking_primes_60 : List ℕ := [3, 11, 31, 3, 5827, 11, 3, 31, 523, 3, 11, 11, 3, 1663, 8867, 3, 11, 31, 3, 1879, 11, 3, 31, 1279, 3, 11, 11, 3, 59, 47, 3, 11, 31, 3, 11839, 11, 3, 31, 59, 3, 3, 331, 11519, 3, 1451, 79, 3, 5303, 1459, 3, 1439, 3463, 3, 71, 227, 3, 331, 9043, 3, 7211, 17027, 3, 59, 1483, 3, 11503, 467, 3, 2063, 1879, 3, 331, 307, 3, 2711, 5779, 3, 11587, 827, 3, 179, 619, 59, 7, 11, 43, 7, 4639, 1103, 7, 4831, 2579, 7, 463, 11, 7, 3391, 4591, 7, 11]
def blocking_prime_by_idx_60 (idx : ℕ) : ℕ := blocking_primes_60.getD (idx - 6000) 3

lemma prime_of_mem_blocking_primes_60 {p : ℕ} (h : p ∈ 3 :: blocking_primes_60) : Nat.Prime p := by
  unfold blocking_primes_60 at h
  simp only [List.mem_cons] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | h_false
  · exact prime_3
  · exact prime_3
  · exact prime_11
  · exact prime_31
  · exact prime_3
  · exact prime_5827
  · exact prime_11
  · exact prime_3
  · exact prime_31
  · exact prime_523
  · exact prime_3
  · exact prime_11
  · exact prime_11
  · exact prime_3
  · exact prime_1663
  · exact prime_8867
  · exact prime_3
  · exact prime_11
  · exact prime_31
  · exact prime_3
  · exact prime_1879
  · exact prime_11
  · exact prime_3
  · exact prime_31
  · exact prime_1279
  · exact prime_3
  · exact prime_11
  · exact prime_11
  · exact prime_3
  · exact prime_59
  · exact prime_47
  · exact prime_3
  · exact prime_11
  · exact prime_31
  · exact prime_3
  · exact prime_11839
  · exact prime_11
  · exact prime_3
  · exact prime_31
  · exact prime_59
  · exact prime_3
  · exact prime_3
  · exact prime_331
  · exact prime_11519
  · exact prime_3
  · exact prime_1451
  · exact prime_79
  · exact prime_3
  · exact prime_5303
  · exact prime_1459
  · exact prime_3
  · exact prime_1439
  · exact prime_3463
  · exact prime_3
  · exact prime_71
  · exact prime_227
  · exact prime_3
  · exact prime_331
  · exact prime_9043
  · exact prime_3
  · exact prime_7211
  · exact prime_17027
  · exact prime_3
  · exact prime_59
  · exact prime_1483
  · exact prime_3
  · exact prime_11503
  · exact prime_467
  · exact prime_3
  · exact prime_2063
  · exact prime_1879
  · exact prime_3
  · exact prime_331
  · exact prime_307
  · exact prime_3
  · exact prime_2711
  · exact prime_5779
  · exact prime_3
  · exact prime_11587
  · exact prime_827
  · exact prime_3
  · exact prime_179
  · exact prime_619
  · exact prime_59
  · exact prime_7
  · exact prime_11
  · exact prime_43
  · exact prime_7
  · exact prime_4639
  · exact prime_1103
  · exact prime_7
  · exact prime_4831
  · exact prime_2579
  · exact prime_7
  · exact prime_463
  · exact prime_11
  · exact prime_7
  · exact prime_3391
  · exact prime_4591
  · exact prime_7
  · exact prime_11
  · cases h_false

lemma blocking_prime_by_idx_60_prime (idx : ℕ) : Nat.Prime (blocking_prime_by_idx_60 idx) :=
  prime_of_mem_blocking_primes_60 (getD_mem blocking_primes_60 (idx - 6000) 3)

lemma mod4_of_mem_blocking_primes_60 {p : ℕ} (h : p ∈ 3 :: blocking_primes_60) : p % 4 = 3 := by
  unfold blocking_primes_60 at h
  simp only [List.mem_cons] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | h_false
  · exact mod4_3
  · exact mod4_3
  · exact mod4_11
  · exact mod4_31
  · exact mod4_3
  · exact mod4_5827
  · exact mod4_11
  · exact mod4_3
  · exact mod4_31
  · exact mod4_523
  · exact mod4_3
  · exact mod4_11
  · exact mod4_11
  · exact mod4_3
  · exact mod4_1663
  · exact mod4_8867
  · exact mod4_3
  · exact mod4_11
  · exact mod4_31
  · exact mod4_3
  · exact mod4_1879
  · exact mod4_11
  · exact mod4_3
  · exact mod4_31
  · exact mod4_1279
  · exact mod4_3
  · exact mod4_11
  · exact mod4_11
  · exact mod4_3
  · exact mod4_59
  · exact mod4_47
  · exact mod4_3
  · exact mod4_11
  · exact mod4_31
  · exact mod4_3
  · exact mod4_11839
  · exact mod4_11
  · exact mod4_3
  · exact mod4_31
  · exact mod4_59
  · exact mod4_3
  · exact mod4_3
  · exact mod4_331
  · exact mod4_11519
  · exact mod4_3
  · exact mod4_1451
  · exact mod4_79
  · exact mod4_3
  · exact mod4_5303
  · exact mod4_1459
  · exact mod4_3
  · exact mod4_1439
  · exact mod4_3463
  · exact mod4_3
  · exact mod4_71
  · exact mod4_227
  · exact mod4_3
  · exact mod4_331
  · exact mod4_9043
  · exact mod4_3
  · exact mod4_7211
  · exact mod4_17027
  · exact mod4_3
  · exact mod4_59
  · exact mod4_1483
  · exact mod4_3
  · exact mod4_11503
  · exact mod4_467
  · exact mod4_3
  · exact mod4_2063
  · exact mod4_1879
  · exact mod4_3
  · exact mod4_331
  · exact mod4_307
  · exact mod4_3
  · exact mod4_2711
  · exact mod4_5779
  · exact mod4_3
  · exact mod4_11587
  · exact mod4_827
  · exact mod4_3
  · exact mod4_179
  · exact mod4_619
  · exact mod4_59
  · exact mod4_7
  · exact mod4_11
  · exact mod4_43
  · exact mod4_7
  · exact mod4_4639
  · exact mod4_1103
  · exact mod4_7
  · exact mod4_4831
  · exact mod4_2579
  · exact mod4_7
  · exact mod4_463
  · exact mod4_11
  · exact mod4_7
  · exact mod4_3391
  · exact mod4_4591
  · exact mod4_7
  · exact mod4_11
  · cases h_false

lemma blocking_prime_by_idx_60_3mod4 (idx : ℕ) : blocking_prime_by_idx_60 idx % 4 = 3 :=
  mod4_of_mem_blocking_primes_60 (getD_mem blocking_primes_60 (idx - 6000) 3)

def blocking_primes_61 : List ℕ := [607, 7583, 2663, 919, 7, 2087, 43, 7, 1087, 11, 7, 2339, 283, 7, 11, 10303, 7, 1103, 4007, 7, 3, 1747, 683, 3, 151, 167, 3, 8863, 6247, 3, 67, 7583, 3, 683, 331, 3, 2731, 827, 3, 151, 1951, 3, 7331, 47, 3, 743, 5147, 3, 3467, 331, 3, 1471, 3499, 3, 151, 683, 3, 3331, 7591, 3, 3, 19, 3607, 3, 47, 9967, 3, 17539, 31, 3, 19, 67, 3, 2939, 1327, 3, 5011, 967, 3, 19, 3907, 3, 14411, 31, 3, 991, 10859, 3, 19, 2539, 3, 3539, 2131, 3, 3371, 2971, 3, 19, 31, 3]
def blocking_prime_by_idx_61 (idx : ℕ) : ℕ := blocking_primes_61.getD (idx - 6100) 3

lemma prime_of_mem_blocking_primes_61 {p : ℕ} (h : p ∈ 3 :: blocking_primes_61) : Nat.Prime p := by
  unfold blocking_primes_61 at h
  simp only [List.mem_cons] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | h_false
  · exact prime_3
  · exact prime_607
  · exact prime_7583
  · exact prime_2663
  · exact prime_919
  · exact prime_7
  · exact prime_2087
  · exact prime_43
  · exact prime_7
  · exact prime_1087
  · exact prime_11
  · exact prime_7
  · exact prime_2339
  · exact prime_283
  · exact prime_7
  · exact prime_11
  · exact prime_10303
  · exact prime_7
  · exact prime_1103
  · exact prime_4007
  · exact prime_7
  · exact prime_3
  · exact prime_1747
  · exact prime_683
  · exact prime_3
  · exact prime_151
  · exact prime_167
  · exact prime_3
  · exact prime_8863
  · exact prime_6247
  · exact prime_3
  · exact prime_67
  · exact prime_7583
  · exact prime_3
  · exact prime_683
  · exact prime_331
  · exact prime_3
  · exact prime_2731
  · exact prime_827
  · exact prime_3
  · exact prime_151
  · exact prime_1951
  · exact prime_3
  · exact prime_7331
  · exact prime_47
  · exact prime_3
  · exact prime_743
  · exact prime_5147
  · exact prime_3
  · exact prime_3467
  · exact prime_331
  · exact prime_3
  · exact prime_1471
  · exact prime_3499
  · exact prime_3
  · exact prime_151
  · exact prime_683
  · exact prime_3
  · exact prime_3331
  · exact prime_7591
  · exact prime_3
  · exact prime_3
  · exact prime_19
  · exact prime_3607
  · exact prime_3
  · exact prime_47
  · exact prime_9967
  · exact prime_3
  · exact prime_17539
  · exact prime_31
  · exact prime_3
  · exact prime_19
  · exact prime_67
  · exact prime_3
  · exact prime_2939
  · exact prime_1327
  · exact prime_3
  · exact prime_5011
  · exact prime_967
  · exact prime_3
  · exact prime_19
  · exact prime_3907
  · exact prime_3
  · exact prime_14411
  · exact prime_31
  · exact prime_3
  · exact prime_991
  · exact prime_10859
  · exact prime_3
  · exact prime_19
  · exact prime_2539
  · exact prime_3
  · exact prime_3539
  · exact prime_2131
  · exact prime_3
  · exact prime_3371
  · exact prime_2971
  · exact prime_3
  · exact prime_19
  · exact prime_31
  · exact prime_3
  · cases h_false

lemma blocking_prime_by_idx_61_prime (idx : ℕ) : Nat.Prime (blocking_prime_by_idx_61 idx) :=
  prime_of_mem_blocking_primes_61 (getD_mem blocking_primes_61 (idx - 6100) 3)

lemma mod4_of_mem_blocking_primes_61 {p : ℕ} (h : p ∈ 3 :: blocking_primes_61) : p % 4 = 3 := by
  unfold blocking_primes_61 at h
  simp only [List.mem_cons] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | h_false
  · exact mod4_3
  · exact mod4_607
  · exact mod4_7583
  · exact mod4_2663
  · exact mod4_919
  · exact mod4_7
  · exact mod4_2087
  · exact mod4_43
  · exact mod4_7
  · exact mod4_1087
  · exact mod4_11
  · exact mod4_7
  · exact mod4_2339
  · exact mod4_283
  · exact mod4_7
  · exact mod4_11
  · exact mod4_10303
  · exact mod4_7
  · exact mod4_1103
  · exact mod4_4007
  · exact mod4_7
  · exact mod4_3
  · exact mod4_1747
  · exact mod4_683
  · exact mod4_3
  · exact mod4_151
  · exact mod4_167
  · exact mod4_3
  · exact mod4_8863
  · exact mod4_6247
  · exact mod4_3
  · exact mod4_67
  · exact mod4_7583
  · exact mod4_3
  · exact mod4_683
  · exact mod4_331
  · exact mod4_3
  · exact mod4_2731
  · exact mod4_827
  · exact mod4_3
  · exact mod4_151
  · exact mod4_1951
  · exact mod4_3
  · exact mod4_7331
  · exact mod4_47
  · exact mod4_3
  · exact mod4_743
  · exact mod4_5147
  · exact mod4_3
  · exact mod4_3467
  · exact mod4_331
  · exact mod4_3
  · exact mod4_1471
  · exact mod4_3499
  · exact mod4_3
  · exact mod4_151
  · exact mod4_683
  · exact mod4_3
  · exact mod4_3331
  · exact mod4_7591
  · exact mod4_3
  · exact mod4_3
  · exact mod4_19
  · exact mod4_3607
  · exact mod4_3
  · exact mod4_47
  · exact mod4_9967
  · exact mod4_3
  · exact mod4_17539
  · exact mod4_31
  · exact mod4_3
  · exact mod4_19
  · exact mod4_67
  · exact mod4_3
  · exact mod4_2939
  · exact mod4_1327
  · exact mod4_3
  · exact mod4_5011
  · exact mod4_967
  · exact mod4_3
  · exact mod4_19
  · exact mod4_3907
  · exact mod4_3
  · exact mod4_14411
  · exact mod4_31
  · exact mod4_3
  · exact mod4_991
  · exact mod4_10859
  · exact mod4_3
  · exact mod4_19
  · exact mod4_2539
  · exact mod4_3
  · exact mod4_3539
  · exact mod4_2131
  · exact mod4_3
  · exact mod4_3371
  · exact mod4_2971
  · exact mod4_3
  · exact mod4_19
  · exact mod4_31
  · exact mod4_3
  · cases h_false

lemma blocking_prime_by_idx_61_3mod4 (idx : ℕ) : blocking_prime_by_idx_61 idx % 4 = 3 :=
  mod4_of_mem_blocking_primes_61 (getD_mem blocking_primes_61 (idx - 6100) 3)

def blocking_primes_62 : List ℕ := [7, 11, 31, 7, 127, 11, 7, 31, 2927, 7, 31, 127, 7, 199, 5419, 7, 11, 31, 127, 5531, 11, 7, 31, 43, 7, 11, 11, 7, 4447, 8747, 7, 11, 31, 7, 107, 11, 7, 31, 811, 79, 3, 23, 8219, 3, 251, 9059, 3, 599, 19, 3, 127, 1291, 3, 67, 12527, 3, 83, 19, 3, 619, 1559, 3, 9551, 23, 3, 7351, 19, 3, 2251, 251, 3, 127, 887, 3, 23, 1543, 3, 4523, 127, 3, 3, 5011, 6011, 3, 11, 211, 3, 8191, 751, 3, 107, 4091, 3, 307, 11, 3, 2531, 2843, 3, 11]
def blocking_prime_by_idx_62 (idx : ℕ) : ℕ := blocking_primes_62.getD (idx - 6200) 3

lemma prime_of_mem_blocking_primes_62 {p : ℕ} (h : p ∈ 3 :: blocking_primes_62) : Nat.Prime p := by
  unfold blocking_primes_62 at h
  simp only [List.mem_cons] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | h_false
  · exact prime_3
  · exact prime_7
  · exact prime_11
  · exact prime_31
  · exact prime_7
  · exact prime_127
  · exact prime_11
  · exact prime_7
  · exact prime_31
  · exact prime_2927
  · exact prime_7
  · exact prime_31
  · exact prime_127
  · exact prime_7
  · exact prime_199
  · exact prime_5419
  · exact prime_7
  · exact prime_11
  · exact prime_31
  · exact prime_127
  · exact prime_5531
  · exact prime_11
  · exact prime_7
  · exact prime_31
  · exact prime_43
  · exact prime_7
  · exact prime_11
  · exact prime_11
  · exact prime_7
  · exact prime_4447
  · exact prime_8747
  · exact prime_7
  · exact prime_11
  · exact prime_31
  · exact prime_7
  · exact prime_107
  · exact prime_11
  · exact prime_7
  · exact prime_31
  · exact prime_811
  · exact prime_79
  · exact prime_3
  · exact prime_23
  · exact prime_8219
  · exact prime_3
  · exact prime_251
  · exact prime_9059
  · exact prime_3
  · exact prime_599
  · exact prime_19
  · exact prime_3
  · exact prime_127
  · exact prime_1291
  · exact prime_3
  · exact prime_67
  · exact prime_12527
  · exact prime_3
  · exact prime_83
  · exact prime_19
  · exact prime_3
  · exact prime_619
  · exact prime_1559
  · exact prime_3
  · exact prime_9551
  · exact prime_23
  · exact prime_3
  · exact prime_7351
  · exact prime_19
  · exact prime_3
  · exact prime_2251
  · exact prime_251
  · exact prime_3
  · exact prime_127
  · exact prime_887
  · exact prime_3
  · exact prime_23
  · exact prime_1543
  · exact prime_3
  · exact prime_4523
  · exact prime_127
  · exact prime_3
  · exact prime_3
  · exact prime_5011
  · exact prime_6011
  · exact prime_3
  · exact prime_11
  · exact prime_211
  · exact prime_3
  · exact prime_8191
  · exact prime_751
  · exact prime_3
  · exact prime_107
  · exact prime_4091
  · exact prime_3
  · exact prime_307
  · exact prime_11
  · exact prime_3
  · exact prime_2531
  · exact prime_2843
  · exact prime_3
  · exact prime_11
  · cases h_false

lemma blocking_prime_by_idx_62_prime (idx : ℕ) : Nat.Prime (blocking_prime_by_idx_62 idx) :=
  prime_of_mem_blocking_primes_62 (getD_mem blocking_primes_62 (idx - 6200) 3)

lemma mod4_of_mem_blocking_primes_62 {p : ℕ} (h : p ∈ 3 :: blocking_primes_62) : p % 4 = 3 := by
  unfold blocking_primes_62 at h
  simp only [List.mem_cons] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | h_false
  · exact mod4_3
  · exact mod4_7
  · exact mod4_11
  · exact mod4_31
  · exact mod4_7
  · exact mod4_127
  · exact mod4_11
  · exact mod4_7
  · exact mod4_31
  · exact mod4_2927
  · exact mod4_7
  · exact mod4_31
  · exact mod4_127
  · exact mod4_7
  · exact mod4_199
  · exact mod4_5419
  · exact mod4_7
  · exact mod4_11
  · exact mod4_31
  · exact mod4_127
  · exact mod4_5531
  · exact mod4_11
  · exact mod4_7
  · exact mod4_31
  · exact mod4_43
  · exact mod4_7
  · exact mod4_11
  · exact mod4_11
  · exact mod4_7
  · exact mod4_4447
  · exact mod4_8747
  · exact mod4_7
  · exact mod4_11
  · exact mod4_31
  · exact mod4_7
  · exact mod4_107
  · exact mod4_11
  · exact mod4_7
  · exact mod4_31
  · exact mod4_811
  · exact mod4_79
  · exact mod4_3
  · exact mod4_23
  · exact mod4_8219
  · exact mod4_3
  · exact mod4_251
  · exact mod4_9059
  · exact mod4_3
  · exact mod4_599
  · exact mod4_19
  · exact mod4_3
  · exact mod4_127
  · exact mod4_1291
  · exact mod4_3
  · exact mod4_67
  · exact mod4_12527
  · exact mod4_3
  · exact mod4_83
  · exact mod4_19
  · exact mod4_3
  · exact mod4_619
  · exact mod4_1559
  · exact mod4_3
  · exact mod4_9551
  · exact mod4_23
  · exact mod4_3
  · exact mod4_7351
  · exact mod4_19
  · exact mod4_3
  · exact mod4_2251
  · exact mod4_251
  · exact mod4_3
  · exact mod4_127
  · exact mod4_887
  · exact mod4_3
  · exact mod4_23
  · exact mod4_1543
  · exact mod4_3
  · exact mod4_4523
  · exact mod4_127
  · exact mod4_3
  · exact mod4_3
  · exact mod4_5011
  · exact mod4_6011
  · exact mod4_3
  · exact mod4_11
  · exact mod4_211
  · exact mod4_3
  · exact mod4_8191
  · exact mod4_751
  · exact mod4_3
  · exact mod4_107
  · exact mod4_4091
  · exact mod4_3
  · exact mod4_307
  · exact mod4_11
  · exact mod4_3
  · exact mod4_2531
  · exact mod4_2843
  · exact mod4_3
  · exact mod4_11
  · cases h_false

lemma blocking_prime_by_idx_62_3mod4 (idx : ℕ) : blocking_prime_by_idx_62 idx % 4 = 3 :=
  mod4_of_mem_blocking_primes_62 (getD_mem blocking_primes_62 (idx - 6200) 3)

def blocking_primes_63 : List ℕ := [179, 3, 919, 83, 3, 431, 643, 3, 271, 1559, 3, 683, 751, 3, 11, 103, 3, 1619, 13619, 3, 7, 1583, 6971, 7, 659, 3359, 7, 283, 79, 7, 23, 839, 7, 2851, 787, 6899, 4751, 167, 7, 8191, 643, 7, 1223, 1531, 7, 191, 3019, 7, 8839, 2687, 7, 1063, 23, 7, 2351, 7643, 8243, 383, 2543, 7, 3, 103, 167, 3, 6971, 43, 3, 3847, 31, 3, 2731, 23, 3, 31, 4643, 3, 7823, 23, 3, 43, 2143, 3, 23, 31, 3, 727, 43, 3, 31, 1123, 3, 547, 563, 3, 167, 4523, 3, 6947, 31, 3]
def blocking_prime_by_idx_63 (idx : ℕ) : ℕ := blocking_primes_63.getD (idx - 6300) 3

lemma prime_of_mem_blocking_primes_63 {p : ℕ} (h : p ∈ 3 :: blocking_primes_63) : Nat.Prime p := by
  unfold blocking_primes_63 at h
  simp only [List.mem_cons] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | h_false
  · exact prime_3
  · exact prime_179
  · exact prime_3
  · exact prime_919
  · exact prime_83
  · exact prime_3
  · exact prime_431
  · exact prime_643
  · exact prime_3
  · exact prime_271
  · exact prime_1559
  · exact prime_3
  · exact prime_683
  · exact prime_751
  · exact prime_3
  · exact prime_11
  · exact prime_103
  · exact prime_3
  · exact prime_1619
  · exact prime_13619
  · exact prime_3
  · exact prime_7
  · exact prime_1583
  · exact prime_6971
  · exact prime_7
  · exact prime_659
  · exact prime_3359
  · exact prime_7
  · exact prime_283
  · exact prime_79
  · exact prime_7
  · exact prime_23
  · exact prime_839
  · exact prime_7
  · exact prime_2851
  · exact prime_787
  · exact prime_6899
  · exact prime_4751
  · exact prime_167
  · exact prime_7
  · exact prime_8191
  · exact prime_643
  · exact prime_7
  · exact prime_1223
  · exact prime_1531
  · exact prime_7
  · exact prime_191
  · exact prime_3019
  · exact prime_7
  · exact prime_8839
  · exact prime_2687
  · exact prime_7
  · exact prime_1063
  · exact prime_23
  · exact prime_7
  · exact prime_2351
  · exact prime_7643
  · exact prime_8243
  · exact prime_383
  · exact prime_2543
  · exact prime_7
  · exact prime_3
  · exact prime_103
  · exact prime_167
  · exact prime_3
  · exact prime_6971
  · exact prime_43
  · exact prime_3
  · exact prime_3847
  · exact prime_31
  · exact prime_3
  · exact prime_2731
  · exact prime_23
  · exact prime_3
  · exact prime_31
  · exact prime_4643
  · exact prime_3
  · exact prime_7823
  · exact prime_23
  · exact prime_3
  · exact prime_43
  · exact prime_2143
  · exact prime_3
  · exact prime_23
  · exact prime_31
  · exact prime_3
  · exact prime_727
  · exact prime_43
  · exact prime_3
  · exact prime_31
  · exact prime_1123
  · exact prime_3
  · exact prime_547
  · exact prime_563
  · exact prime_3
  · exact prime_167
  · exact prime_4523
  · exact prime_3
  · exact prime_6947
  · exact prime_31
  · exact prime_3
  · cases h_false

lemma blocking_prime_by_idx_63_prime (idx : ℕ) : Nat.Prime (blocking_prime_by_idx_63 idx) :=
  prime_of_mem_blocking_primes_63 (getD_mem blocking_primes_63 (idx - 6300) 3)

lemma mod4_of_mem_blocking_primes_63 {p : ℕ} (h : p ∈ 3 :: blocking_primes_63) : p % 4 = 3 := by
  unfold blocking_primes_63 at h
  simp only [List.mem_cons] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | h_false
  · exact mod4_3
  · exact mod4_179
  · exact mod4_3
  · exact mod4_919
  · exact mod4_83
  · exact mod4_3
  · exact mod4_431
  · exact mod4_643
  · exact mod4_3
  · exact mod4_271
  · exact mod4_1559
  · exact mod4_3
  · exact mod4_683
  · exact mod4_751
  · exact mod4_3
  · exact mod4_11
  · exact mod4_103
  · exact mod4_3
  · exact mod4_1619
  · exact mod4_13619
  · exact mod4_3
  · exact mod4_7
  · exact mod4_1583
  · exact mod4_6971
  · exact mod4_7
  · exact mod4_659
  · exact mod4_3359
  · exact mod4_7
  · exact mod4_283
  · exact mod4_79
  · exact mod4_7
  · exact mod4_23
  · exact mod4_839
  · exact mod4_7
  · exact mod4_2851
  · exact mod4_787
  · exact mod4_6899
  · exact mod4_4751
  · exact mod4_167
  · exact mod4_7
  · exact mod4_8191
  · exact mod4_643
  · exact mod4_7
  · exact mod4_1223
  · exact mod4_1531
  · exact mod4_7
  · exact mod4_191
  · exact mod4_3019
  · exact mod4_7
  · exact mod4_8839
  · exact mod4_2687
  · exact mod4_7
  · exact mod4_1063
  · exact mod4_23
  · exact mod4_7
  · exact mod4_2351
  · exact mod4_7643
  · exact mod4_8243
  · exact mod4_383
  · exact mod4_2543
  · exact mod4_7
  · exact mod4_3
  · exact mod4_103
  · exact mod4_167
  · exact mod4_3
  · exact mod4_6971
  · exact mod4_43
  · exact mod4_3
  · exact mod4_3847
  · exact mod4_31
  · exact mod4_3
  · exact mod4_2731
  · exact mod4_23
  · exact mod4_3
  · exact mod4_31
  · exact mod4_4643
  · exact mod4_3
  · exact mod4_7823
  · exact mod4_23
  · exact mod4_3
  · exact mod4_43
  · exact mod4_2143
  · exact mod4_3
  · exact mod4_23
  · exact mod4_31
  · exact mod4_3
  · exact mod4_727
  · exact mod4_43
  · exact mod4_3
  · exact mod4_31
  · exact mod4_1123
  · exact mod4_3
  · exact mod4_547
  · exact mod4_563
  · exact mod4_3
  · exact mod4_167
  · exact mod4_4523
  · exact mod4_3
  · exact mod4_6947
  · exact mod4_31
  · exact mod4_3
  · cases h_false

lemma blocking_prime_by_idx_63_3mod4 (idx : ℕ) : blocking_prime_by_idx_63 idx % 4 = 3 :=
  mod4_of_mem_blocking_primes_63 (getD_mem blocking_primes_63 (idx - 6300) 3)

def blocking_primes_64 : List ℕ := [7]
def blocking_prime_by_idx_64 (idx : ℕ) : ℕ := blocking_primes_64.getD (idx - 6400) 3

lemma prime_of_mem_blocking_primes_64 {p : ℕ} (h : p ∈ 3 :: blocking_primes_64) : Nat.Prime p := by
  unfold blocking_primes_64 at h
  simp only [List.mem_cons] at h
  rcases h with rfl | rfl | h_false
  · exact prime_3
  · exact prime_7
  · cases h_false

lemma blocking_prime_by_idx_64_prime (idx : ℕ) : Nat.Prime (blocking_prime_by_idx_64 idx) :=
  prime_of_mem_blocking_primes_64 (getD_mem blocking_primes_64 (idx - 6400) 3)

lemma mod4_of_mem_blocking_primes_64 {p : ℕ} (h : p ∈ 3 :: blocking_primes_64) : p % 4 = 3 := by
  unfold blocking_primes_64 at h
  simp only [List.mem_cons] at h
  rcases h with rfl | rfl | h_false
  · exact mod4_3
  · exact mod4_7
  · cases h_false

lemma blocking_prime_by_idx_64_3mod4 (idx : ℕ) : blocking_prime_by_idx_64 idx % 4 = 3 :=
  mod4_of_mem_blocking_primes_64 (getD_mem blocking_primes_64 (idx - 6400) 3)

def blocking_prime_by_idx (idx : ℕ) : ℕ :=
  match idx / 100 with
  | 0 => blocking_prime_by_idx_0 idx
  | 1 => blocking_prime_by_idx_1 idx
  | 2 => blocking_prime_by_idx_2 idx
  | 3 => blocking_prime_by_idx_3 idx
  | 4 => blocking_prime_by_idx_4 idx
  | 5 => blocking_prime_by_idx_5 idx
  | 6 => blocking_prime_by_idx_6 idx
  | 7 => blocking_prime_by_idx_7 idx
  | 8 => blocking_prime_by_idx_8 idx
  | 9 => blocking_prime_by_idx_9 idx
  | 10 => blocking_prime_by_idx_10 idx
  | 11 => blocking_prime_by_idx_11 idx
  | 12 => blocking_prime_by_idx_12 idx
  | 13 => blocking_prime_by_idx_13 idx
  | 14 => blocking_prime_by_idx_14 idx
  | 15 => blocking_prime_by_idx_15 idx
  | 16 => blocking_prime_by_idx_16 idx
  | 17 => blocking_prime_by_idx_17 idx
  | 18 => blocking_prime_by_idx_18 idx
  | 19 => blocking_prime_by_idx_19 idx
  | 20 => blocking_prime_by_idx_20 idx
  | 21 => blocking_prime_by_idx_21 idx
  | 22 => blocking_prime_by_idx_22 idx
  | 23 => blocking_prime_by_idx_23 idx
  | 24 => blocking_prime_by_idx_24 idx
  | 25 => blocking_prime_by_idx_25 idx
  | 26 => blocking_prime_by_idx_26 idx
  | 27 => blocking_prime_by_idx_27 idx
  | 28 => blocking_prime_by_idx_28 idx
  | 29 => blocking_prime_by_idx_29 idx
  | 30 => blocking_prime_by_idx_30 idx
  | 31 => blocking_prime_by_idx_31 idx
  | 32 => blocking_prime_by_idx_32 idx
  | 33 => blocking_prime_by_idx_33 idx
  | 34 => blocking_prime_by_idx_34 idx
  | 35 => blocking_prime_by_idx_35 idx
  | 36 => blocking_prime_by_idx_36 idx
  | 37 => blocking_prime_by_idx_37 idx
  | 38 => blocking_prime_by_idx_38 idx
  | 39 => blocking_prime_by_idx_39 idx
  | 40 => blocking_prime_by_idx_40 idx
  | 41 => blocking_prime_by_idx_41 idx
  | 42 => blocking_prime_by_idx_42 idx
  | 43 => blocking_prime_by_idx_43 idx
  | 44 => blocking_prime_by_idx_44 idx
  | 45 => blocking_prime_by_idx_45 idx
  | 46 => blocking_prime_by_idx_46 idx
  | 47 => blocking_prime_by_idx_47 idx
  | 48 => blocking_prime_by_idx_48 idx
  | 49 => blocking_prime_by_idx_49 idx
  | 50 => blocking_prime_by_idx_50 idx
  | 51 => blocking_prime_by_idx_51 idx
  | 52 => blocking_prime_by_idx_52 idx
  | 53 => blocking_prime_by_idx_53 idx
  | 54 => blocking_prime_by_idx_54 idx
  | 55 => blocking_prime_by_idx_55 idx
  | 56 => blocking_prime_by_idx_56 idx
  | 57 => blocking_prime_by_idx_57 idx
  | 58 => blocking_prime_by_idx_58 idx
  | 59 => blocking_prime_by_idx_59 idx
  | 60 => blocking_prime_by_idx_60 idx
  | 61 => blocking_prime_by_idx_61 idx
  | 62 => blocking_prime_by_idx_62 idx
  | 63 => blocking_prime_by_idx_63 idx
  | _ => blocking_prime_by_idx_64 idx

lemma blocking_prime_by_idx_prime (idx : ℕ) : Nat.Prime (blocking_prime_by_idx idx) :=
  by
    unfold blocking_prime_by_idx
    split
    · exact blocking_prime_by_idx_0_prime idx
    · exact blocking_prime_by_idx_1_prime idx
    · exact blocking_prime_by_idx_2_prime idx
    · exact blocking_prime_by_idx_3_prime idx
    · exact blocking_prime_by_idx_4_prime idx
    · exact blocking_prime_by_idx_5_prime idx
    · exact blocking_prime_by_idx_6_prime idx
    · exact blocking_prime_by_idx_7_prime idx
    · exact blocking_prime_by_idx_8_prime idx
    · exact blocking_prime_by_idx_9_prime idx
    · exact blocking_prime_by_idx_10_prime idx
    · exact blocking_prime_by_idx_11_prime idx
    · exact blocking_prime_by_idx_12_prime idx
    · exact blocking_prime_by_idx_13_prime idx
    · exact blocking_prime_by_idx_14_prime idx
    · exact blocking_prime_by_idx_15_prime idx
    · exact blocking_prime_by_idx_16_prime idx
    · exact blocking_prime_by_idx_17_prime idx
    · exact blocking_prime_by_idx_18_prime idx
    · exact blocking_prime_by_idx_19_prime idx
    · exact blocking_prime_by_idx_20_prime idx
    · exact blocking_prime_by_idx_21_prime idx
    · exact blocking_prime_by_idx_22_prime idx
    · exact blocking_prime_by_idx_23_prime idx
    · exact blocking_prime_by_idx_24_prime idx
    · exact blocking_prime_by_idx_25_prime idx
    · exact blocking_prime_by_idx_26_prime idx
    · exact blocking_prime_by_idx_27_prime idx
    · exact blocking_prime_by_idx_28_prime idx
    · exact blocking_prime_by_idx_29_prime idx
    · exact blocking_prime_by_idx_30_prime idx
    · exact blocking_prime_by_idx_31_prime idx
    · exact blocking_prime_by_idx_32_prime idx
    · exact blocking_prime_by_idx_33_prime idx
    · exact blocking_prime_by_idx_34_prime idx
    · exact blocking_prime_by_idx_35_prime idx
    · exact blocking_prime_by_idx_36_prime idx
    · exact blocking_prime_by_idx_37_prime idx
    · exact blocking_prime_by_idx_38_prime idx
    · exact blocking_prime_by_idx_39_prime idx
    · exact blocking_prime_by_idx_40_prime idx
    · exact blocking_prime_by_idx_41_prime idx
    · exact blocking_prime_by_idx_42_prime idx
    · exact blocking_prime_by_idx_43_prime idx
    · exact blocking_prime_by_idx_44_prime idx
    · exact blocking_prime_by_idx_45_prime idx
    · exact blocking_prime_by_idx_46_prime idx
    · exact blocking_prime_by_idx_47_prime idx
    · exact blocking_prime_by_idx_48_prime idx
    · exact blocking_prime_by_idx_49_prime idx
    · exact blocking_prime_by_idx_50_prime idx
    · exact blocking_prime_by_idx_51_prime idx
    · exact blocking_prime_by_idx_52_prime idx
    · exact blocking_prime_by_idx_53_prime idx
    · exact blocking_prime_by_idx_54_prime idx
    · exact blocking_prime_by_idx_55_prime idx
    · exact blocking_prime_by_idx_56_prime idx
    · exact blocking_prime_by_idx_57_prime idx
    · exact blocking_prime_by_idx_58_prime idx
    · exact blocking_prime_by_idx_59_prime idx
    · exact blocking_prime_by_idx_60_prime idx
    · exact blocking_prime_by_idx_61_prime idx
    · exact blocking_prime_by_idx_62_prime idx
    · exact blocking_prime_by_idx_63_prime idx
    · exact blocking_prime_by_idx_64_prime idx

lemma blocking_prime_by_idx_3mod4 (idx : ℕ) : blocking_prime_by_idx idx % 4 = 3 :=
  by
    unfold blocking_prime_by_idx
    split
    · exact blocking_prime_by_idx_0_3mod4 idx
    · exact blocking_prime_by_idx_1_3mod4 idx
    · exact blocking_prime_by_idx_2_3mod4 idx
    · exact blocking_prime_by_idx_3_3mod4 idx
    · exact blocking_prime_by_idx_4_3mod4 idx
    · exact blocking_prime_by_idx_5_3mod4 idx
    · exact blocking_prime_by_idx_6_3mod4 idx
    · exact blocking_prime_by_idx_7_3mod4 idx
    · exact blocking_prime_by_idx_8_3mod4 idx
    · exact blocking_prime_by_idx_9_3mod4 idx
    · exact blocking_prime_by_idx_10_3mod4 idx
    · exact blocking_prime_by_idx_11_3mod4 idx
    · exact blocking_prime_by_idx_12_3mod4 idx
    · exact blocking_prime_by_idx_13_3mod4 idx
    · exact blocking_prime_by_idx_14_3mod4 idx
    · exact blocking_prime_by_idx_15_3mod4 idx
    · exact blocking_prime_by_idx_16_3mod4 idx
    · exact blocking_prime_by_idx_17_3mod4 idx
    · exact blocking_prime_by_idx_18_3mod4 idx
    · exact blocking_prime_by_idx_19_3mod4 idx
    · exact blocking_prime_by_idx_20_3mod4 idx
    · exact blocking_prime_by_idx_21_3mod4 idx
    · exact blocking_prime_by_idx_22_3mod4 idx
    · exact blocking_prime_by_idx_23_3mod4 idx
    · exact blocking_prime_by_idx_24_3mod4 idx
    · exact blocking_prime_by_idx_25_3mod4 idx
    · exact blocking_prime_by_idx_26_3mod4 idx
    · exact blocking_prime_by_idx_27_3mod4 idx
    · exact blocking_prime_by_idx_28_3mod4 idx
    · exact blocking_prime_by_idx_29_3mod4 idx
    · exact blocking_prime_by_idx_30_3mod4 idx
    · exact blocking_prime_by_idx_31_3mod4 idx
    · exact blocking_prime_by_idx_32_3mod4 idx
    · exact blocking_prime_by_idx_33_3mod4 idx
    · exact blocking_prime_by_idx_34_3mod4 idx
    · exact blocking_prime_by_idx_35_3mod4 idx
    · exact blocking_prime_by_idx_36_3mod4 idx
    · exact blocking_prime_by_idx_37_3mod4 idx
    · exact blocking_prime_by_idx_38_3mod4 idx
    · exact blocking_prime_by_idx_39_3mod4 idx
    · exact blocking_prime_by_idx_40_3mod4 idx
    · exact blocking_prime_by_idx_41_3mod4 idx
    · exact blocking_prime_by_idx_42_3mod4 idx
    · exact blocking_prime_by_idx_43_3mod4 idx
    · exact blocking_prime_by_idx_44_3mod4 idx
    · exact blocking_prime_by_idx_45_3mod4 idx
    · exact blocking_prime_by_idx_46_3mod4 idx
    · exact blocking_prime_by_idx_47_3mod4 idx
    · exact blocking_prime_by_idx_48_3mod4 idx
    · exact blocking_prime_by_idx_49_3mod4 idx
    · exact blocking_prime_by_idx_50_3mod4 idx
    · exact blocking_prime_by_idx_51_3mod4 idx
    · exact blocking_prime_by_idx_52_3mod4 idx
    · exact blocking_prime_by_idx_53_3mod4 idx
    · exact blocking_prime_by_idx_54_3mod4 idx
    · exact blocking_prime_by_idx_55_3mod4 idx
    · exact blocking_prime_by_idx_56_3mod4 idx
    · exact blocking_prime_by_idx_57_3mod4 idx
    · exact blocking_prime_by_idx_58_3mod4 idx
    · exact blocking_prime_by_idx_59_3mod4 idx
    · exact blocking_prime_by_idx_60_3mod4 idx
    · exact blocking_prime_by_idx_61_3mod4 idx
    · exact blocking_prime_by_idx_62_3mod4 idx
    · exact blocking_prime_by_idx_63_3mod4 idx
    · exact blocking_prime_by_idx_64_3mod4 idx

def is_blocked_by_idx (idx : ℕ) : Bool :=
  let p := blocking_prime_by_idx idx
  let v := if idx = 6400 then 1 else 4^(idx / 40) * (10 * 16^(idx % 40) + 16 * 4^(idx % 40) + 10) / 9
  (N^2 - v) % p == 0 && (N^2 - v) % (p^2) != 0

lemma is_blocked_chunk_0 : ∀ idx < 100, is_blocked_by_idx (idx + 0) = true := by decide
lemma is_blocked_chunk_1 : ∀ idx < 100, is_blocked_by_idx (idx + 100) = true := by decide
lemma is_blocked_chunk_2 : ∀ idx < 100, is_blocked_by_idx (idx + 200) = true := by decide
lemma is_blocked_chunk_3 : ∀ idx < 100, is_blocked_by_idx (idx + 300) = true := by decide
lemma is_blocked_chunk_4 : ∀ idx < 100, is_blocked_by_idx (idx + 400) = true := by decide
lemma is_blocked_chunk_5 : ∀ idx < 100, is_blocked_by_idx (idx + 500) = true := by decide
lemma is_blocked_chunk_6 : ∀ idx < 100, is_blocked_by_idx (idx + 600) = true := by decide
lemma is_blocked_chunk_7 : ∀ idx < 100, is_blocked_by_idx (idx + 700) = true := by decide
lemma is_blocked_chunk_8 : ∀ idx < 100, is_blocked_by_idx (idx + 800) = true := by decide
lemma is_blocked_chunk_9 : ∀ idx < 100, is_blocked_by_idx (idx + 900) = true := by decide
lemma is_blocked_chunk_10 : ∀ idx < 100, is_blocked_by_idx (idx + 1000) = true := by decide
lemma is_blocked_chunk_11 : ∀ idx < 100, is_blocked_by_idx (idx + 1100) = true := by decide
lemma is_blocked_chunk_12 : ∀ idx < 100, is_blocked_by_idx (idx + 1200) = true := by decide
lemma is_blocked_chunk_13 : ∀ idx < 100, is_blocked_by_idx (idx + 1300) = true := by decide
lemma is_blocked_chunk_14 : ∀ idx < 100, is_blocked_by_idx (idx + 1400) = true := by decide
lemma is_blocked_chunk_15 : ∀ idx < 100, is_blocked_by_idx (idx + 1500) = true := by decide
lemma is_blocked_chunk_16 : ∀ idx < 100, is_blocked_by_idx (idx + 1600) = true := by decide
lemma is_blocked_chunk_17 : ∀ idx < 100, is_blocked_by_idx (idx + 1700) = true := by decide
lemma is_blocked_chunk_18 : ∀ idx < 100, is_blocked_by_idx (idx + 1800) = true := by decide
lemma is_blocked_chunk_19 : ∀ idx < 100, is_blocked_by_idx (idx + 1900) = true := by decide
lemma is_blocked_chunk_20 : ∀ idx < 100, is_blocked_by_idx (idx + 2000) = true := by decide
lemma is_blocked_chunk_21 : ∀ idx < 100, is_blocked_by_idx (idx + 2100) = true := by decide
lemma is_blocked_chunk_22 : ∀ idx < 100, is_blocked_by_idx (idx + 2200) = true := by decide
lemma is_blocked_chunk_23 : ∀ idx < 100, is_blocked_by_idx (idx + 2300) = true := by decide
lemma is_blocked_chunk_24 : ∀ idx < 100, is_blocked_by_idx (idx + 2400) = true := by decide
lemma is_blocked_chunk_25 : ∀ idx < 100, is_blocked_by_idx (idx + 2500) = true := by decide
lemma is_blocked_chunk_26 : ∀ idx < 100, is_blocked_by_idx (idx + 2600) = true := by decide
lemma is_blocked_chunk_27 : ∀ idx < 100, is_blocked_by_idx (idx + 2700) = true := by decide
lemma is_blocked_chunk_28 : ∀ idx < 100, is_blocked_by_idx (idx + 2800) = true := by decide
lemma is_blocked_chunk_29 : ∀ idx < 100, is_blocked_by_idx (idx + 2900) = true := by decide
lemma is_blocked_chunk_30 : ∀ idx < 100, is_blocked_by_idx (idx + 3000) = true := by decide
lemma is_blocked_chunk_31 : ∀ idx < 100, is_blocked_by_idx (idx + 3100) = true := by decide
lemma is_blocked_chunk_32 : ∀ idx < 100, is_blocked_by_idx (idx + 3200) = true := by decide
lemma is_blocked_chunk_33 : ∀ idx < 100, is_blocked_by_idx (idx + 3300) = true := by decide
lemma is_blocked_chunk_34 : ∀ idx < 100, is_blocked_by_idx (idx + 3400) = true := by decide
lemma is_blocked_chunk_35 : ∀ idx < 100, is_blocked_by_idx (idx + 3500) = true := by decide
lemma is_blocked_chunk_36 : ∀ idx < 100, is_blocked_by_idx (idx + 3600) = true := by decide
lemma is_blocked_chunk_37 : ∀ idx < 100, is_blocked_by_idx (idx + 3700) = true := by decide
lemma is_blocked_chunk_38 : ∀ idx < 100, is_blocked_by_idx (idx + 3800) = true := by decide
lemma is_blocked_chunk_39 : ∀ idx < 100, is_blocked_by_idx (idx + 3900) = true := by decide
lemma is_blocked_chunk_40 : ∀ idx < 100, is_blocked_by_idx (idx + 4000) = true := by decide
lemma is_blocked_chunk_41 : ∀ idx < 100, is_blocked_by_idx (idx + 4100) = true := by decide
lemma is_blocked_chunk_42 : ∀ idx < 100, is_blocked_by_idx (idx + 4200) = true := by decide
lemma is_blocked_chunk_43 : ∀ idx < 100, is_blocked_by_idx (idx + 4300) = true := by decide
lemma is_blocked_chunk_44 : ∀ idx < 100, is_blocked_by_idx (idx + 4400) = true := by decide
lemma is_blocked_chunk_45 : ∀ idx < 100, is_blocked_by_idx (idx + 4500) = true := by decide
lemma is_blocked_chunk_46 : ∀ idx < 100, is_blocked_by_idx (idx + 4600) = true := by decide
lemma is_blocked_chunk_47 : ∀ idx < 100, is_blocked_by_idx (idx + 4700) = true := by decide
lemma is_blocked_chunk_48 : ∀ idx < 100, is_blocked_by_idx (idx + 4800) = true := by decide
lemma is_blocked_chunk_49 : ∀ idx < 100, is_blocked_by_idx (idx + 4900) = true := by decide
lemma is_blocked_chunk_50 : ∀ idx < 100, is_blocked_by_idx (idx + 5000) = true := by decide
lemma is_blocked_chunk_51 : ∀ idx < 100, is_blocked_by_idx (idx + 5100) = true := by decide
lemma is_blocked_chunk_52 : ∀ idx < 100, is_blocked_by_idx (idx + 5200) = true := by decide
lemma is_blocked_chunk_53 : ∀ idx < 100, is_blocked_by_idx (idx + 5300) = true := by decide
lemma is_blocked_chunk_54 : ∀ idx < 100, is_blocked_by_idx (idx + 5400) = true := by decide
lemma is_blocked_chunk_55 : ∀ idx < 100, is_blocked_by_idx (idx + 5500) = true := by decide
lemma is_blocked_chunk_56 : ∀ idx < 100, is_blocked_by_idx (idx + 5600) = true := by decide
lemma is_blocked_chunk_57 : ∀ idx < 100, is_blocked_by_idx (idx + 5700) = true := by decide
lemma is_blocked_chunk_58 : ∀ idx < 100, is_blocked_by_idx (idx + 5800) = true := by decide
lemma is_blocked_chunk_59 : ∀ idx < 100, is_blocked_by_idx (idx + 5900) = true := by decide
lemma is_blocked_chunk_60 : ∀ idx < 100, is_blocked_by_idx (idx + 6000) = true := by decide
lemma is_blocked_chunk_61 : ∀ idx < 100, is_blocked_by_idx (idx + 6100) = true := by decide
lemma is_blocked_chunk_62 : ∀ idx < 100, is_blocked_by_idx (idx + 6200) = true := by decide
lemma is_blocked_chunk_63 : ∀ idx < 100, is_blocked_by_idx (idx + 6300) = true := by decide
lemma is_blocked_chunk_64 : ∀ idx < 100, is_blocked_by_idx (idx + 6400) = true := by decide

theorem is_blocked_all : ∀ idx < 6401, is_blocked_by_idx idx = true := by
  intro idx h_lt
  have h_cases : (idx ≥ 0 ∧ idx < 100) ∨ (idx ≥ 100 ∧ idx < 200) ∨ (idx ≥ 200 ∧ idx < 300) ∨ (idx ≥ 300 ∧ idx < 400) ∨ (idx ≥ 400 ∧ idx < 500) ∨ (idx ≥ 500 ∧ idx < 600) ∨ (idx ≥ 600 ∧ idx < 700) ∨ (idx ≥ 700 ∧ idx < 800) ∨ (idx ≥ 800 ∧ idx < 900) ∨ (idx ≥ 900 ∧ idx < 1000) ∨ (idx ≥ 1000 ∧ idx < 1100) ∨ (idx ≥ 1100 ∧ idx < 1200) ∨ (idx ≥ 1200 ∧ idx < 1300) ∨ (idx ≥ 1300 ∧ idx < 1400) ∨ (idx ≥ 1400 ∧ idx < 1500) ∨ (idx ≥ 1500 ∧ idx < 1600) ∨ (idx ≥ 1600 ∧ idx < 1700) ∨ (idx ≥ 1700 ∧ idx < 1800) ∨ (idx ≥ 1800 ∧ idx < 1900) ∨ (idx ≥ 1900 ∧ idx < 2000) ∨ (idx ≥ 2000 ∧ idx < 2100) ∨ (idx ≥ 2100 ∧ idx < 2200) ∨ (idx ≥ 2200 ∧ idx < 2300) ∨ (idx ≥ 2300 ∧ idx < 2400) ∨ (idx ≥ 2400 ∧ idx < 2500) ∨ (idx ≥ 2500 ∧ idx < 2600) ∨ (idx ≥ 2600 ∧ idx < 2700) ∨ (idx ≥ 2700 ∧ idx < 2800) ∨ (idx ≥ 2800 ∧ idx < 2900) ∨ (idx ≥ 2900 ∧ idx < 3000) ∨ (idx ≥ 3000 ∧ idx < 3100) ∨ (idx ≥ 3100 ∧ idx < 3200) ∨ (idx ≥ 3200 ∧ idx < 3300) ∨ (idx ≥ 3300 ∧ idx < 3400) ∨ (idx ≥ 3400 ∧ idx < 3500) ∨ (idx ≥ 3500 ∧ idx < 3600) ∨ (idx ≥ 3600 ∧ idx < 3700) ∨ (idx ≥ 3700 ∧ idx < 3800) ∨ (idx ≥ 3800 ∧ idx < 3900) ∨ (idx ≥ 3900 ∧ idx < 4000) ∨ (idx ≥ 4000 ∧ idx < 4100) ∨ (idx ≥ 4100 ∧ idx < 4200) ∨ (idx ≥ 4200 ∧ idx < 4300) ∨ (idx ≥ 4300 ∧ idx < 4400) ∨ (idx ≥ 4400 ∧ idx < 4500) ∨ (idx ≥ 4500 ∧ idx < 4600) ∨ (idx ≥ 4600 ∧ idx < 4700) ∨ (idx ≥ 4700 ∧ idx < 4800) ∨ (idx ≥ 4800 ∧ idx < 4900) ∨ (idx ≥ 4900 ∧ idx < 5000) ∨ (idx ≥ 5000 ∧ idx < 5100) ∨ (idx ≥ 5100 ∧ idx < 5200) ∨ (idx ≥ 5200 ∧ idx < 5300) ∨ (idx ≥ 5300 ∧ idx < 5400) ∨ (idx ≥ 5400 ∧ idx < 5500) ∨ (idx ≥ 5500 ∧ idx < 5600) ∨ (idx ≥ 5600 ∧ idx < 5700) ∨ (idx ≥ 5700 ∧ idx < 5800) ∨ (idx ≥ 5800 ∧ idx < 5900) ∨ (idx ≥ 5900 ∧ idx < 6000) ∨ (idx ≥ 6000 ∧ idx < 6100) ∨ (idx ≥ 6100 ∧ idx < 6200) ∨ (idx ≥ 6200 ∧ idx < 6300) ∨ (idx ≥ 6300 ∧ idx < 6400) ∨ (idx ≥ 6400) := by omega
  rcases h_cases with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 | h21 | h22 | h23 | h24 | h25 | h26 | h27 | h28 | h29 | h30 | h31 | h32 | h33 | h34 | h35 | h36 | h37 | h38 | h39 | h40 | h41 | h42 | h43 | h44 | h45 | h46 | h47 | h48 | h49 | h50 | h51 | h52 | h53 | h54 | h55 | h56 | h57 | h58 | h59 | h60 | h61 | h62 | h63 | h64
  · have h0_lt : idx < 100 := h0.2
    exact is_blocked_chunk_0 idx h0_lt
  · have : idx - 100 < 100 := by omega
    have h_eq : idx = (idx - 100) + 100 := by omega
    rw [h_eq]
    exact is_blocked_chunk_1 (idx - 100) this
  · have : idx - 200 < 100 := by omega
    have h_eq : idx = (idx - 200) + 200 := by omega
    rw [h_eq]
    exact is_blocked_chunk_2 (idx - 200) this
  · have : idx - 300 < 100 := by omega
    have h_eq : idx = (idx - 300) + 300 := by omega
    rw [h_eq]
    exact is_blocked_chunk_3 (idx - 300) this
  · have : idx - 400 < 100 := by omega
    have h_eq : idx = (idx - 400) + 400 := by omega
    rw [h_eq]
    exact is_blocked_chunk_4 (idx - 400) this
  · have : idx - 500 < 100 := by omega
    have h_eq : idx = (idx - 500) + 500 := by omega
    rw [h_eq]
    exact is_blocked_chunk_5 (idx - 500) this
  · have : idx - 600 < 100 := by omega
    have h_eq : idx = (idx - 600) + 600 := by omega
    rw [h_eq]
    exact is_blocked_chunk_6 (idx - 600) this
  · have : idx - 700 < 100 := by omega
    have h_eq : idx = (idx - 700) + 700 := by omega
    rw [h_eq]
    exact is_blocked_chunk_7 (idx - 700) this
  · have : idx - 800 < 100 := by omega
    have h_eq : idx = (idx - 800) + 800 := by omega
    rw [h_eq]
    exact is_blocked_chunk_8 (idx - 800) this
  · have : idx - 900 < 100 := by omega
    have h_eq : idx = (idx - 900) + 900 := by omega
    rw [h_eq]
    exact is_blocked_chunk_9 (idx - 900) this
  · have : idx - 1000 < 100 := by omega
    have h_eq : idx = (idx - 1000) + 1000 := by omega
    rw [h_eq]
    exact is_blocked_chunk_10 (idx - 1000) this
  · have : idx - 1100 < 100 := by omega
    have h_eq : idx = (idx - 1100) + 1100 := by omega
    rw [h_eq]
    exact is_blocked_chunk_11 (idx - 1100) this
  · have : idx - 1200 < 100 := by omega
    have h_eq : idx = (idx - 1200) + 1200 := by omega
    rw [h_eq]
    exact is_blocked_chunk_12 (idx - 1200) this
  · have : idx - 1300 < 100 := by omega
    have h_eq : idx = (idx - 1300) + 1300 := by omega
    rw [h_eq]
    exact is_blocked_chunk_13 (idx - 1300) this
  · have : idx - 1400 < 100 := by omega
    have h_eq : idx = (idx - 1400) + 1400 := by omega
    rw [h_eq]
    exact is_blocked_chunk_14 (idx - 1400) this
  · have : idx - 1500 < 100 := by omega
    have h_eq : idx = (idx - 1500) + 1500 := by omega
    rw [h_eq]
    exact is_blocked_chunk_15 (idx - 1500) this
  · have : idx - 1600 < 100 := by omega
    have h_eq : idx = (idx - 1600) + 1600 := by omega
    rw [h_eq]
    exact is_blocked_chunk_16 (idx - 1600) this
  · have : idx - 1700 < 100 := by omega
    have h_eq : idx = (idx - 1700) + 1700 := by omega
    rw [h_eq]
    exact is_blocked_chunk_17 (idx - 1700) this
  · have : idx - 1800 < 100 := by omega
    have h_eq : idx = (idx - 1800) + 1800 := by omega
    rw [h_eq]
    exact is_blocked_chunk_18 (idx - 1800) this
  · have : idx - 1900 < 100 := by omega
    have h_eq : idx = (idx - 1900) + 1900 := by omega
    rw [h_eq]
    exact is_blocked_chunk_19 (idx - 1900) this
  · have : idx - 2000 < 100 := by omega
    have h_eq : idx = (idx - 2000) + 2000 := by omega
    rw [h_eq]
    exact is_blocked_chunk_20 (idx - 2000) this
  · have : idx - 2100 < 100 := by omega
    have h_eq : idx = (idx - 2100) + 2100 := by omega
    rw [h_eq]
    exact is_blocked_chunk_21 (idx - 2100) this
  · have : idx - 2200 < 100 := by omega
    have h_eq : idx = (idx - 2200) + 2200 := by omega
    rw [h_eq]
    exact is_blocked_chunk_22 (idx - 2200) this
  · have : idx - 2300 < 100 := by omega
    have h_eq : idx = (idx - 2300) + 2300 := by omega
    rw [h_eq]
    exact is_blocked_chunk_23 (idx - 2300) this
  · have : idx - 2400 < 100 := by omega
    have h_eq : idx = (idx - 2400) + 2400 := by omega
    rw [h_eq]
    exact is_blocked_chunk_24 (idx - 2400) this
  · have : idx - 2500 < 100 := by omega
    have h_eq : idx = (idx - 2500) + 2500 := by omega
    rw [h_eq]
    exact is_blocked_chunk_25 (idx - 2500) this
  · have : idx - 2600 < 100 := by omega
    have h_eq : idx = (idx - 2600) + 2600 := by omega
    rw [h_eq]
    exact is_blocked_chunk_26 (idx - 2600) this
  · have : idx - 2700 < 100 := by omega
    have h_eq : idx = (idx - 2700) + 2700 := by omega
    rw [h_eq]
    exact is_blocked_chunk_27 (idx - 2700) this
  · have : idx - 2800 < 100 := by omega
    have h_eq : idx = (idx - 2800) + 2800 := by omega
    rw [h_eq]
    exact is_blocked_chunk_28 (idx - 2800) this
  · have : idx - 2900 < 100 := by omega
    have h_eq : idx = (idx - 2900) + 2900 := by omega
    rw [h_eq]
    exact is_blocked_chunk_29 (idx - 2900) this
  · have : idx - 3000 < 100 := by omega
    have h_eq : idx = (idx - 3000) + 3000 := by omega
    rw [h_eq]
    exact is_blocked_chunk_30 (idx - 3000) this
  · have : idx - 3100 < 100 := by omega
    have h_eq : idx = (idx - 3100) + 3100 := by omega
    rw [h_eq]
    exact is_blocked_chunk_31 (idx - 3100) this
  · have : idx - 3200 < 100 := by omega
    have h_eq : idx = (idx - 3200) + 3200 := by omega
    rw [h_eq]
    exact is_blocked_chunk_32 (idx - 3200) this
  · have : idx - 3300 < 100 := by omega
    have h_eq : idx = (idx - 3300) + 3300 := by omega
    rw [h_eq]
    exact is_blocked_chunk_33 (idx - 3300) this
  · have : idx - 3400 < 100 := by omega
    have h_eq : idx = (idx - 3400) + 3400 := by omega
    rw [h_eq]
    exact is_blocked_chunk_34 (idx - 3400) this
  · have : idx - 3500 < 100 := by omega
    have h_eq : idx = (idx - 3500) + 3500 := by omega
    rw [h_eq]
    exact is_blocked_chunk_35 (idx - 3500) this
  · have : idx - 3600 < 100 := by omega
    have h_eq : idx = (idx - 3600) + 3600 := by omega
    rw [h_eq]
    exact is_blocked_chunk_36 (idx - 3600) this
  · have : idx - 3700 < 100 := by omega
    have h_eq : idx = (idx - 3700) + 3700 := by omega
    rw [h_eq]
    exact is_blocked_chunk_37 (idx - 3700) this
  · have : idx - 3800 < 100 := by omega
    have h_eq : idx = (idx - 3800) + 3800 := by omega
    rw [h_eq]
    exact is_blocked_chunk_38 (idx - 3800) this
  · have : idx - 3900 < 100 := by omega
    have h_eq : idx = (idx - 3900) + 3900 := by omega
    rw [h_eq]
    exact is_blocked_chunk_39 (idx - 3900) this
  · have : idx - 4000 < 100 := by omega
    have h_eq : idx = (idx - 4000) + 4000 := by omega
    rw [h_eq]
    exact is_blocked_chunk_40 (idx - 4000) this
  · have : idx - 4100 < 100 := by omega
    have h_eq : idx = (idx - 4100) + 4100 := by omega
    rw [h_eq]
    exact is_blocked_chunk_41 (idx - 4100) this
  · have : idx - 4200 < 100 := by omega
    have h_eq : idx = (idx - 4200) + 4200 := by omega
    rw [h_eq]
    exact is_blocked_chunk_42 (idx - 4200) this
  · have : idx - 4300 < 100 := by omega
    have h_eq : idx = (idx - 4300) + 4300 := by omega
    rw [h_eq]
    exact is_blocked_chunk_43 (idx - 4300) this
  · have : idx - 4400 < 100 := by omega
    have h_eq : idx = (idx - 4400) + 4400 := by omega
    rw [h_eq]
    exact is_blocked_chunk_44 (idx - 4400) this
  · have : idx - 4500 < 100 := by omega
    have h_eq : idx = (idx - 4500) + 4500 := by omega
    rw [h_eq]
    exact is_blocked_chunk_45 (idx - 4500) this
  · have : idx - 4600 < 100 := by omega
    have h_eq : idx = (idx - 4600) + 4600 := by omega
    rw [h_eq]
    exact is_blocked_chunk_46 (idx - 4600) this
  · have : idx - 4700 < 100 := by omega
    have h_eq : idx = (idx - 4700) + 4700 := by omega
    rw [h_eq]
    exact is_blocked_chunk_47 (idx - 4700) this
  · have : idx - 4800 < 100 := by omega
    have h_eq : idx = (idx - 4800) + 4800 := by omega
    rw [h_eq]
    exact is_blocked_chunk_48 (idx - 4800) this
  · have : idx - 4900 < 100 := by omega
    have h_eq : idx = (idx - 4900) + 4900 := by omega
    rw [h_eq]
    exact is_blocked_chunk_49 (idx - 4900) this
  · have : idx - 5000 < 100 := by omega
    have h_eq : idx = (idx - 5000) + 5000 := by omega
    rw [h_eq]
    exact is_blocked_chunk_50 (idx - 5000) this
  · have : idx - 5100 < 100 := by omega
    have h_eq : idx = (idx - 5100) + 5100 := by omega
    rw [h_eq]
    exact is_blocked_chunk_51 (idx - 5100) this
  · have : idx - 5200 < 100 := by omega
    have h_eq : idx = (idx - 5200) + 5200 := by omega
    rw [h_eq]
    exact is_blocked_chunk_52 (idx - 5200) this
  · have : idx - 5300 < 100 := by omega
    have h_eq : idx = (idx - 5300) + 5300 := by omega
    rw [h_eq]
    exact is_blocked_chunk_53 (idx - 5300) this
  · have : idx - 5400 < 100 := by omega
    have h_eq : idx = (idx - 5400) + 5400 := by omega
    rw [h_eq]
    exact is_blocked_chunk_54 (idx - 5400) this
  · have : idx - 5500 < 100 := by omega
    have h_eq : idx = (idx - 5500) + 5500 := by omega
    rw [h_eq]
    exact is_blocked_chunk_55 (idx - 5500) this
  · have : idx - 5600 < 100 := by omega
    have h_eq : idx = (idx - 5600) + 5600 := by omega
    rw [h_eq]
    exact is_blocked_chunk_56 (idx - 5600) this
  · have : idx - 5700 < 100 := by omega
    have h_eq : idx = (idx - 5700) + 5700 := by omega
    rw [h_eq]
    exact is_blocked_chunk_57 (idx - 5700) this
  · have : idx - 5800 < 100 := by omega
    have h_eq : idx = (idx - 5800) + 5800 := by omega
    rw [h_eq]
    exact is_blocked_chunk_58 (idx - 5800) this
  · have : idx - 5900 < 100 := by omega
    have h_eq : idx = (idx - 5900) + 5900 := by omega
    rw [h_eq]
    exact is_blocked_chunk_59 (idx - 5900) this
  · have : idx - 6000 < 100 := by omega
    have h_eq : idx = (idx - 6000) + 6000 := by omega
    rw [h_eq]
    exact is_blocked_chunk_60 (idx - 6000) this
  · have : idx - 6100 < 100 := by omega
    have h_eq : idx = (idx - 6100) + 6100 := by omega
    rw [h_eq]
    exact is_blocked_chunk_61 (idx - 6100) this
  · have : idx - 6200 < 100 := by omega
    have h_eq : idx = (idx - 6200) + 6200 := by omega
    rw [h_eq]
    exact is_blocked_chunk_62 (idx - 6200) this
  · have : idx - 6300 < 100 := by omega
    have h_eq : idx = (idx - 6300) + 6300 := by omega
    rw [h_eq]
    exact is_blocked_chunk_63 (idx - 6300) this
  · have h_last : idx - 6400 < 100 := by omega
    have h_eq : idx = (idx - 6400) + 6400 := by omega
    rw [h_eq]
    exact is_blocked_chunk_64 (idx - 6400) h_last

lemma h_id_int_lemma (p : (ℕ × ℕ) × ℕ × ℕ) (k u v_pow : ℕ) (h_uv : u + v_pow = 2 * k) (h_eq_class : 36 * (p.1.1^2 + p.1.2^2) = 10 * 2^(2*v_pow) + 16 * 2^(2*k) + 10 * 2^(2*u)) (hu_ge : u ≥ 1) (h_u_le_k : u ≤ k) : 9 * (p.1.1^2 + p.1.2^2) = 4^(u - 1) * (10 * 16^(k - u) + 16 * 4^(k - u) + 10) := by
  let i := u - 1
  let s := k - u
  have h_id_int' : (36 * (p.1.1^2 + p.1.2^2) : ℤ) = (4 * (4^i * (10 * 16^s + 16 * 4^s + 10)) : ℤ) := by
    have h_eq_class_cast : (36 * (p.1.1^2 + p.1.2^2) : ℤ) = (10 * 2^(2*v_pow) + 16 * 2^(2*k) + 10 * 2^(2*u) : ℤ) := by exact_mod_cast h_eq_class
    rw [h_eq_class_cast]
    have h_16 : (16^s : ℤ) = 2^(4 * s) := by
      have : (16^s : ℕ) = 2^(4 * s) := by rw [show 16 = 2^4 by rfl, ← pow_mul]
      exact_mod_cast this
    have h_4s : (4^s : ℤ) = 2^(2 * s) := by
      have : (4^s : ℕ) = 2^(2 * s) := by rw [show 4 = 2^2 by rfl, ← pow_mul]
      exact_mod_cast this
    have h_4i : (4^i : ℤ) = 2^(2 * i) := by
      have : (4^i : ℕ) = 2^(2 * i) := by rw [show 4 = 2^2 by rfl, ← pow_mul]
      exact_mod_cast this
    rw [h_16, h_4s, h_4i]
    have h1 : (2^(2 * v_pow) : ℤ) = 2^(2 * i + 2 + 4 * s) := by
      have : 2 * v_pow = 2 * i + 2 + 4 * s := by omega
      rw [this]
    have h2 : (2^(2 * k) : ℤ) = 2^(2 * i + 2 + 2 * s) := by
      have : 2 * k = 2 * i + 2 + 2 * s := by omega
      rw [this]
    have h3 : (2^(2 * u) : ℤ) = 2^(2 * i + 2) := by
      have : 2 * u = 2 * i + 2 := by omega
      rw [this]
    rw [h1, h2, h3]
    repeat rw [pow_add]
    ring
  have h_id_nat : 36 * (p.1.1^2 + p.1.2^2) = 4 * (4^i * (10 * 16^s + 16 * 4^s + 10)) := by
    exact_mod_cast h_id_int'
  change 9 * (p.1.1^2 + p.1.2^2) = 4^i * (10 * 16^s + 16 * 4^s + 10)
  omega

theorem A301376_conjecture.disproof : ¬ ∀ (n : ℕ), n > 0 → a n > 0 := by
  intro h
  have h_pos : N > 0 := by decide
  have h_a := h N h_pos
  have h_a' : 0 < a N := h_a
  unfold a at h_a'
  dsimp only at h_a'
  rw [Finset.card_pos, Finset.filter_nonempty_iff] at h_a'
  obtain ⟨p, hp⟩ := h_a'
  rcases hp with ⟨h_dom, h_sum, h_zw, k, hk_mem, hk_eq⟩
  obtain ⟨u, v_pow, h_uv, h_le_v, h_eq_class⟩ := classification_step p.1.1 p.1.2 k hk_eq
  have h_cases : u = 0 ∨ u ≥ 1 := by omega
  rcases h_cases with rfl | hu_ge
  · -- Case u = 0
    have h_k_cases : k = 0 ∨ k ≥ 1 := by omega
    rcases h_k_cases with rfl | hk_ge
    · -- Subcase k = 0
      have h_v0 : v_pow = 0 := by omega
      subst h_v0
      have h_sum_class : 36 * (p.1.1^2 + p.1.2^2) = 36 := by
        rw [h_eq_class]
        rfl
      have h_v_one : p.1.1^2 + p.1.2^2 = 1 := by omega
      have h_two_sq : ∃ z w, z^2 + w^2 = N^2 - 1 := by
        use p.2.1, p.2.2
        omega
      have h_blocked : is_blocked_by_idx 6400 = true := is_blocked_all 6400 (by decide)
      unfold is_blocked_by_idx at h_blocked
      dsimp only at h_blocked
      have h_p_prop : (N^2 - 1) % (blocking_prime_by_idx 6400) = 0 ∧ (N^2 - 1) % (blocking_prime_by_idx 6400)^2 ≠ 0 := by decide
      let p' := blocking_prime_by_idx 6400
      have h_prime_fact : Fact (Nat.Prime p') := ⟨blocking_prime_by_idx_prime 6400⟩
      have h_prime_3mod4 : p' % 4 = 3 := blocking_prime_by_idx_3mod4 6400
      have h_dvd : p' ∣ N^2 - 1 := Nat.dvd_of_mod_eq_zero h_p_prop.1
      have h_not_dvd : ¬ p'^2 ∣ N^2 - 1 := by
        intro hd
        have h_mod : (N^2 - 1) % p'^2 = 0 := Nat.mod_eq_zero_of_dvd hd
        exact h_p_prop.2 h_mod
      have h_no_rep := not_sq_add_sq (N^2 - 1) p' h_prime_3mod4 h_dvd h_not_dvd
      exact h_no_rep h_two_sq
    · -- Subcase k >= 1
      have h_v_eq : v_pow = 2 * k := by omega
      rw [h_v_eq] at h_eq_class
      have h_rhs_mod : (10 * 2^(2 * (2 * k)) + 16 * 2^(2 * k) + 10 * 2^(2 * 0)) % 4 = 2 := by
        have h_k_ge : 2 * k ≥ 2 := by omega
        have h_pow1 : 4 ∣ 2^(2 * (2 * k)) := by
          have : 2^(2 * (2 * k)) = 4^(2 * k) := by
            rw [show 2^(2 * (2 * k)) = (2^2)^(2 * k) by rw [← pow_mul, mul_comm]]
            rfl
          rw [this]
          use 4^(2 * k - 1)
          have : 2 * k = (2 * k - 1) + 1 := by omega
          nth_rw 1 [this]
          rw [pow_add]
          ring
        have h_pow2 : 4 ∣ 2^(2 * k) := by
          have : 2^(2 * k) = 4^k := by
            rw [show 2^(2 * k) = (2^2)^k by rw [← pow_mul, mul_comm]]
            rfl
          rw [this]
          use 4^(k - 1)
          have : k = (k - 1) + 1 := by omega
          nth_rw 1 [this]
          rw [pow_add]
          ring
        omega
      have h_lhs_mod : (36 * (p.1.1^2 + p.1.2^2)) % 4 = 0 := by omega
      omega
  · -- Case u >= 1
    let i := u - 1
    let s := k - u
    have h_s_bounds : s < 40 := by
      by_contra hc
      push_neg at hc
      have h_pow16 : 10 * 16^s ≥ 10 * 16^40 := by
        have : 16^s ≥ 16^40 := Nat.pow_le_pow_right (by decide : 16 > 0) (by omega)
        omega
      have h_val_ge : 4^i * (10 * 16^s + 16 * 4^s + 10) / 9 > N^2 := by
        have : 4^i * (10 * 16^s + 16 * 4^s + 10) ≥ 10 * 16^s := by
          have hA : 4^i ≥ 1 := by
            have : 4^i > 0 := by positivity
            omega
          have hB : 10 * 16^s + 16 * 4^s + 10 ≥ 10 * 16^s := by omega
          nlinarith
        calc 4^i * (10 * 16^s + 16 * 4^s + 10) / 9 ≥ 10 * 16^s / 9 := Nat.div_le_div_right this
        _ ≥ 10 * 16^40 / 9 := Nat.div_le_div_right h_pow16
        _ > N^2 := by decide
      have h_v_bound : p.1.1^2 + p.1.2^2 > N^2 := by
        have h_u_le_k : u ≤ k := by omega
        have h_eq_class' : 9 * (p.1.1^2 + p.1.2^2) = 4^i * (10 * 16^s + 16 * 4^s + 10) := h_id_int_lemma p k u v_pow h_uv h_eq_class hu_ge h_u_le_k
        have h_div : p.1.1^2 + p.1.2^2 = 4^i * (10 * 16^s + 16 * 4^s + 10) / 9 := by
          rw [← h_eq_class']
          rw [Nat.mul_div_cancel_left]
          decide
        rw [h_div]
        exact h_val_ge
      omega
    have h_i_bounds : i < 160 := by
      by_contra hc
      push_neg at hc
      have h_pow4 : 4^i ≥ 4^160 := Nat.pow_le_pow_right (by decide : 4 > 0) (by omega)
      have h_val_ge : 4^i * (10 * 16^s + 16 * 4^s + 10) / 9 > N^2 := by
        have : 4^i * (10 * 16^s + 16 * 4^s + 10) ≥ 4^160 * 10 := by
          have hA : 10 * 16^s + 16 * 4^s + 10 ≥ 10 := by omega
          nlinarith
        calc 4^i * (10 * 16^s + 16 * 4^s + 10) / 9 ≥ (4^160 * 10) / 9 := Nat.div_le_div_right this
        _ > N^2 := by decide
      have h_v_bound : p.1.1^2 + p.1.2^2 > N^2 := by
        have h_u_le_k : u ≤ k := by omega
        have h_eq_class' : 9 * (p.1.1^2 + p.1.2^2) = 4^i * (10 * 16^s + 16 * 4^s + 10) := h_id_int_lemma p k u v_pow h_uv h_eq_class hu_ge h_u_le_k
        have h_div : p.1.1^2 + p.1.2^2 = 4^i * (10 * 16^s + 16 * 4^s + 10) / 9 := by
          rw [← h_eq_class']
          rw [Nat.mul_div_cancel_left]
          decide
        rw [h_div]
        exact h_val_ge
      omega
    have h_u_le_k : u ≤ k := by omega
    have h_eq_class' : 9 * (p.1.1^2 + p.1.2^2) = 4^i * (10 * 16^s + 16 * 4^s + 10) := h_id_int_lemma p k u v_pow h_uv h_eq_class hu_ge h_u_le_k
    have h_v_div : p.1.1^2 + p.1.2^2 = 4^i * (10 * 16^s + 16 * 4^s + 10) / 9 := by
      rw [← h_eq_class']
      rw [Nat.mul_div_cancel_left]
      decide
    have h_two_sq : ∃ z w, z^2 + w^2 = N^2 - (p.1.1^2 + p.1.2^2) := by
      use p.2.1, p.2.2
      omega
    let idx := i * 40 + s
    have h_idx_lt : idx < 6401 := by omega
    have h_div_idx : idx / 40 = i := by omega
    have h_mod_idx : idx % 40 = s := by omega
    have h_blocked : is_blocked_by_idx idx = true := is_blocked_all idx h_idx_lt
    unfold is_blocked_by_idx at h_blocked
    have h_not_6400 : idx ≠ 6400 := by omega
    split_ifs at h_blocked
    · contradiction
    · rw [h_div_idx, h_mod_idx, h_v_div] at h_blocked
      let p' := blocking_prime_by_idx idx
      have h_p_prop : (N^2 - (p.1.1^2 + p.1.2^2)) % p' = 0 ∧ (N^2 - (p.1.1^2 + p.1.2^2)) % p'^2 ≠ 0 := by
        rw [Bool.and_eq_true] at h_blocked
        exact ⟨beq_iff_eq.mp h_blocked.1, bne_iff_ne.mp h_blocked.2⟩
      have h_prime_fact : Fact (Nat.Prime p') := ⟨blocking_prime_by_idx_prime idx⟩
      have h_prime_3mod4 : p' % 4 = 3 := blocking_prime_by_idx_3mod4 idx
      have h_dvd : p' ∣ N^2 - (p.1.1^2 + p.1.2^2) := Nat.dvd_of_mod_eq_zero h_p_prop.1
      have h_not_dvd : ¬ p'^2 ∣ N^2 - (p.1.1^2 + p.1.2^2) := by
        intro hd
        have h_mod : (N^2 - (p.1.1^2 + p.1.2^2)) % p'^2 = 0 := Nat.mod_eq_zero_of_dvd hd
        exact h_p_prop.2 h_mod
      have h_no_rep := not_sq_add_sq (N^2 - (p.1.1^2 + p.1.2^2)) p' h_prime_3mod4 h_dvd h_not_dvd
      exact h_no_rep h_two_sq
