import FormalConjectures.Util.ProblemImports
open Nat Finset

/--
A234360: $a(n) = \left|\left\{0 < k < n: (k+1)^{\phi(n-k)} + k \text{ is prime}\right\}\right|$, where $\phi(\cdot)$ is Euler's totient function.
-/
def a (n : ℕ) : ℕ :=
  (filter (fun k => Nat.Prime ((k + 1) ^ (Nat.totient (n - k)) + k)) (Ico 1 n)).card

theorem refute_factor2 (val e : ℕ) (h : 1 < e ∧ e ∣ val ∧ e < val) : ¬ Nat.Prime val := by
  obtain ⟨h1,hd,h2⟩ := h
  exact fun hp => by rcases hp.eq_one_or_self_of_dvd e hd with h | h <;> omega

theorem not_prime_fermat (N r : ℕ) (hN : 1 < N) (hr1 : 1 < r) (hrN : r < N)
    (hdvd : ¬ N ∣ 2)
    (hpow : (2 : ZMod N) ^ (N - 1) = ((r : ℕ) : ZMod N)) : ¬ Nat.Prime N := by
  intro hp
  haveI : Fact (Nat.Prime N) := ⟨hp⟩
  haveI : Fact (1 < N) := ⟨hN⟩
  have h2 : (2 : ZMod N) ≠ 0 := by
    rw [show (2 : ZMod N) = ((2:ℕ) : ZMod N) by push_cast; ring, Ne, ZMod.natCast_eq_zero_iff]
    exact hdvd
  have hf : (2 : ZMod N) ^ (N - 1) = 1 := ZMod.pow_card_sub_one_eq_one h2
  rw [hpow] at hf
  have hval := congrArg ZMod.val hf
  rw [ZMod.val_natCast_of_lt hrN, ZMod.val_one] at hval
  omega

set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
set_option exponentiation.threshold 1000000

theorem refute_e (k e d : ℕ) (he : Nat.totient (1408 - k) / 2 = e)
    (h : 1 < d ∧ d ∣ ((k+1)^e - k) ∧ d < (k+1)^e - k) :
    ¬ Nat.Prime ((k+1)^(Nat.totient (1408 - k)/2) - k) := by
  rw [he]; exact refute_factor2 _ d h

theorem refute_triv (k e : ℕ) (he : Nat.totient (1408 - k) / 2 = e)
    (h : ¬ Nat.Prime ((k+1)^e - k)) : ¬ Nat.Prime ((k+1)^(Nat.totient (1408 - k)/2) - k) := by
  rw [he]; exact h

theorem refute_fermat (k e r : ℕ) (he : Nat.totient (1408 - k) / 2 = e)
    (hN : 1 < (k+1)^e - k) (hr1 : 1 < r) (hrN : r < (k+1)^e - k)
    (hd : ¬ ((k+1)^e - k) ∣ 2)
    (hpow : (2 : ZMod ((k+1)^e - k)) ^ (((k+1)^e - k) - 1) = ((r:ℕ) : ZMod ((k+1)^e - k))) :
    ¬ Nat.Prime ((k+1)^(Nat.totient (1408 - k)/2) - k) := by
  rw [he]; exact not_prime_fermat _ r hN hr1 hrN hd hpow

theorem pk_1 : ¬ Nat.Prime ((1+1)^(Nat.totient (1408-1)/2) - 1) := refute_e 1 396 3 (by decide) (by decide)
theorem pk_2 : ¬ Nat.Prime ((2+1)^(Nat.totient (1408-2)/2) - 2) := refute_e 2 324 31 (by decide) (by decide)
theorem pk_3 : ¬ Nat.Prime ((3+1)^(Nat.totient (1408-3)/2) - 3) := refute_e 3 560 13 (by decide) (by decide)
theorem pk_4 : ¬ Nat.Prime ((4+1)^(Nat.totient (1408-4)/2) - 4) := refute_e 4 216 3 (by decide) (by decide)
theorem pk_5 : ¬ Nat.Prime ((5+1)^(Nat.totient (1408-5)/2) - 5) := refute_e 5 660 8819 (by decide) (by decide)
theorem pk_6 : ¬ Nat.Prime ((6+1)^(Nat.totient (1408-6)/2) - 6) := refute_e 6 350 43 (by decide) (by decide)
theorem pk_7 : ¬ Nat.Prime ((7+1)^(Nat.totient (1408-7)/2) - 7) := refute_e 7 466 3 (by decide) (by decide)
theorem pk_8 : ¬ Nat.Prime ((8+1)^(Nat.totient (1408-8)/2) - 8) := refute_e 8 240 7 (by decide) (by decide)
theorem pk_9 : ¬ Nat.Prime ((9+1)^(Nat.totient (1408-9)/2) - 9) := refute_e 9 699 5867 (by decide) (by decide)
theorem pk_10 : ¬ Nat.Prime ((10+1)^(Nat.totient (1408-10)/2) - 10) := refute_e 10 232 3 (by decide) (by decide)
theorem pk_11 : ¬ Nat.Prime ((11+1)^(Nat.totient (1408-11)/2) - 11) := refute_e 11 630 529181351 (by decide) (by decide)
theorem pk_12 : ¬ Nat.Prime ((12+1)^(Nat.totient (1408-12)/2) - 12) := refute_e 12 348 47 (by decide) (by decide)
theorem pk_13 : ¬ Nat.Prime ((13+1)^(Nat.totient (1408-13)/2) - 13) := refute_e 13 360 3 (by decide) (by decide)
theorem pk_14 : ¬ Nat.Prime ((14+1)^(Nat.totient (1408-14)/2) - 14) := refute_e 14 320 47 (by decide) (by decide)
theorem pk_15 : ¬ Nat.Prime ((15+1)^(Nat.totient (1408-15)/2) - 15) := refute_e 15 594 7 (by decide) (by decide)
theorem pk_16 : ¬ Nat.Prime ((16+1)^(Nat.totient (1408-16)/2) - 16) := refute_e 16 224 3 (by decide) (by decide)
theorem pk_17 : ¬ Nat.Prime ((17+1)^(Nat.totient (1408-17)/2) - 17) := refute_e 17 636 171593370671 (by decide) (by decide)
theorem pk_18 : ¬ Nat.Prime ((18+1)^(Nat.totient (1408-18)/2) - 18) := refute_e 18 276 191 (by decide) (by decide)
theorem pk_19 : ¬ Nat.Prime ((19+1)^(Nat.totient (1408-19)/2) - 19) := refute_e 19 462 3 (by decide) (by decide)
theorem pk_20 : ¬ Nat.Prime ((20+1)^(Nat.totient (1408-20)/2) - 20) := refute_e 20 346 13679 (by decide) (by decide)
theorem pk_21 : ¬ Nat.Prime ((21+1)^(Nat.totient (1408-21)/2) - 21) := refute_e 21 648 5 (by decide) (by decide)
theorem pk_22 : ¬ Nat.Prime ((22+1)^(Nat.totient (1408-22)/2) - 22) := refute_e 22 180 3 (by decide) (by decide)
theorem pk_23 : ¬ Nat.Prime ((23+1)^(Nat.totient (1408-23)/2) - 23) := refute_e 23 552 29 (by decide) (by decide)
theorem pk_24 : ¬ Nat.Prime ((24+1)^(Nat.totient (1408-24)/2) - 24) := refute_e 24 344 601 (by decide) (by decide)
theorem pk_25 : ¬ Nat.Prime ((25+1)^(Nat.totient (1408-25)/2) - 25) := refute_e 25 460 3 (by decide) (by decide)
theorem pk_26 : ¬ Nat.Prime ((26+1)^(Nat.totient (1408-26)/2) - 26) := refute_e 26 345 23 (by decide) (by decide)
theorem pk_27 : ¬ Nat.Prime ((27+1)^(Nat.totient (1408-27)/2) - 27) := refute_e 27 690 347 (by decide) (by decide)
theorem pk_28 : ¬ Nat.Prime ((28+1)^(Nat.totient (1408-28)/2) - 28) := refute_e 28 176 3 (by decide) (by decide)
theorem pk_29 : ¬ Nat.Prime ((29+1)^(Nat.totient (1408-29)/2) - 29) := refute_e 29 588 7 (by decide) (by decide)
theorem pk_30 : ¬ Nat.Prime ((30+1)^(Nat.totient (1408-30)/2) - 30) := refute_e 30 312 384922215790533167442915360518992430557291454768924689897653366262802472285458751271333307156140784736589857320100419545760578062194110434196211366278928343974765209626362839649602423114974900302040423719305968795660642544572464702172474426662600274363069486813075379735417987145639209054958927992845601662608834375607192579847209908615510835224531083057587639652945305368854772870756607817950357924013480509468741634074954924675833 (by decide) (by decide)
theorem pk_31 : ¬ Nat.Prime ((31+1)^(Nat.totient (1408-31)/2) - 31) := refute_e 31 432 3 (by decide) (by decide)
theorem pk_32 : ¬ Nat.Prime ((32+1)^(Nat.totient (1408-32)/2) - 32) := refute_e 32 336 881 (by decide) (by decide)
theorem pk_33 : ¬ Nat.Prime ((33+1)^(Nat.totient (1408-33)/2) - 33) := refute_e 33 500 97 (by decide) (by decide)
theorem pk_34 : ¬ Nat.Prime ((34+1)^(Nat.totient (1408-34)/2) - 34) := refute_e 34 228 3 (by decide) (by decide)
theorem pk_35 : ¬ Nat.Prime ((35+1)^(Nat.totient (1408-35)/2) - 35) := refute_e 35 686 13 (by decide) (by decide)
theorem pk_36 : ¬ Nat.Prime ((36+1)^(Nat.totient (1408-36)/2) - 36) := refute_e 36 294 7 (by decide) (by decide)
theorem pk_37 : ¬ Nat.Prime ((37+1)^(Nat.totient (1408-37)/2) - 37) := refute_e 37 456 3 (by decide) (by decide)
theorem pk_38 : ¬ Nat.Prime ((38+1)^(Nat.totient (1408-38)/2) - 38) := refute_e 38 272 1483 (by decide) (by decide)
theorem pk_39 : ¬ Nat.Prime ((39+1)^(Nat.totient (1408-39)/2) - 39) := refute_e 39 666 19 (by decide) (by decide)
theorem pk_40 : ¬ Nat.Prime ((40+1)^(Nat.totient (1408-40)/2) - 40) := refute_e 40 216 3 (by decide) (by decide)
theorem pk_41 : ¬ Nat.Prime ((41+1)^(Nat.totient (1408-41)/2) - 41) := refute_e 41 683 794311889339 (by decide) (by decide)
theorem pk_42 : ¬ Nat.Prime ((42+1)^(Nat.totient (1408-42)/2) - 42) := refute_e 42 341 17 (by decide) (by decide)
theorem pk_43 : ¬ Nat.Prime ((43+1)^(Nat.totient (1408-43)/2) - 43) := refute_e 43 288 3 (by decide) (by decide)
theorem pk_44 : ¬ Nat.Prime ((44+1)^(Nat.totient (1408-44)/2) - 44) := refute_e 44 300 269 (by decide) (by decide)
theorem pk_45 : ¬ Nat.Prime ((45+1)^(Nat.totient (1408-45)/2) - 45) := refute_e 45 644 19 (by decide) (by decide)
theorem pk_46 : ¬ Nat.Prime ((46+1)^(Nat.totient (1408-46)/2) - 46) := refute_e 46 226 3 (by decide) (by decide)
theorem pk_47 : ¬ Nat.Prime ((47+1)^(Nat.totient (1408-47)/2) - 47) := refute_e 47 680 37 (by decide) (by decide)
theorem pk_48 : ¬ Nat.Prime ((48+1)^(Nat.totient (1408-48)/2) - 48) := refute_e 48 256 107 (by decide) (by decide)
theorem pk_49 : ¬ Nat.Prime ((49+1)^(Nat.totient (1408-49)/2) - 49) := refute_e 49 450 3 (by decide) (by decide)
theorem pk_50 : ¬ Nat.Prime ((50+1)^(Nat.totient (1408-50)/2) - 50) := refute_e 50 288 7 (by decide) (by decide)
theorem pk_51 : ¬ Nat.Prime ((51+1)^(Nat.totient (1408-51)/2) - 51) := refute_e 51 638 7 (by decide) (by decide)
theorem pk_52 : ¬ Nat.Prime ((52+1)^(Nat.totient (1408-52)/2) - 52) := refute_e 52 224 3 (by decide) (by decide)
theorem pk_53 : ¬ Nat.Prime ((53+1)^(Nat.totient (1408-53)/2) - 53) := refute_e 53 540 13 (by decide) (by decide)
theorem pk_54 : ¬ Nat.Prime ((54+1)^(Nat.totient (1408-54)/2) - 54) := refute_e 54 338 2971 (by decide) (by decide)
theorem pk_55 : ¬ Nat.Prime ((55+1)^(Nat.totient (1408-55)/2) - 55) := refute_e 55 400 3 (by decide) (by decide)
theorem pk_56 : ¬ Nat.Prime ((56+1)^(Nat.totient (1408-56)/2) - 56) := refute_e 56 312 5 (by decide) (by decide)
theorem pk_57 : ¬ Nat.Prime ((57+1)^(Nat.totient (1408-57)/2) - 57) := refute_e 57 576 7 (by decide) (by decide)
theorem pk_58 : ¬ Nat.Prime ((58+1)^(Nat.totient (1408-58)/2) - 58) := refute_e 58 180 3 (by decide) (by decide)
theorem pk_59 : ¬ Nat.Prime ((59+1)^(Nat.totient (1408-59)/2) - 59) := refute_e 59 630 67 (by decide) (by decide)
theorem pk_60 : ¬ Nat.Prime ((60+1)^(Nat.totient (1408-60)/2) - 60) := refute_e 60 336 11 (by decide) (by decide)
theorem pk_61 : ¬ Nat.Prime ((61+1)^(Nat.totient (1408-61)/2) - 61) := refute_e 61 448 3 (by decide) (by decide)
theorem pk_62 : ¬ Nat.Prime ((62+1)^(Nat.totient (1408-62)/2) - 62) := refute_e 62 336 199 (by decide) (by decide)
theorem pk_63 : ¬ Nat.Prime ((63+1)^(Nat.totient (1408-63)/2) - 63) := refute_e 63 536 37 (by decide) (by decide)
theorem pk_64 : ¬ Nat.Prime ((64+1)^(Nat.totient (1408-64)/2) - 64) := refute_e 64 192 3 (by decide) (by decide)
theorem pk_65 : ¬ Nat.Prime ((65+1)^(Nat.totient (1408-65)/2) - 65) := refute_e 65 624 164357 (by decide) (by decide)
theorem pk_66 : ¬ Nat.Prime ((66+1)^(Nat.totient (1408-66)/2) - 66) := refute_e 66 300 5 (by decide) (by decide)
theorem pk_67 : ¬ Nat.Prime ((67+1)^(Nat.totient (1408-67)/2) - 67) := refute_e 67 444 3 (by decide) (by decide)
theorem pk_68 : ¬ Nat.Prime ((68+1)^(Nat.totient (1408-68)/2) - 68) := refute_e 68 264 67 (by decide) (by decide)
theorem pk_69 : ¬ Nat.Prime ((69+1)^(Nat.totient (1408-69)/2) - 69) := refute_e 69 612 743 (by decide) (by decide)
theorem pk_70 : ¬ Nat.Prime ((70+1)^(Nat.totient (1408-70)/2) - 70) := refute_e 70 222 3 (by decide) (by decide)
theorem pk_71 : ¬ Nat.Prime ((71+1)^(Nat.totient (1408-71)/2) - 71) := refute_e 71 570 7 (by decide) (by decide)
theorem pk_72 : ¬ Nat.Prime ((72+1)^(Nat.totient (1408-72)/2) - 72) := refute_e 72 332 7 (by decide) (by decide)
theorem pk_73 : ¬ Nat.Prime ((73+1)^(Nat.totient (1408-73)/2) - 73) := refute_e 73 352 3 (by decide) (by decide)
theorem pk_74 : ¬ Nat.Prime ((74+1)^(Nat.totient (1408-74)/2) - 74) := refute_e 74 308 7 (by decide) (by decide)
theorem pk_75 : ¬ Nat.Prime ((75+1)^(Nat.totient (1408-75)/2) - 75) := refute_e 75 630 660719 (by decide) (by decide)
theorem pk_76 : ¬ Nat.Prime ((76+1)^(Nat.totient (1408-76)/2) - 76) := refute_e 76 216 3 (by decide) (by decide)
theorem pk_77 : ¬ Nat.Prime ((77+1)^(Nat.totient (1408-77)/2) - 77) := refute_e 77 605 61357 (by decide) (by decide)
theorem pk_78 : ¬ Nat.Prime ((78+1)^(Nat.totient (1408-78)/2) - 78) := refute_e 78 216 7 (by decide) (by decide)
theorem pk_79 : ¬ Nat.Prime ((79+1)^(Nat.totient (1408-79)/2) - 79) := refute_e 79 442 3 (by decide) (by decide)
theorem pk_80 : ¬ Nat.Prime ((80+1)^(Nat.totient (1408-80)/2) - 80) := refute_e 80 328 101 (by decide) (by decide)
theorem pk_81 : ¬ Nat.Prime ((81+1)^(Nat.totient (1408-81)/2) - 81) := refute_e 81 663 11 (by decide) (by decide)
theorem pk_82 : ¬ Nat.Prime ((82+1)^(Nat.totient (1408-82)/2) - 82) := refute_e 82 192 3 (by decide) (by decide)
theorem pk_83 : ¬ Nat.Prime ((83+1)^(Nat.totient (1408-83)/2) - 83) := refute_e 83 520 41 (by decide) (by decide)
theorem pk_84 : ¬ Nat.Prime ((84+1)^(Nat.totient (1408-84)/2) - 84) := refute_fermat 84 330 3932055639753323355671058877877921197494848472601092735999170940757673330699711082307745545791403089499258643365073684779473655008168992507715828908508666984312991800881692031545346231163450247486537260148958206524423016670099538688432039948129062337164016329353138184828090077216640855205809373890737804803368281854062334497806605877398872752840441537462753303897598241394068724728275087318104422286086406713592882122718236947866787416847778500490896068699837574734370056696094141219125149795527281891247814877822745162862722039552907266994780828476195913977719542410088448652874073758653984585602355537488241849392278169434114548698878 (by decide) (by norm_num) (by norm_num) (by norm_num) (by decide) (by reduce_mod_char)
theorem pk_85 : ¬ Nat.Prime ((85+1)^(Nat.totient (1408-85)/2) - 85) := refute_e 85 378 3 (by decide) (by decide)
theorem pk_86 : ¬ Nat.Prime ((86+1)^(Nat.totient (1408-86)/2) - 86) := refute_e 86 330 8719 (by decide) (by decide)
theorem pk_87 : ¬ Nat.Prime ((87+1)^(Nat.totient (1408-87)/2) - 87) := refute_e 87 660 101 (by decide) (by decide)
theorem pk_88 : ¬ Nat.Prime ((88+1)^(Nat.totient (1408-88)/2) - 88) := refute_e 88 160 3 (by decide) (by decide)
theorem pk_89 : ¬ Nat.Prime ((89+1)^(Nat.totient (1408-89)/2) - 89) := refute_e 89 659 19 (by decide) (by decide)
theorem pk_90 : ¬ Nat.Prime ((90+1)^(Nat.totient (1408-90)/2) - 90) := refute_e 90 329 313 (by decide) (by decide)
theorem pk_91 : ¬ Nat.Prime ((91+1)^(Nat.totient (1408-91)/2) - 91) := refute_e 91 438 3 (by decide) (by decide)
theorem pk_92 : ¬ Nat.Prime ((92+1)^(Nat.totient (1408-92)/2) - 92) := refute_e 92 276 7 (by decide) (by decide)
theorem pk_93 : ¬ Nat.Prime ((93+1)^(Nat.totient (1408-93)/2) - 93) := refute_e 93 524 7 (by decide) (by decide)
theorem pk_94 : ¬ Nat.Prime ((94+1)^(Nat.totient (1408-94)/2) - 94) := refute_e 94 216 3 (by decide) (by decide)
theorem pk_95 : ¬ Nat.Prime ((95+1)^(Nat.totient (1408-95)/2) - 95) := refute_e 95 600 87520021 (by decide) (by decide)
theorem pk_96 : ¬ Nat.Prime ((96+1)^(Nat.totient (1408-96)/2) - 96) := refute_e 96 320 5 (by decide) (by decide)
theorem pk_97 : ¬ Nat.Prime ((97+1)^(Nat.totient (1408-97)/2) - 97) := refute_e 97 396 3 (by decide) (by decide)
theorem pk_98 : ¬ Nat.Prime ((98+1)^(Nat.totient (1408-98)/2) - 98) := refute_e 98 260 17 (by decide) (by decide)
theorem pk_99 : ¬ Nat.Prime ((99+1)^(Nat.totient (1408-99)/2) - 99) := refute_e 99 480 7 (by decide) (by decide)
theorem pk_100 : ¬ Nat.Prime ((100+1)^(Nat.totient (1408-100)/2) - 100) := refute_e 100 216 3 (by decide) (by decide)
theorem pk_101 : ¬ Nat.Prime ((101+1)^(Nat.totient (1408-101)/2) - 101) := refute_e 101 653 1129 (by decide) (by decide)
theorem pk_102 : ¬ Nat.Prime ((102+1)^(Nat.totient (1408-102)/2) - 102) := refute_e 102 326 7 (by decide) (by decide)
theorem pk_103 : ¬ Nat.Prime ((103+1)^(Nat.totient (1408-103)/2) - 103) := refute_e 103 336 3 (by decide) (by decide)
theorem pk_104 : ¬ Nat.Prime ((104+1)^(Nat.totient (1408-104)/2) - 104) := refute_e 104 324 9161 (by decide) (by decide)
theorem pk_105 : ¬ Nat.Prime ((105+1)^(Nat.totient (1408-105)/2) - 105) := refute_e 105 651 3307 (by decide) (by decide)
theorem pk_106 : ¬ Nat.Prime ((106+1)^(Nat.totient (1408-106)/2) - 106) := refute_e 106 180 3 (by decide) (by decide)
theorem pk_107 : ¬ Nat.Prime ((107+1)^(Nat.totient (1408-107)/2) - 107) := refute_e 107 650 7 (by decide) (by decide)
theorem pk_108 : ¬ Nat.Prime ((108+1)^(Nat.totient (1408-108)/2) - 108) := refute_e 108 240 23 (by decide) (by decide)
theorem pk_109 : ¬ Nat.Prime ((109+1)^(Nat.totient (1408-109)/2) - 109) := refute_e 109 432 3 (by decide) (by decide)
theorem pk_110 : ¬ Nat.Prime ((110+1)^(Nat.totient (1408-110)/2) - 110) := refute_e 110 290 487 (by decide) (by decide)
theorem pk_111 : ¬ Nat.Prime ((111+1)^(Nat.totient (1408-111)/2) - 111) := refute_e 111 648 5 (by decide) (by decide)
theorem pk_112 : ¬ Nat.Prime ((112+1)^(Nat.totient (1408-112)/2) - 112) := refute_e 112 216 3 (by decide) (by decide)
theorem pk_113 : ¬ Nat.Prime ((113+1)^(Nat.totient (1408-113)/2) - 113) := refute_e 113 432 7 (by decide) (by decide)
theorem pk_114 : ¬ Nat.Prime ((114+1)^(Nat.totient (1408-114)/2) - 114) := refute_e 114 323 11 (by decide) (by decide)
theorem pk_115 : ¬ Nat.Prime ((115+1)^(Nat.totient (1408-115)/2) - 115) := refute_e 115 430 3 (by decide) (by decide)
theorem pk_116 : ¬ Nat.Prime ((116+1)^(Nat.totient (1408-116)/2) - 116) := refute_e 116 288 5 (by decide) (by decide)
theorem pk_117 : ¬ Nat.Prime ((117+1)^(Nat.totient (1408-117)/2) - 117) := refute_e 117 645 23 (by decide) (by decide)
theorem pk_118 : ¬ Nat.Prime ((118+1)^(Nat.totient (1408-118)/2) - 118) := refute_e 118 168 3 (by decide) (by decide)
theorem pk_119 : ¬ Nat.Prime ((119+1)^(Nat.totient (1408-119)/2) - 119) := refute_e 119 644 19 (by decide) (by decide)
theorem pk_120 : ¬ Nat.Prime ((120+1)^(Nat.totient (1408-120)/2) - 120) := refute_e 120 264 7 (by decide) (by decide)
theorem pk_121 : ¬ Nat.Prime ((121+1)^(Nat.totient (1408-121)/2) - 121) := refute_e 121 360 3 (by decide) (by decide)
theorem pk_122 : ¬ Nat.Prime ((122+1)^(Nat.totient (1408-122)/2) - 122) := refute_e 122 321 13 (by decide) (by decide)
theorem pk_123 : ¬ Nat.Prime ((123+1)^(Nat.totient (1408-123)/2) - 123) := refute_e 123 512 7 (by decide) (by decide)
theorem pk_124 : ¬ Nat.Prime ((124+1)^(Nat.totient (1408-124)/2) - 124) := refute_e 124 212 3 (by decide) (by decide)
theorem pk_125 : ¬ Nat.Prime ((125+1)^(Nat.totient (1408-125)/2) - 125) := refute_fermat 125 641 125818351584776255877142912383664852461718705743465761856346472038463350124922675163284493694814447943970505792701385936357659876861004032325060024942239578902371785338961777362764544819936588422854275857088710608210834763115317937064884558269725728529345020500227919955624295487764022660844889977139267713124860097252192896363015920332057741256292676654528376508064278279486532136252657913673115159240614977422387357193610657174053066834929142544286484893557112962948599380228345415087315521664873468851083621829284131161798268112967707056468852236938392586000098096250599429189580294780765074083992390847809442987049464771189277451292022189774514886928567842416033449574168027505478264200669972829293178232554201562367631703527003645611410211759494630404411717252024519589839469018273837938377224078636278908005967410065870438898711548355639672512219112507460837767607955152711797995976161271738499810466599739035806615537323136330534831700403236356225309392221933322591012039205653273475863833797601113426047496342134758210816668589791237656166238955283317691376438891886645028948419563269195609609003586312842188557048632402868929447884633070441566564386159671958947406010329741362202053663701650416411640627058430041661976936654626529651008184242852193496963755594032574835572253201413461890754678474802587949171418659958934557744793610539841 (by decide) (by norm_num) (by norm_num) (by norm_num) (by decide) (by reduce_mod_char)
theorem pk_126 : ¬ Nat.Prime ((126+1)^(Nat.totient (1408-126)/2) - 126) := refute_e 126 320 5 (by decide) (by decide)
theorem pk_127 : ¬ Nat.Prime ((127+1)^(Nat.totient (1408-127)/2) - 127) := refute_e 127 360 3 (by decide) (by decide)
theorem pk_128 : ¬ Nat.Prime ((128+1)^(Nat.totient (1408-128)/2) - 128) := refute_e 128 256 89 (by decide) (by decide)
theorem pk_129 : ¬ Nat.Prime ((129+1)^(Nat.totient (1408-129)/2) - 129) := refute_e 129 639 41 (by decide) (by decide)
theorem pk_130 : ¬ Nat.Prime ((130+1)^(Nat.totient (1408-130)/2) - 130) := refute_e 130 210 3 (by decide) (by decide)
theorem pk_131 : ¬ Nat.Prime ((131+1)^(Nat.totient (1408-131)/2) - 131) := refute_e 131 638 17293 (by decide) (by decide)
theorem pk_132 : ¬ Nat.Prime ((132+1)^(Nat.totient (1408-132)/2) - 132) := refute_e 132 280 4987 (by decide) (by decide)
theorem pk_133 : ¬ Nat.Prime ((133+1)^(Nat.totient (1408-133)/2) - 133) := refute_e 133 320 3 (by decide) (by decide)
theorem pk_134 : ¬ Nat.Prime ((134+1)^(Nat.totient (1408-134)/2) - 134) := refute_e 134 252 7 (by decide) (by decide)
theorem pk_135 : ¬ Nat.Prime ((135+1)^(Nat.totient (1408-135)/2) - 135) := refute_e 135 594 11 (by decide) (by decide)
theorem pk_136 : ¬ Nat.Prime ((136+1)^(Nat.totient (1408-136)/2) - 136) := refute_e 136 208 3 (by decide) (by decide)
theorem pk_137 : ¬ Nat.Prime ((137+1)^(Nat.totient (1408-137)/2) - 137) := refute_e 137 600 17 (by decide) (by decide)
theorem pk_138 : ¬ Nat.Prime ((138+1)^(Nat.totient (1408-138)/2) - 138) := refute_e 138 252 941981 (by decide) (by decide)
theorem pk_139 : ¬ Nat.Prime ((139+1)^(Nat.totient (1408-139)/2) - 139) := refute_e 139 414 3 (by decide) (by decide)
theorem pk_140 : ¬ Nat.Prime ((140+1)^(Nat.totient (1408-140)/2) - 140) := refute_e 140 316 17 (by decide) (by decide)
theorem pk_141 : ¬ Nat.Prime ((141+1)^(Nat.totient (1408-141)/2) - 141) := refute_e 141 540 5 (by decide) (by decide)
theorem pk_142 : ¬ Nat.Prime ((142+1)^(Nat.totient (1408-142)/2) - 142) := refute_e 142 210 3 (by decide) (by decide)
theorem pk_143 : ¬ Nat.Prime ((143+1)^(Nat.totient (1408-143)/2) - 143) := refute_e 143 440 547 (by decide) (by decide)
theorem pk_144 : ¬ Nat.Prime ((144+1)^(Nat.totient (1408-144)/2) - 144) := refute_e 144 312 13 (by decide) (by decide)
theorem pk_145 : ¬ Nat.Prime ((145+1)^(Nat.totient (1408-145)/2) - 145) := refute_e 145 420 3 (by decide) (by decide)
theorem pk_146 : ¬ Nat.Prime ((146+1)^(Nat.totient (1408-146)/2) - 146) := refute_e 146 315 249971305257836411 (by decide) (by decide)
theorem pk_147 : ¬ Nat.Prime ((147+1)^(Nat.totient (1408-147)/2) - 147) := refute_e 147 576 73 (by decide) (by decide)
theorem pk_148 : ¬ Nat.Prime ((148+1)^(Nat.totient (1408-148)/2) - 148) := refute_e 148 144 3 (by decide) (by decide)
theorem pk_149 : ¬ Nat.Prime ((149+1)^(Nat.totient (1408-149)/2) - 149) := refute_e 149 629 83 (by decide) (by decide)
theorem pk_150 : ¬ Nat.Prime ((150+1)^(Nat.totient (1408-150)/2) - 150) := refute_e 150 288 43 (by decide) (by decide)
theorem pk_151 : ¬ Nat.Prime ((151+1)^(Nat.totient (1408-151)/2) - 151) := refute_e 151 418 3 (by decide) (by decide)
theorem pk_152 : ¬ Nat.Prime ((152+1)^(Nat.totient (1408-152)/2) - 152) := refute_e 152 312 29 (by decide) (by decide)
theorem pk_153 : ¬ Nat.Prime ((153+1)^(Nat.totient (1408-153)/2) - 153) := refute_e 153 500 23563 (by decide) (by decide)
theorem pk_154 : ¬ Nat.Prime ((154+1)^(Nat.totient (1408-154)/2) - 154) := refute_e 154 180 3 (by decide) (by decide)
theorem pk_155 : ¬ Nat.Prime ((155+1)^(Nat.totient (1408-155)/2) - 155) := refute_e 155 534 7 (by decide) (by decide)
theorem pk_156 : ¬ Nat.Prime ((156+1)^(Nat.totient (1408-156)/2) - 156) := refute_e 156 312 5 (by decide) (by decide)
theorem pk_157 : ¬ Nat.Prime ((157+1)^(Nat.totient (1408-157)/2) - 157) := refute_e 157 414 3 (by decide) (by decide)
theorem pk_158 : ¬ Nat.Prime ((158+1)^(Nat.totient (1408-158)/2) - 158) := refute_e 158 250 67 (by decide) (by decide)
theorem pk_159 : ¬ Nat.Prime ((159+1)^(Nat.totient (1408-159)/2) - 159) := refute_e 159 624 79 (by decide) (by decide)
theorem pk_160 : ¬ Nat.Prime ((160+1)^(Nat.totient (1408-160)/2) - 160) := refute_e 160 192 3 (by decide) (by decide)
theorem pk_161 : ¬ Nat.Prime ((161+1)^(Nat.totient (1408-161)/2) - 161) := refute_e 161 588 5 (by decide) (by decide)
theorem pk_162 : ¬ Nat.Prime ((162+1)^(Nat.totient (1408-162)/2) - 162) := refute_e 162 264 7 (by decide) (by decide)
theorem pk_163 : ¬ Nat.Prime ((163+1)^(Nat.totient (1408-163)/2) - 163) := refute_e 163 328 3 (by decide) (by decide)
theorem pk_164 : ¬ Nat.Prime ((164+1)^(Nat.totient (1408-164)/2) - 164) := refute_e 164 310 546546697 (by decide) (by decide)
theorem pk_165 : ¬ Nat.Prime ((165+1)^(Nat.totient (1408-165)/2) - 165) := refute_e 165 560 7 (by decide) (by decide)
theorem pk_166 : ¬ Nat.Prime ((166+1)^(Nat.totient (1408-166)/2) - 166) := refute_e 166 198 3 (by decide) (by decide)
theorem pk_167 : ¬ Nat.Prime ((167+1)^(Nat.totient (1408-167)/2) - 167) := refute_e 167 576 397 (by decide) (by decide)
theorem pk_168 : ¬ Nat.Prime ((168+1)^(Nat.totient (1408-168)/2) - 168) := refute_e 168 240 782711 (by decide) (by decide)
theorem pk_169 : ¬ Nat.Prime ((169+1)^(Nat.totient (1408-169)/2) - 169) := refute_e 169 348 3 (by decide) (by decide)
theorem pk_170 : ¬ Nat.Prime ((170+1)^(Nat.totient (1408-170)/2) - 170) := refute_e 170 309 20803827362834972369 (by decide) (by decide)
theorem pk_171 : ¬ Nat.Prime ((171+1)^(Nat.totient (1408-171)/2) - 171) := refute_e 171 618 31 (by decide) (by decide)
theorem pk_172 : ¬ Nat.Prime ((172+1)^(Nat.totient (1408-172)/2) - 172) := refute_e 172 204 3 (by decide) (by decide)
theorem pk_173 : ¬ Nat.Prime ((173+1)^(Nat.totient (1408-173)/2) - 173) := refute_e 173 432 23 (by decide) (by decide)
theorem pk_174 : ¬ Nat.Prime ((174+1)^(Nat.totient (1408-174)/2) - 174) := refute_e 174 308 31 (by decide) (by decide)
theorem pk_175 : ¬ Nat.Prime ((175+1)^(Nat.totient (1408-175)/2) - 175) := refute_e 175 408 3 (by decide) (by decide)
theorem pk_176 : ¬ Nat.Prime ((176+1)^(Nat.totient (1408-176)/2) - 176) := refute_e 176 240 5 (by decide) (by decide)
theorem pk_177 : ¬ Nat.Prime ((177+1)^(Nat.totient (1408-177)/2) - 177) := refute_e 177 615 5 (by decide) (by decide)
theorem pk_178 : ¬ Nat.Prime ((178+1)^(Nat.totient (1408-178)/2) - 178) := refute_e 178 160 3 (by decide) (by decide)
theorem pk_179 : ¬ Nat.Prime ((179+1)^(Nat.totient (1408-179)/2) - 179) := refute_e 179 614 7 (by decide) (by decide)
theorem pk_180 : ¬ Nat.Prime ((180+1)^(Nat.totient (1408-180)/2) - 180) := refute_e 180 306 2381 (by decide) (by decide)
theorem pk_181 : ¬ Nat.Prime ((181+1)^(Nat.totient (1408-181)/2) - 181) := refute_e 181 408 3 (by decide) (by decide)
theorem pk_182 : ¬ Nat.Prime ((182+1)^(Nat.totient (1408-182)/2) - 182) := refute_e 182 306 101 (by decide) (by decide)
theorem pk_183 : ¬ Nat.Prime ((183+1)^(Nat.totient (1408-183)/2) - 183) := refute_e 183 420 7 (by decide) (by decide)
theorem pk_184 : ¬ Nat.Prime ((184+1)^(Nat.totient (1408-184)/2) - 184) := refute_e 184 192 3 (by decide) (by decide)
theorem pk_185 : ¬ Nat.Prime ((185+1)^(Nat.totient (1408-185)/2) - 185) := refute_e 185 611 19 (by decide) (by decide)
theorem pk_186 : ¬ Nat.Prime ((186+1)^(Nat.totient (1408-186)/2) - 186) := refute_e 186 276 5 (by decide) (by decide)
theorem pk_187 : ¬ Nat.Prime ((187+1)^(Nat.totient (1408-187)/2) - 187) := refute_e 187 360 3 (by decide) (by decide)
theorem pk_188 : ¬ Nat.Prime ((188+1)^(Nat.totient (1408-188)/2) - 188) := refute_e 188 240 11 (by decide) (by decide)
theorem pk_189 : ¬ Nat.Prime ((189+1)^(Nat.totient (1408-189)/2) - 189) := refute_e 189 572 41 (by decide) (by decide)
theorem pk_190 : ¬ Nat.Prime ((190+1)^(Nat.totient (1408-190)/2) - 190) := refute_e 190 168 3 (by decide) (by decide)
theorem pk_191 : ¬ Nat.Prime ((191+1)^(Nat.totient (1408-191)/2) - 191) := refute_e 191 608 5 (by decide) (by decide)
theorem pk_192 : ¬ Nat.Prime ((192+1)^(Nat.totient (1408-192)/2) - 192) := refute_e 192 288 1470913 (by decide) (by decide)
theorem pk_193 : ¬ Nat.Prime ((193+1)^(Nat.totient (1408-193)/2) - 193) := refute_e 193 324 3 (by decide) (by decide)
theorem pk_194 : ¬ Nat.Prime ((194+1)^(Nat.totient (1408-194)/2) - 194) := refute_e 194 303 4363 (by decide) (by decide)
theorem pk_195 : ¬ Nat.Prime ((195+1)^(Nat.totient (1408-195)/2) - 195) := refute_e 195 606 587 (by decide) (by decide)
theorem pk_196 : ¬ Nat.Prime ((196+1)^(Nat.totient (1408-196)/2) - 196) := refute_e 196 200 3 (by decide) (by decide)
theorem pk_197 : ¬ Nat.Prime ((197+1)^(Nat.totient (1408-197)/2) - 197) := refute_e 197 516 7 (by decide) (by decide)
theorem pk_198 : ¬ Nat.Prime ((198+1)^(Nat.totient (1408-198)/2) - 198) := refute_e 198 220 449 (by decide) (by decide)
theorem pk_199 : ¬ Nat.Prime ((199+1)^(Nat.totient (1408-199)/2) - 199) := refute_e 199 360 3 (by decide) (by decide)
theorem pk_200 : ¬ Nat.Prime ((200+1)^(Nat.totient (1408-200)/2) - 200) := refute_e 200 300 242021371665673 (by decide) (by decide)
theorem pk_201 : ¬ Nat.Prime ((201+1)^(Nat.totient (1408-201)/2) - 201) := refute_e 201 560 5 (by decide) (by decide)
theorem pk_202 : ¬ Nat.Prime ((202+1)^(Nat.totient (1408-202)/2) - 202) := refute_e 202 198 3 (by decide) (by decide)
theorem pk_203 : ¬ Nat.Prime ((203+1)^(Nat.totient (1408-203)/2) - 203) := refute_e 203 480 99689 (by decide) (by decide)
theorem pk_204 : ¬ Nat.Prime ((204+1)^(Nat.totient (1408-204)/2) - 204) := refute_e 204 252 7 (by decide) (by decide)
theorem pk_205 : ¬ Nat.Prime ((205+1)^(Nat.totient (1408-205)/2) - 205) := refute_e 205 400 3 (by decide) (by decide)
theorem pk_206 : ¬ Nat.Prime ((206+1)^(Nat.totient (1408-206)/2) - 206) := refute_e 206 300 5 (by decide) (by decide)
theorem pk_207 : ¬ Nat.Prime ((207+1)^(Nat.totient (1408-207)/2) - 207) := refute_e 207 600 1063 (by decide) (by decide)
theorem pk_208 : ¬ Nat.Prime ((208+1)^(Nat.totient (1408-208)/2) - 208) := refute_e 208 160 3 (by decide) (by decide)
theorem pk_209 : ¬ Nat.Prime ((209+1)^(Nat.totient (1408-209)/2) - 209) := refute_e 209 540 13 (by decide) (by decide)
theorem pk_210 : ¬ Nat.Prime ((210+1)^(Nat.totient (1408-210)/2) - 210) := refute_e 210 299 145687 (by decide) (by decide)
theorem pk_211 : ¬ Nat.Prime ((211+1)^(Nat.totient (1408-211)/2) - 211) := refute_e 211 324 3 (by decide) (by decide)
theorem pk_212 : ¬ Nat.Prime ((212+1)^(Nat.totient (1408-212)/2) - 212) := refute_e 212 264 11 (by decide) (by decide)
theorem pk_213 : ¬ Nat.Prime ((213+1)^(Nat.totient (1408-213)/2) - 213) := refute_e 213 476 19 (by decide) (by decide)
theorem pk_214 : ¬ Nat.Prime ((214+1)^(Nat.totient (1408-214)/2) - 214) := refute_e 214 198 3 (by decide) (by decide)
theorem pk_215 : ¬ Nat.Prime ((215+1)^(Nat.totient (1408-215)/2) - 215) := refute_e 215 596 1531 (by decide) (by decide)
theorem pk_216 : ¬ Nat.Prime ((216+1)^(Nat.totient (1408-216)/2) - 216) := refute_e 216 296 5 (by decide) (by decide)
theorem pk_217 : ¬ Nat.Prime ((217+1)^(Nat.totient (1408-217)/2) - 217) := refute_e 217 396 3 (by decide) (by decide)
theorem pk_218 : ¬ Nat.Prime ((218+1)^(Nat.totient (1408-218)/2) - 218) := refute_e 218 192 7 (by decide) (by decide)
theorem pk_219 : ¬ Nat.Prime ((219+1)^(Nat.totient (1408-219)/2) - 219) := refute_e 219 560 7 (by decide) (by decide)
theorem pk_220 : ¬ Nat.Prime ((220+1)^(Nat.totient (1408-220)/2) - 220) := refute_e 220 180 3 (by decide) (by decide)
theorem pk_221 : ¬ Nat.Prime ((221+1)^(Nat.totient (1408-221)/2) - 221) := refute_fermat 221 593 165485965792060128230838969526996583765037550759996141702559600646979042991143619696451831903855894434100433816807455124557706614036800950715209644715556672288265798402428798500797625398716412971699682860498882199244071866299965356126397201827254352100995975339727708660901644031549719020748251516676618161216950379508138284250258007908526476208995270046165085534477738851201829514306052659299857492127554513667923253113218482898661986542325028304796728470948797411768282057954599511574104270820130898755905045243582012689565673059099577948888425361421104040122734208505273312171094702572511101237641181194060376964427763280165797371658898936957086440526506587156773794688766779320320588753152552417096126855547218961132110499377542517326417432646790619576014298936250241526944896707898743674256064923374268302095535804784206612358196974716849472127784460155322757897872262393273960813759912521504941995588119459719241976329924764275917559044271484141079214709604857154504340115640112330161617694883327900923502096084562403990512787544218841296029381007778628784436618573613436859983691032892765962585549727612882624563279428655858543840447192442979674597738296109193376479077307108838638266096722480204731640649848054818333813592277062768533596287508214591064171924491971571533005418756746217824065111796690317034766719683107044045077417958236704454446865905800336746817374182920220280268639 (by decide) (by norm_num) (by norm_num) (by norm_num) (by decide) (by reduce_mod_char)
theorem pk_222 : ¬ Nat.Prime ((222+1)^(Nat.totient (1408-222)/2) - 222) := refute_e 222 296 17 (by decide) (by decide)
theorem pk_223 : ¬ Nat.Prime ((223+1)^(Nat.totient (1408-223)/2) - 223) := refute_e 223 312 3 (by decide) (by decide)
theorem pk_224 : ¬ Nat.Prime ((224+1)^(Nat.totient (1408-224)/2) - 224) := refute_e 224 288 11 (by decide) (by decide)
theorem pk_225 : ¬ Nat.Prime ((225+1)^(Nat.totient (1408-225)/2) - 225) := refute_e 225 468 7 (by decide) (by decide)
theorem pk_226 : ¬ Nat.Prime ((226+1)^(Nat.totient (1408-226)/2) - 226) := refute_e 226 196 3 (by decide) (by decide)
theorem pk_227 : ¬ Nat.Prime ((227+1)^(Nat.totient (1408-227)/2) - 227) := refute_e 227 590 73 (by decide) (by decide)
theorem pk_228 : ¬ Nat.Prime ((228+1)^(Nat.totient (1408-228)/2) - 228) := refute_e 228 232 67057 (by decide) (by decide)
theorem pk_229 : ¬ Nat.Prime ((229+1)^(Nat.totient (1408-229)/2) - 229) := refute_e 229 390 3 (by decide) (by decide)
theorem pk_230 : ¬ Nat.Prime ((230+1)^(Nat.totient (1408-230)/2) - 230) := refute_e 230 270 27011 (by decide) (by decide)
theorem pk_231 : ¬ Nat.Prime ((231+1)^(Nat.totient (1408-231)/2) - 231) := refute_e 231 530 73 (by decide) (by decide)
theorem pk_232 : ¬ Nat.Prime ((232+1)^(Nat.totient (1408-232)/2) - 232) := refute_e 232 168 3 (by decide) (by decide)
theorem pk_233 : ¬ Nat.Prime ((233+1)^(Nat.totient (1408-233)/2) - 233) := refute_e 233 460 6734346677 (by decide) (by decide)
theorem pk_234 : ¬ Nat.Prime ((234+1)^(Nat.totient (1408-234)/2) - 234) := refute_e 234 293 1361682414135461797 (by decide) (by decide)
theorem pk_235 : ¬ Nat.Prime ((235+1)^(Nat.totient (1408-235)/2) - 235) := refute_e 235 352 3 (by decide) (by decide)
theorem pk_236 : ¬ Nat.Prime ((236+1)^(Nat.totient (1408-236)/2) - 236) := refute_e 236 292 5 (by decide) (by decide)
theorem pk_237 : ¬ Nat.Prime ((237+1)^(Nat.totient (1408-237)/2) - 237) := refute_e 237 585 41 (by decide) (by decide)
theorem pk_238 : ¬ Nat.Prime ((238+1)^(Nat.totient (1408-238)/2) - 238) := refute_e 238 144 3 (by decide) (by decide)
theorem pk_239 : ¬ Nat.Prime ((239+1)^(Nat.totient (1408-239)/2) - 239) := refute_e 239 498 7 (by decide) (by decide)
theorem pk_240 : ¬ Nat.Prime ((240+1)^(Nat.totient (1408-240)/2) - 240) := refute_e 240 288 103 (by decide) (by decide)
theorem pk_241 : ¬ Nat.Prime ((241+1)^(Nat.totient (1408-241)/2) - 241) := refute_e 241 388 3 (by decide) (by decide)
theorem pk_242 : ¬ Nat.Prime ((242+1)^(Nat.totient (1408-242)/2) - 242) := refute_e 242 260 7 (by decide) (by decide)
theorem pk_243 : ¬ Nat.Prime ((243+1)^(Nat.totient (1408-243)/2) - 243) := refute_e 243 464 13 (by decide) (by decide)
theorem pk_244 : ¬ Nat.Prime ((244+1)^(Nat.totient (1408-244)/2) - 244) := refute_e 244 192 3 (by decide) (by decide)
theorem pk_245 : ¬ Nat.Prime ((245+1)^(Nat.totient (1408-245)/2) - 245) := refute_e 245 581 47 (by decide) (by decide)
theorem pk_246 : ¬ Nat.Prime ((246+1)^(Nat.totient (1408-246)/2) - 246) := refute_e 246 246 7 (by decide) (by decide)
theorem pk_247 : ¬ Nat.Prime ((247+1)^(Nat.totient (1408-247)/2) - 247) := refute_e 247 378 3 (by decide) (by decide)
theorem pk_248 : ¬ Nat.Prime ((248+1)^(Nat.totient (1408-248)/2) - 248) := refute_e 248 224 37 (by decide) (by decide)
theorem pk_249 : ¬ Nat.Prime ((249+1)^(Nat.totient (1408-249)/2) - 249) := refute_e 249 540 31 (by decide) (by decide)
theorem pk_250 : ¬ Nat.Prime ((250+1)^(Nat.totient (1408-250)/2) - 250) := refute_e 250 192 3 (by decide) (by decide)
theorem pk_251 : ¬ Nat.Prime ((251+1)^(Nat.totient (1408-251)/2) - 251) := refute_e 251 528 5 (by decide) (by decide)
theorem pk_252 : ¬ Nat.Prime ((252+1)^(Nat.totient (1408-252)/2) - 252) := refute_e 252 272 103 (by decide) (by decide)
theorem pk_253 : ¬ Nat.Prime ((253+1)^(Nat.totient (1408-253)/2) - 253) := refute_e 253 240 3 (by decide) (by decide)
theorem pk_254 : ¬ Nat.Prime ((254+1)^(Nat.totient (1408-254)/2) - 254) := refute_e 254 288 814219012488096081435047 (by decide) (by decide)
theorem pk_255 : ¬ Nat.Prime ((255+1)^(Nat.totient (1408-255)/2) - 255) := refute_e 255 576 5568615539 (by decide) (by decide)
theorem pk_256 : ¬ Nat.Prime ((256+1)^(Nat.totient (1408-256)/2) - 256) := refute_e 256 192 3 (by decide) (by decide)
theorem pk_257 : ¬ Nat.Prime ((257+1)^(Nat.totient (1408-257)/2) - 257) := refute_e 257 575 5 (by decide) (by decide)
theorem pk_258 : ¬ Nat.Prime ((258+1)^(Nat.totient (1408-258)/2) - 258) := refute_e 258 220 4339 (by decide) (by decide)
theorem pk_259 : ¬ Nat.Prime ((259+1)^(Nat.totient (1408-259)/2) - 259) := refute_e 259 382 3 (by decide) (by decide)
theorem pk_260 : ¬ Nat.Prime ((260+1)^(Nat.totient (1408-260)/2) - 260) := refute_e 260 240 7 (by decide) (by decide)
theorem pk_261 : ¬ Nat.Prime ((261+1)^(Nat.totient (1408-261)/2) - 261) := refute_e 261 540 5 (by decide) (by decide)
theorem pk_262 : ¬ Nat.Prime ((262+1)^(Nat.totient (1408-262)/2) - 262) := refute_e 262 190 3 (by decide) (by decide)
theorem pk_263 : ¬ Nat.Prime ((263+1)^(Nat.totient (1408-263)/2) - 263) := refute_e 263 456 167 (by decide) (by decide)
theorem pk_264 : ¬ Nat.Prime ((264+1)^(Nat.totient (1408-264)/2) - 264) := refute_e 264 240 846647 (by decide) (by decide)
theorem pk_265 : ¬ Nat.Prime ((265+1)^(Nat.totient (1408-265)/2) - 265) := refute_e 265 378 3 (by decide) (by decide)
theorem pk_266 : ¬ Nat.Prime ((266+1)^(Nat.totient (1408-266)/2) - 266) := refute_e 266 285 249947 (by decide) (by decide)
theorem pk_267 : ¬ Nat.Prime ((267+1)^(Nat.totient (1408-267)/2) - 267) := refute_e 267 486 7 (by decide) (by decide)
theorem pk_268 : ¬ Nat.Prime ((268+1)^(Nat.totient (1408-268)/2) - 268) := refute_e 268 144 3 (by decide) (by decide)
theorem pk_269 : ¬ Nat.Prime ((269+1)^(Nat.totient (1408-269)/2) - 269) := refute_e 269 528 67 (by decide) (by decide)
theorem pk_270 : ¬ Nat.Prime ((270+1)^(Nat.totient (1408-270)/2) - 270) := refute_e 270 284 7 (by decide) (by decide)
theorem pk_271 : ¬ Nat.Prime ((271+1)^(Nat.totient (1408-271)/2) - 271) := refute_e 271 378 3 (by decide) (by decide)
theorem pk_272 : ¬ Nat.Prime ((272+1)^(Nat.totient (1408-272)/2) - 272) := refute_e 272 280 2423 (by decide) (by decide)
theorem pk_273 : ¬ Nat.Prime ((273+1)^(Nat.totient (1408-273)/2) - 273) := refute_e 273 452 19 (by decide) (by decide)
theorem pk_274 : ¬ Nat.Prime ((274+1)^(Nat.totient (1408-274)/2) - 274) := refute_e 274 162 3 (by decide) (by decide)
theorem pk_275 : ¬ Nat.Prime ((275+1)^(Nat.totient (1408-275)/2) - 275) := refute_e 275 510 5087861 (by decide) (by decide)
theorem pk_276 : ¬ Nat.Prime ((276+1)^(Nat.totient (1408-276)/2) - 276) := refute_e 276 282 137 (by decide) (by decide)
theorem pk_277 : ¬ Nat.Prime ((277+1)^(Nat.totient (1408-277)/2) - 277) := refute_e 277 336 3 (by decide) (by decide)
theorem pk_278 : ¬ Nat.Prime ((278+1)^(Nat.totient (1408-278)/2) - 278) := refute_e 278 224 11 (by decide) (by decide)
theorem pk_279 : ¬ Nat.Prime ((279+1)^(Nat.totient (1408-279)/2) - 279) := refute_e 279 564 5839 (by decide) (by decide)
theorem pk_280 : ¬ Nat.Prime ((280+1)^(Nat.totient (1408-280)/2) - 280) := refute_e 280 184 3 (by decide) (by decide)
theorem pk_281 : ¬ Nat.Prime ((281+1)^(Nat.totient (1408-281)/2) - 281) := refute_e 281 462 7 (by decide) (by decide)
theorem pk_282 : ¬ Nat.Prime ((282+1)^(Nat.totient (1408-282)/2) - 282) := refute_e 282 281 188212071547 (by decide) (by decide)
theorem pk_283 : ¬ Nat.Prime ((283+1)^(Nat.totient (1408-283)/2) - 283) := refute_e 283 300 3 (by decide) (by decide)
theorem pk_284 : ¬ Nat.Prime ((284+1)^(Nat.totient (1408-284)/2) - 284) := refute_e 284 280 23 (by decide) (by decide)
theorem pk_285 : ¬ Nat.Prime ((285+1)^(Nat.totient (1408-285)/2) - 285) := refute_e 285 561 149 (by decide) (by decide)
theorem pk_286 : ¬ Nat.Prime ((286+1)^(Nat.totient (1408-286)/2) - 286) := refute_e 286 160 3 (by decide) (by decide)
theorem pk_287 : ¬ Nat.Prime ((287+1)^(Nat.totient (1408-287)/2) - 287) := refute_e 287 522 363057971523869 (by decide) (by decide)
theorem pk_288 : ¬ Nat.Prime ((288+1)^(Nat.totient (1408-288)/2) - 288) := refute_e 288 192 7 (by decide) (by decide)
theorem pk_289 : ¬ Nat.Prime ((289+1)^(Nat.totient (1408-289)/2) - 289) := refute_e 289 372 3 (by decide) (by decide)
theorem pk_290 : ¬ Nat.Prime ((290+1)^(Nat.totient (1408-290)/2) - 290) := refute_e 290 252 67 (by decide) (by decide)
theorem pk_291 : ¬ Nat.Prime ((291+1)^(Nat.totient (1408-291)/2) - 291) := refute_e 291 558 17 (by decide) (by decide)
theorem pk_292 : ¬ Nat.Prime ((292+1)^(Nat.totient (1408-292)/2) - 292) := refute_e 292 180 3 (by decide) (by decide)
theorem pk_293 : ¬ Nat.Prime ((293+1)^(Nat.totient (1408-293)/2) - 293) := refute_e 293 444 17 (by decide) (by decide)
theorem pk_294 : ¬ Nat.Prime ((294+1)^(Nat.totient (1408-294)/2) - 294) := refute_e 294 278 23 (by decide) (by decide)
theorem pk_295 : ¬ Nat.Prime ((295+1)^(Nat.totient (1408-295)/2) - 295) := refute_e 295 312 3 (by decide) (by decide)
theorem pk_296 : ¬ Nat.Prime ((296+1)^(Nat.totient (1408-296)/2) - 296) := refute_e 296 276 5 (by decide) (by decide)
theorem pk_297 : ¬ Nat.Prime ((297+1)^(Nat.totient (1408-297)/2) - 297) := refute_e 297 500 67 (by decide) (by decide)
theorem pk_298 : ¬ Nat.Prime ((298+1)^(Nat.totient (1408-298)/2) - 298) := refute_e 298 144 3 (by decide) (by decide)
theorem pk_299 : ¬ Nat.Prime ((299+1)^(Nat.totient (1408-299)/2) - 299) := refute_e 299 554 271 (by decide) (by decide)
theorem pk_300 : ¬ Nat.Prime ((300+1)^(Nat.totient (1408-300)/2) - 300) := refute_e 300 276 13 (by decide) (by decide)
theorem pk_301 : ¬ Nat.Prime ((301+1)^(Nat.totient (1408-301)/2) - 301) := refute_e 301 360 3 (by decide) (by decide)
theorem pk_302 : ¬ Nat.Prime ((302+1)^(Nat.totient (1408-302)/2) - 302) := refute_e 302 234 7 (by decide) (by decide)
theorem pk_303 : ¬ Nat.Prime ((303+1)^(Nat.totient (1408-303)/2) - 303) := refute_e 303 384 2753 (by decide) (by decide)
theorem pk_304 : ¬ Nat.Prime ((304+1)^(Nat.totient (1408-304)/2) - 304) := refute_e 304 176 3 (by decide) (by decide)
theorem pk_305 : ¬ Nat.Prime ((305+1)^(Nat.totient (1408-305)/2) - 305) := refute_e 305 551 21419 (by decide) (by decide)
theorem pk_306 : ¬ Nat.Prime ((306+1)^(Nat.totient (1408-306)/2) - 306) := refute_e 306 252 5 (by decide) (by decide)
theorem pk_307 : ¬ Nat.Prime ((307+1)^(Nat.totient (1408-307)/2) - 307) := refute_e 307 366 3 (by decide) (by decide)
theorem pk_308 : ¬ Nat.Prime ((308+1)^(Nat.totient (1408-308)/2) - 308) := refute_e 308 200 13 (by decide) (by decide)
theorem pk_309 : ¬ Nat.Prime ((309+1)^(Nat.totient (1408-309)/2) - 309) := refute_e 309 468 7 (by decide) (by decide)
theorem pk_310 : ¬ Nat.Prime ((310+1)^(Nat.totient (1408-310)/2) - 310) := refute_e 310 180 3 (by decide) (by decide)
theorem pk_311 : ¬ Nat.Prime ((311+1)^(Nat.totient (1408-311)/2) - 311) := refute_e 311 548 5 (by decide) (by decide)
theorem pk_312 : ¬ Nat.Prime ((312+1)^(Nat.totient (1408-312)/2) - 312) := refute_e 312 272 7 (by decide) (by decide)
theorem pk_313 : ¬ Nat.Prime ((313+1)^(Nat.totient (1408-313)/2) - 313) := refute_e 313 288 3 (by decide) (by decide)
theorem pk_314 : ¬ Nat.Prime ((314+1)^(Nat.totient (1408-314)/2) - 314) := refute_e 314 273 59 (by decide) (by decide)
theorem pk_315 : ¬ Nat.Prime ((315+1)^(Nat.totient (1408-315)/2) - 315) := refute_e 315 546 59 (by decide) (by decide)
theorem pk_316 : ¬ Nat.Prime ((316+1)^(Nat.totient (1408-316)/2) - 316) := refute_e 316 144 3 (by decide) (by decide)
theorem pk_317 : ¬ Nat.Prime ((317+1)^(Nat.totient (1408-317)/2) - 317) := refute_e 317 545 116243 (by decide) (by decide)
theorem pk_318 : ¬ Nat.Prime ((318+1)^(Nat.totient (1408-318)/2) - 318) := refute_e 318 216 31 (by decide) (by decide)
theorem pk_319 : ¬ Nat.Prime ((319+1)^(Nat.totient (1408-319)/2) - 319) := refute_e 319 330 3 (by decide) (by decide)
theorem pk_320 : ¬ Nat.Prime ((320+1)^(Nat.totient (1408-320)/2) - 320) := refute_e 320 256 19 (by decide) (by decide)
theorem pk_321 : ¬ Nat.Prime ((321+1)^(Nat.totient (1408-321)/2) - 321) := refute_e 321 543 14281 (by decide) (by decide)
theorem pk_322 : ¬ Nat.Prime ((322+1)^(Nat.totient (1408-322)/2) - 322) := refute_e 322 180 3 (by decide) (by decide)
theorem pk_323 : ¬ Nat.Prime ((323+1)^(Nat.totient (1408-323)/2) - 323) := refute_e 323 360 7 (by decide) (by decide)
theorem pk_324 : ¬ Nat.Prime ((324+1)^(Nat.totient (1408-324)/2) - 324) := refute_e 324 270 19 (by decide) (by decide)
theorem pk_325 : ¬ Nat.Prime ((325+1)^(Nat.totient (1408-325)/2) - 325) := refute_e 325 342 3 (by decide) (by decide)
theorem pk_326 : ¬ Nat.Prime ((326+1)^(Nat.totient (1408-326)/2) - 326) := refute_e 326 270 4027 (by decide) (by decide)
theorem pk_327 : ¬ Nat.Prime ((327+1)^(Nat.totient (1408-327)/2) - 327) := refute_e 327 506 283 (by decide) (by decide)
theorem pk_328 : ¬ Nat.Prime ((328+1)^(Nat.totient (1408-328)/2) - 328) := refute_e 328 144 3 (by decide) (by decide)
theorem pk_329 : ¬ Nat.Prime ((329+1)^(Nat.totient (1408-329)/2) - 329) := refute_e 329 492 144335748923 (by decide) (by decide)
theorem pk_330 : ¬ Nat.Prime ((330+1)^(Nat.totient (1408-330)/2) - 330) := refute_e 330 210 7 (by decide) (by decide)
theorem pk_331 : ¬ Nat.Prime ((331+1)^(Nat.totient (1408-331)/2) - 331) := refute_e 331 358 3 (by decide) (by decide)
theorem pk_332 : ¬ Nat.Prime ((332+1)^(Nat.totient (1408-332)/2) - 332) := refute_e 332 268 283 (by decide) (by decide)
theorem pk_333 : ¬ Nat.Prime ((333+1)^(Nat.totient (1408-333)/2) - 333) := refute_e 333 420 229 (by decide) (by decide)
theorem pk_334 : ¬ Nat.Prime ((334+1)^(Nat.totient (1408-334)/2) - 334) := refute_e 334 178 3 (by decide) (by decide)
theorem pk_335 : ¬ Nat.Prime ((335+1)^(Nat.totient (1408-335)/2) - 335) := refute_e 335 504 240763273 (by decide) (by decide)
theorem pk_336 : ¬ Nat.Prime ((336+1)^(Nat.totient (1408-336)/2) - 336) := refute_e 336 264 5 (by decide) (by decide)
theorem pk_337 : ¬ Nat.Prime ((337+1)^(Nat.totient (1408-337)/2) - 337) := refute_e 337 288 3 (by decide) (by decide)
theorem pk_338 : ¬ Nat.Prime ((338+1)^(Nat.totient (1408-338)/2) - 338) := refute_e 338 212 7 (by decide) (by decide)
theorem pk_339 : ¬ Nat.Prime ((339+1)^(Nat.totient (1408-339)/2) - 339) := refute_e 339 534 251 (by decide) (by decide)
theorem pk_340 : ¬ Nat.Prime ((340+1)^(Nat.totient (1408-340)/2) - 340) := refute_e 340 176 3 (by decide) (by decide)
theorem pk_341 : ¬ Nat.Prime ((341+1)^(Nat.totient (1408-341)/2) - 341) := refute_e 341 480 5 (by decide) (by decide)
theorem pk_342 : ¬ Nat.Prime ((342+1)^(Nat.totient (1408-342)/2) - 342) := refute_e 342 240 11 (by decide) (by decide)
theorem pk_343 : ¬ Nat.Prime ((343+1)^(Nat.totient (1408-343)/2) - 343) := refute_e 343 280 3 (by decide) (by decide)
theorem pk_344 : ¬ Nat.Prime ((344+1)^(Nat.totient (1408-344)/2) - 344) := refute_e 344 216 7 (by decide) (by decide)
theorem pk_345 : ¬ Nat.Prime ((345+1)^(Nat.totient (1408-345)/2) - 345) := refute_e 345 531 3535047447299235049328717 (by decide) (by decide)
theorem pk_346 : ¬ Nat.Prime ((346+1)^(Nat.totient (1408-346)/2) - 346) := refute_e 346 174 3 (by decide) (by decide)
theorem pk_347 : ¬ Nat.Prime ((347+1)^(Nat.totient (1408-347)/2) - 347) := refute_e 347 530 7 (by decide) (by decide)
theorem pk_348 : ¬ Nat.Prime ((348+1)^(Nat.totient (1408-348)/2) - 348) := refute_e 348 208 83 (by decide) (by decide)
theorem pk_349 : ¬ Nat.Prime ((349+1)^(Nat.totient (1408-349)/2) - 349) := refute_e 349 352 3 (by decide) (by decide)
theorem pk_350 : ¬ Nat.Prime ((350+1)^(Nat.totient (1408-350)/2) - 350) := refute_e 350 253 31 (by decide) (by decide)
theorem pk_351 : ¬ Nat.Prime ((351+1)^(Nat.totient (1408-351)/2) - 351) := refute_e 351 450 7 (by decide) (by decide)
theorem pk_352 : ¬ Nat.Prime ((352+1)^(Nat.totient (1408-352)/2) - 352) := refute_e 352 160 3 (by decide) (by decide)
theorem pk_353 : ¬ Nat.Prime ((353+1)^(Nat.totient (1408-353)/2) - 353) := refute_e 353 420 11 (by decide) (by decide)
theorem pk_354 : ¬ Nat.Prime ((354+1)^(Nat.totient (1408-354)/2) - 354) := refute_fermat 354 240 293938039436603079010105870205433191859240991946065466838773867979766105083865435253313388828296056906211830123605323286494892814456301697508925680774960298937990063354487902271712269097734070636229117168716954574561705825959796920650377465865556354340235598434323475967782743774817426960168976446817942402676750024187333406671837631601697976686008960511571828987061941269569029394508943606704523626670668348478806171101241066967244680235762580469672663700693440158366930237951574281333695680302953490887649827688305284277612445669583011475522311540099034873399815908425492793002532312801406894956126477758079383 (by decide) (by norm_num) (by norm_num) (by norm_num) (by decide) (by reduce_mod_char)
theorem pk_355 : ¬ Nat.Prime ((355+1)^(Nat.totient (1408-355)/2) - 355) := refute_e 355 324 3 (by decide) (by decide)
theorem pk_356 : ¬ Nat.Prime ((356+1)^(Nat.totient (1408-356)/2) - 356) := refute_e 356 262 47 (by decide) (by decide)
theorem pk_357 : ¬ Nat.Prime ((357+1)^(Nat.totient (1408-357)/2) - 357) := refute_e 357 525 593149631 (by decide) (by decide)
theorem pk_358 : ¬ Nat.Prime ((358+1)^(Nat.totient (1408-358)/2) - 358) := refute_e 358 120 3 (by decide) (by decide)
theorem pk_359 : ¬ Nat.Prime ((359+1)^(Nat.totient (1408-359)/2) - 359) := refute_e 359 524 7 (by decide) (by decide)
theorem pk_360 : ¬ Nat.Prime ((360+1)^(Nat.totient (1408-360)/2) - 360) := refute_e 360 260 13 (by decide) (by decide)
theorem pk_361 : ¬ Nat.Prime ((361+1)^(Nat.totient (1408-361)/2) - 361) := refute_e 361 348 3 (by decide) (by decide)
theorem pk_362 : ¬ Nat.Prime ((362+1)^(Nat.totient (1408-362)/2) - 362) := refute_e 362 261 1613 (by decide) (by decide)
theorem pk_363 : ¬ Nat.Prime ((363+1)^(Nat.totient (1408-363)/2) - 363) := refute_e 363 360 181 (by decide) (by decide)
theorem pk_364 : ¬ Nat.Prime ((364+1)^(Nat.totient (1408-364)/2) - 364) := refute_e 364 168 3 (by decide) (by decide)
theorem pk_365 : ¬ Nat.Prime ((365+1)^(Nat.totient (1408-365)/2) - 365) := refute_e 365 444 7 (by decide) (by decide)
theorem pk_366 : ¬ Nat.Prime ((366+1)^(Nat.totient (1408-366)/2) - 366) := refute_e 366 260 5 (by decide) (by decide)
theorem pk_367 : ¬ Nat.Prime ((367+1)^(Nat.totient (1408-367)/2) - 367) := refute_e 367 346 3 (by decide) (by decide)
theorem pk_368 : ¬ Nat.Prime ((368+1)^(Nat.totient (1408-368)/2) - 368) := refute_e 368 192 79 (by decide) (by decide)
theorem pk_369 : ¬ Nat.Prime ((369+1)^(Nat.totient (1408-369)/2) - 369) := refute_e 369 519 402923 (by decide) (by decide)
theorem pk_370 : ¬ Nat.Prime ((370+1)^(Nat.totient (1408-370)/2) - 370) := refute_e 370 172 3 (by decide) (by decide)
theorem pk_371 : ¬ Nat.Prime ((371+1)^(Nat.totient (1408-371)/2) - 371) := refute_e 371 480 5 (by decide) (by decide)
theorem pk_372 : ¬ Nat.Prime ((372+1)^(Nat.totient (1408-372)/2) - 372) := refute_e 372 216 7 (by decide) (by decide)
theorem pk_373 : ¬ Nat.Prime ((373+1)^(Nat.totient (1408-373)/2) - 373) := refute_e 373 264 3 (by decide) (by decide)
theorem pk_374 : ¬ Nat.Prime ((374+1)^(Nat.totient (1408-374)/2) - 374) := refute_e 374 230 139 (by decide) (by decide)
theorem pk_375 : ¬ Nat.Prime ((375+1)^(Nat.totient (1408-375)/2) - 375) := refute_e 375 516 293 (by decide) (by decide)
theorem pk_376 : ¬ Nat.Prime ((376+1)^(Nat.totient (1408-376)/2) - 376) := refute_e 376 168 3 (by decide) (by decide)
theorem pk_377 : ¬ Nat.Prime ((377+1)^(Nat.totient (1408-377)/2) - 377) := refute_e 377 515 5 (by decide) (by decide)
theorem pk_378 : ¬ Nat.Prime ((378+1)^(Nat.totient (1408-378)/2) - 378) := refute_e 378 204 13 (by decide) (by decide)
theorem pk_379 : ¬ Nat.Prime ((379+1)^(Nat.totient (1408-379)/2) - 379) := refute_e 379 294 3 (by decide) (by decide)
theorem pk_380 : ¬ Nat.Prime ((380+1)^(Nat.totient (1408-380)/2) - 380) := refute_e 380 256 23 (by decide) (by decide)
theorem pk_381 : ¬ Nat.Prime ((381+1)^(Nat.totient (1408-381)/2) - 381) := refute_e 381 468 5 (by decide) (by decide)
theorem pk_382 : ¬ Nat.Prime ((382+1)^(Nat.totient (1408-382)/2) - 382) := refute_e 382 162 3 (by decide) (by decide)
theorem pk_383 : ¬ Nat.Prime ((383+1)^(Nat.totient (1408-383)/2) - 383) := refute_e 383 400 1769500854815943251 (by decide) (by decide)
theorem pk_384 : ¬ Nat.Prime ((384+1)^(Nat.totient (1408-384)/2) - 384) := refute_e 384 256 29 (by decide) (by decide)
theorem pk_385 : ¬ Nat.Prime ((385+1)^(Nat.totient (1408-385)/2) - 385) := refute_e 385 300 3 (by decide) (by decide)
theorem pk_386 : ¬ Nat.Prime ((386+1)^(Nat.totient (1408-386)/2) - 386) := refute_e 386 216 5 (by decide) (by decide)
theorem pk_387 : ¬ Nat.Prime ((387+1)^(Nat.totient (1408-387)/2) - 387) := refute_e 387 510 53 (by decide) (by decide)
theorem pk_388 : ¬ Nat.Prime ((388+1)^(Nat.totient (1408-388)/2) - 388) := refute_e 388 128 3 (by decide) (by decide)
theorem pk_389 : ¬ Nat.Prime ((389+1)^(Nat.totient (1408-389)/2) - 389) := refute_e 389 509 809 (by decide) (by decide)
theorem pk_390 : ¬ Nat.Prime ((390+1)^(Nat.totient (1408-390)/2) - 390) := refute_e 390 254 31 (by decide) (by decide)
theorem pk_391 : ¬ Nat.Prime ((391+1)^(Nat.totient (1408-391)/2) - 391) := refute_e 391 336 3 (by decide) (by decide)
theorem pk_392 : ¬ Nat.Prime ((392+1)^(Nat.totient (1408-392)/2) - 392) := refute_e 392 252 41 (by decide) (by decide)
theorem pk_393 : ¬ Nat.Prime ((393+1)^(Nat.totient (1408-393)/2) - 393) := refute_e 393 336 7 (by decide) (by decide)
theorem pk_394 : ¬ Nat.Prime ((394+1)^(Nat.totient (1408-394)/2) - 394) := refute_e 394 156 3 (by decide) (by decide)
theorem pk_395 : ¬ Nat.Prime ((395+1)^(Nat.totient (1408-395)/2) - 395) := refute_e 395 506 331 (by decide) (by decide)
theorem pk_396 : ¬ Nat.Prime ((396+1)^(Nat.totient (1408-396)/2) - 396) := refute_e 396 220 5 (by decide) (by decide)
theorem pk_397 : ¬ Nat.Prime ((397+1)^(Nat.totient (1408-397)/2) - 397) := refute_e 397 336 3 (by decide) (by decide)
theorem pk_398 : ¬ Nat.Prime ((398+1)^(Nat.totient (1408-398)/2) - 398) := refute_e 398 200 158803 (by decide) (by decide)
theorem pk_399 : ¬ Nat.Prime ((399+1)^(Nat.totient (1408-399)/2) - 399) := refute_e 399 504 11 (by decide) (by decide)
theorem pk_400 : ¬ Nat.Prime ((400+1)^(Nat.totient (1408-400)/2) - 400) := refute_e 400 144 3 (by decide) (by decide)
theorem pk_401 : ¬ Nat.Prime ((401+1)^(Nat.totient (1408-401)/2) - 401) := refute_e 401 468 5 (by decide) (by decide)
theorem pk_402 : ¬ Nat.Prime ((402+1)^(Nat.totient (1408-402)/2) - 402) := refute_e 402 251 5 (by decide) (by decide)
theorem pk_403 : ¬ Nat.Prime ((403+1)^(Nat.totient (1408-403)/2) - 403) := refute_e 403 264 3 (by decide) (by decide)
theorem pk_404 : ¬ Nat.Prime ((404+1)^(Nat.totient (1408-404)/2) - 404) := refute_e 404 250 23 (by decide) (by decide)
theorem pk_405 : ¬ Nat.Prime ((405+1)^(Nat.totient (1408-405)/2) - 405) := refute_e 405 464 1949 (by decide) (by decide)
theorem pk_406 : ¬ Nat.Prime ((406+1)^(Nat.totient (1408-406)/2) - 406) := refute_e 406 166 3 (by decide) (by decide)
theorem pk_407 : ¬ Nat.Prime ((407+1)^(Nat.totient (1408-407)/2) - 407) := refute_e 407 360 7 (by decide) (by decide)
theorem pk_408 : ¬ Nat.Prime ((408+1)^(Nat.totient (1408-408)/2) - 408) := refute_e 408 200 7 (by decide) (by decide)
theorem pk_409 : ¬ Nat.Prime ((409+1)^(Nat.totient (1408-409)/2) - 409) := refute_e 409 324 3 (by decide) (by decide)
theorem pk_410 : ¬ Nat.Prime ((410+1)^(Nat.totient (1408-410)/2) - 410) := refute_e 410 249 11 (by decide) (by decide)
theorem pk_411 : ¬ Nat.Prime ((411+1)^(Nat.totient (1408-411)/2) - 411) := refute_e 411 498 11 (by decide) (by decide)
theorem pk_412 : ¬ Nat.Prime ((412+1)^(Nat.totient (1408-412)/2) - 412) := refute_e 412 164 3 (by decide) (by decide)
theorem pk_413 : ¬ Nat.Prime ((413+1)^(Nat.totient (1408-413)/2) - 413) := refute_e 413 396 29 (by decide) (by decide)
theorem pk_414 : ¬ Nat.Prime ((414+1)^(Nat.totient (1408-414)/2) - 414) := refute_e 414 210 7 (by decide) (by decide)
theorem pk_415 : ¬ Nat.Prime ((415+1)^(Nat.totient (1408-415)/2) - 415) := refute_e 415 330 3 (by decide) (by decide)
theorem pk_416 : ¬ Nat.Prime ((416+1)^(Nat.totient (1408-416)/2) - 416) := refute_e 416 240 5 (by decide) (by decide)
theorem pk_417 : ¬ Nat.Prime ((417+1)^(Nat.totient (1408-417)/2) - 417) := refute_e 417 495 5 (by decide) (by decide)
theorem pk_418 : ¬ Nat.Prime ((418+1)^(Nat.totient (1408-418)/2) - 418) := refute_e 418 120 3 (by decide) (by decide)
theorem pk_419 : ¬ Nat.Prime ((419+1)^(Nat.totient (1408-419)/2) - 419) := refute_e 419 462 223 (by decide) (by decide)
theorem pk_420 : ¬ Nat.Prime ((420+1)^(Nat.totient (1408-420)/2) - 420) := refute_e 420 216 41 (by decide) (by decide)
theorem pk_421 : ¬ Nat.Prime ((421+1)^(Nat.totient (1408-421)/2) - 421) := refute_e 421 276 3 (by decide) (by decide)
theorem pk_422 : ¬ Nat.Prime ((422+1)^(Nat.totient (1408-422)/2) - 422) := refute_e 422 224 7 (by decide) (by decide)
theorem pk_423 : ¬ Nat.Prime ((423+1)^(Nat.totient (1408-423)/2) - 423) := refute_e 423 392 19 (by decide) (by decide)
theorem pk_424 : ¬ Nat.Prime ((424+1)^(Nat.totient (1408-424)/2) - 424) := refute_e 424 160 3 (by decide) (by decide)
theorem pk_425 : ¬ Nat.Prime ((425+1)^(Nat.totient (1408-425)/2) - 425) := refute_e 425 491 137 (by decide) (by decide)
theorem pk_426 : ¬ Nat.Prime ((426+1)^(Nat.totient (1408-426)/2) - 426) := refute_e 426 245 23 (by decide) (by decide)
theorem pk_427 : ¬ Nat.Prime ((427+1)^(Nat.totient (1408-427)/2) - 427) := refute_e 427 324 3 (by decide) (by decide)
theorem pk_428 : ¬ Nat.Prime ((428+1)^(Nat.totient (1408-428)/2) - 428) := refute_e 428 168 7 (by decide) (by decide)
theorem pk_429 : ¬ Nat.Prime ((429+1)^(Nat.totient (1408-429)/2) - 429) := refute_e 429 440 7 (by decide) (by decide)
theorem pk_430 : ¬ Nat.Prime ((430+1)^(Nat.totient (1408-430)/2) - 430) := refute_e 430 162 3 (by decide) (by decide)
theorem pk_431 : ¬ Nat.Prime ((431+1)^(Nat.totient (1408-431)/2) - 431) := refute_e 431 488 5 (by decide) (by decide)
theorem pk_432 : ¬ Nat.Prime ((432+1)^(Nat.totient (1408-432)/2) - 432) := refute_e 432 240 109 (by decide) (by decide)
theorem pk_433 : ¬ Nat.Prime ((433+1)^(Nat.totient (1408-433)/2) - 433) := refute_e 433 240 3 (by decide) (by decide)
theorem pk_434 : ¬ Nat.Prime ((434+1)^(Nat.totient (1408-434)/2) - 434) := refute_e 434 243 431 (by decide) (by decide)
theorem pk_435 : ¬ Nat.Prime ((435+1)^(Nat.totient (1408-435)/2) - 435) := refute_e 435 414 7 (by decide) (by decide)
theorem pk_436 : ¬ Nat.Prime ((436+1)^(Nat.totient (1408-436)/2) - 436) := refute_e 436 162 3 (by decide) (by decide)
theorem pk_437 : ¬ Nat.Prime ((437+1)^(Nat.totient (1408-437)/2) - 437) := refute_e 437 485 4363 (by decide) (by decide)
theorem pk_438 : ¬ Nat.Prime ((438+1)^(Nat.totient (1408-438)/2) - 438) := refute_fermat 438 192 1921199965818544348280305681747081991232504135290241435659962819845545500176832839407609633170399713161199085332934671194153949977120761849085683577135093407281521687107520192396585318005618060592746926653551646239305740439010398687344322428849055945185079185887813349889507365994573777258581725747400572620509262503184542081917769049818298152300075466325499363844676877765567120281147105090951870323159567259252180337479105229801241079294890914508927601044143311267290283908172789403898532499768265628897421 (by decide) (by norm_num) (by norm_num) (by norm_num) (by decide) (by reduce_mod_char)
theorem pk_439 : ¬ Nat.Prime ((439+1)^(Nat.totient (1408-439)/2) - 439) := refute_e 439 288 3 (by decide) (by decide)
theorem pk_440 : ¬ Nat.Prime ((440+1)^(Nat.totient (1408-440)/2) - 440) := refute_e 440 220 157 (by decide) (by decide)
theorem pk_441 : ¬ Nat.Prime ((441+1)^(Nat.totient (1408-441)/2) - 441) := refute_e 441 483 269 (by decide) (by decide)
theorem pk_442 : ¬ Nat.Prime ((442+1)^(Nat.totient (1408-442)/2) - 442) := refute_e 442 132 3 (by decide) (by decide)
theorem pk_443 : ¬ Nat.Prime ((443+1)^(Nat.totient (1408-443)/2) - 443) := refute_e 443 384 11 (by decide) (by decide)
theorem pk_444 : ¬ Nat.Prime ((444+1)^(Nat.totient (1408-444)/2) - 444) := refute_e 444 240 3231236428727 (by decide) (by decide)
theorem pk_445 : ¬ Nat.Prime ((445+1)^(Nat.totient (1408-445)/2) - 445) := refute_e 445 318 3 (by decide) (by decide)
theorem pk_446 : ¬ Nat.Prime ((446+1)^(Nat.totient (1408-446)/2) - 446) := refute_e 446 216 5 (by decide) (by decide)
theorem pk_447 : ¬ Nat.Prime ((447+1)^(Nat.totient (1408-447)/2) - 447) := refute_e 447 465 13 (by decide) (by decide)
theorem pk_448 : ¬ Nat.Prime ((448+1)^(Nat.totient (1408-448)/2) - 448) := refute_e 448 128 3 (by decide) (by decide)
theorem pk_449 : ¬ Nat.Prime ((449+1)^(Nat.totient (1408-449)/2) - 449) := refute_e 449 408 7 (by decide) (by decide)
theorem pk_450 : ¬ Nat.Prime ((450+1)^(Nat.totient (1408-450)/2) - 450) := refute_e 450 239 47 (by decide) (by decide)
theorem pk_451 : ¬ Nat.Prime ((451+1)^(Nat.totient (1408-451)/2) - 451) := refute_e 451 280 3 (by decide) (by decide)
theorem pk_452 : ¬ Nat.Prime ((452+1)^(Nat.totient (1408-452)/2) - 452) := refute_e 452 238 13 (by decide) (by decide)
theorem pk_453 : ¬ Nat.Prime ((453+1)^(Nat.totient (1408-453)/2) - 453) := refute_e 453 380 149 (by decide) (by decide)
theorem pk_454 : ¬ Nat.Prime ((454+1)^(Nat.totient (1408-454)/2) - 454) := refute_e 454 156 3 (by decide) (by decide)
theorem pk_455 : ¬ Nat.Prime ((455+1)^(Nat.totient (1408-455)/2) - 455) := refute_e 455 476 23 (by decide) (by decide)
theorem pk_456 : ¬ Nat.Prime ((456+1)^(Nat.totient (1408-456)/2) - 456) := refute_e 456 192 5 (by decide) (by decide)
theorem pk_457 : ¬ Nat.Prime ((457+1)^(Nat.totient (1408-457)/2) - 457) := refute_e 457 316 3 (by decide) (by decide)
theorem pk_458 : ¬ Nat.Prime ((458+1)^(Nat.totient (1408-458)/2) - 458) := refute_e 458 180 20071 (by decide) (by decide)
theorem pk_459 : ¬ Nat.Prime ((459+1)^(Nat.totient (1408-459)/2) - 459) := refute_fermat 459 432 5108908529425879757468476576825697313995667817176519610644269172811162425080217318108773274068255435737568107511793901049228404161709186600396565397889618418111554689725042970744999336423415354641709639576510272463449003042858387197768499485415824820404562391414956854367568472381150258955013096752770381054184289133242187133014995767373009409371009328484956953001950174723798617466697964186761774313966371244208797715590057430745915185003019518213567800273421847951133149843677884224980558818143709426161946070079039733679232190386858804200896888790829829506523560385115952465069246088778696814821161923842184344060185262807276728682170588059644514846125730037191327909589750671747653150986389449420814490370091272354372462447644128022547020004460930531258698001327931687206337580874677087804006195961357062726747696251104491068208969486951590094879921376013319205885119048227237031488292370398098943792154898342667101511833343374520173123023770482261077694669503888932208313791258420773089616087180922845126227118307246785784472641591114298430303068276458887682926079962593705187621254418039599060835881364997109461813024624018782978128958130474863 (by decide) (by norm_num) (by norm_num) (by norm_num) (by decide) (by reduce_mod_char)
theorem pk_460 : ¬ Nat.Prime ((460+1)^(Nat.totient (1408-460)/2) - 460) := refute_e 460 156 3 (by decide) (by decide)
theorem pk_461 : ¬ Nat.Prime ((461+1)^(Nat.totient (1408-461)/2) - 461) := refute_e 461 473 19 (by decide) (by decide)
theorem pk_462 : ¬ Nat.Prime ((462+1)^(Nat.totient (1408-462)/2) - 462) := refute_e 462 210 289309 (by decide) (by decide)
theorem pk_463 : ¬ Nat.Prime ((463+1)^(Nat.totient (1408-463)/2) - 463) := refute_e 463 216 3 (by decide) (by decide)
theorem pk_464 : ¬ Nat.Prime ((464+1)^(Nat.totient (1408-464)/2) - 464) := refute_e 464 232 21894536939136486169 (by decide) (by decide)
theorem pk_465 : ¬ Nat.Prime ((465+1)^(Nat.totient (1408-465)/2) - 465) := refute_e 465 440 337 (by decide) (by decide)
theorem pk_466 : ¬ Nat.Prime ((466+1)^(Nat.totient (1408-466)/2) - 466) := refute_e 466 156 3 (by decide) (by decide)
theorem pk_467 : ¬ Nat.Prime ((467+1)^(Nat.totient (1408-467)/2) - 467) := refute_e 467 470 19 (by decide) (by decide)
theorem pk_468 : ¬ Nat.Prime ((468+1)^(Nat.totient (1408-468)/2) - 468) := refute_e 468 184 1901 (by decide) (by decide)
theorem pk_469 : ¬ Nat.Prime ((469+1)^(Nat.totient (1408-469)/2) - 469) := refute_e 469 312 3 (by decide) (by decide)
theorem pk_470 : ¬ Nat.Prime ((470+1)^(Nat.totient (1408-470)/2) - 470) := refute_e 470 198 7 (by decide) (by decide)
theorem pk_471 : ¬ Nat.Prime ((471+1)^(Nat.totient (1408-471)/2) - 471) := refute_e 471 468 5 (by decide) (by decide)
theorem pk_472 : ¬ Nat.Prime ((472+1)^(Nat.totient (1408-472)/2) - 472) := refute_e 472 144 3 (by decide) (by decide)
theorem pk_473 : ¬ Nat.Prime ((473+1)^(Nat.totient (1408-473)/2) - 473) := refute_e 473 320 7 (by decide) (by decide)
theorem pk_474 : ¬ Nat.Prime ((474+1)^(Nat.totient (1408-474)/2) - 474) := refute_e 474 233 102161 (by decide) (by decide)
theorem pk_475 : ¬ Nat.Prime ((475+1)^(Nat.totient (1408-475)/2) - 475) := refute_e 475 310 3 (by decide) (by decide)
theorem pk_476 : ¬ Nat.Prime ((476+1)^(Nat.totient (1408-476)/2) - 476) := refute_e 476 232 5 (by decide) (by decide)
theorem pk_477 : ¬ Nat.Prime ((477+1)^(Nat.totient (1408-477)/2) - 477) := refute_e 477 378 7 (by decide) (by decide)
theorem pk_478 : ¬ Nat.Prime ((478+1)^(Nat.totient (1408-478)/2) - 478) := refute_e 478 120 3 (by decide) (by decide)
theorem pk_479 : ¬ Nat.Prime ((479+1)^(Nat.totient (1408-479)/2) - 479) := refute_e 479 464 43 (by decide) (by decide)
theorem pk_480 : ¬ Nat.Prime ((480+1)^(Nat.totient (1408-480)/2) - 480) := refute_e 480 224 7 (by decide) (by decide)
theorem pk_481 : ¬ Nat.Prime ((481+1)^(Nat.totient (1408-481)/2) - 481) := refute_e 481 306 3 (by decide) (by decide)
theorem pk_482 : ¬ Nat.Prime ((482+1)^(Nat.totient (1408-482)/2) - 482) := refute_e 482 231 5 (by decide) (by decide)
theorem pk_483 : ¬ Nat.Prime ((483+1)^(Nat.totient (1408-483)/2) - 483) := refute_e 483 360 241 (by decide) (by decide)
theorem pk_484 : ¬ Nat.Prime ((484+1)^(Nat.totient (1408-484)/2) - 484) := refute_e 484 120 3 (by decide) (by decide)
theorem pk_485 : ¬ Nat.Prime ((485+1)^(Nat.totient (1408-485)/2) - 485) := refute_e 485 420 11 (by decide) (by decide)
theorem pk_486 : ¬ Nat.Prime ((486+1)^(Nat.totient (1408-486)/2) - 486) := refute_e 486 230 19 (by decide) (by decide)
theorem pk_487 : ¬ Nat.Prime ((487+1)^(Nat.totient (1408-487)/2) - 487) := refute_e 487 306 3 (by decide) (by decide)
theorem pk_488 : ¬ Nat.Prime ((488+1)^(Nat.totient (1408-488)/2) - 488) := refute_e 488 176 127 (by decide) (by decide)
theorem pk_489 : ¬ Nat.Prime ((489+1)^(Nat.totient (1408-489)/2) - 489) := refute_e 489 459 647 (by decide) (by decide)
theorem pk_490 : ¬ Nat.Prime ((490+1)^(Nat.totient (1408-490)/2) - 490) := refute_e 490 144 3 (by decide) (by decide)
theorem pk_491 : ¬ Nat.Prime ((491+1)^(Nat.totient (1408-491)/2) - 491) := refute_e 491 390 7 (by decide) (by decide)
theorem pk_492 : ¬ Nat.Prime ((492+1)^(Nat.totient (1408-492)/2) - 492) := refute_e 492 228 7307 (by decide) (by decide)
theorem pk_493 : ¬ Nat.Prime ((493+1)^(Nat.totient (1408-493)/2) - 493) := refute_e 493 240 3 (by decide) (by decide)
theorem pk_494 : ¬ Nat.Prime ((494+1)^(Nat.totient (1408-494)/2) - 494) := refute_e 494 228 26417 (by decide) (by decide)
theorem pk_495 : ¬ Nat.Prime ((495+1)^(Nat.totient (1408-495)/2) - 495) := refute_e 495 410 23 (by decide) (by decide)
theorem pk_496 : ¬ Nat.Prime ((496+1)^(Nat.totient (1408-496)/2) - 496) := refute_e 496 144 3 (by decide) (by decide)
theorem pk_497 : ¬ Nat.Prime ((497+1)^(Nat.totient (1408-497)/2) - 497) := refute_e 497 455 5 (by decide) (by decide)
theorem pk_498 : ¬ Nat.Prime ((498+1)^(Nat.totient (1408-498)/2) - 498) := refute_e 498 144 7 (by decide) (by decide)
theorem pk_499 : ¬ Nat.Prime ((499+1)^(Nat.totient (1408-499)/2) - 499) := refute_e 499 300 3 (by decide) (by decide)
theorem pk_500 : ¬ Nat.Prime ((500+1)^(Nat.totient (1408-500)/2) - 500) := refute_e 500 226 11 (by decide) (by decide)
theorem pk_501 : ¬ Nat.Prime ((501+1)^(Nat.totient (1408-501)/2) - 501) := refute_e 501 453 17 (by decide) (by decide)
theorem pk_502 : ¬ Nat.Prime ((502+1)^(Nat.totient (1408-502)/2) - 502) := refute_e 502 150 3 (by decide) (by decide)
theorem pk_503 : ¬ Nat.Prime ((503+1)^(Nat.totient (1408-503)/2) - 503) := refute_e 503 360 2083 (by decide) (by decide)
theorem pk_504 : ¬ Nat.Prime ((504+1)^(Nat.totient (1408-504)/2) - 504) := refute_e 504 224 199 (by decide) (by decide)
theorem pk_505 : ¬ Nat.Prime ((505+1)^(Nat.totient (1408-505)/2) - 505) := refute_e 505 252 3 (by decide) (by decide)
theorem pk_506 : ¬ Nat.Prime ((506+1)^(Nat.totient (1408-506)/2) - 506) := refute_e 506 200 5 (by decide) (by decide)
theorem pk_507 : ¬ Nat.Prime ((507+1)^(Nat.totient (1408-507)/2) - 507) := refute_e 507 416 37 (by decide) (by decide)
theorem pk_508 : ¬ Nat.Prime ((508+1)^(Nat.totient (1408-508)/2) - 508) := refute_e 508 120 3 (by decide) (by decide)
theorem pk_509 : ¬ Nat.Prime ((509+1)^(Nat.totient (1408-509)/2) - 509) := refute_e 509 420 67 (by decide) (by decide)
theorem pk_510 : ¬ Nat.Prime ((510+1)^(Nat.totient (1408-510)/2) - 510) := refute_e 510 224 13 (by decide) (by decide)
theorem pk_511 : ¬ Nat.Prime ((511+1)^(Nat.totient (1408-511)/2) - 511) := refute_e 511 264 3 (by decide) (by decide)
theorem pk_512 : ¬ Nat.Prime ((512+1)^(Nat.totient (1408-512)/2) - 512) := refute_e 512 192 7 (by decide) (by decide)
theorem pk_513 : ¬ Nat.Prime ((513+1)^(Nat.totient (1408-513)/2) - 513) := refute_e 513 356 7 (by decide) (by decide)
theorem pk_514 : ¬ Nat.Prime ((514+1)^(Nat.totient (1408-514)/2) - 514) := refute_e 514 148 3 (by decide) (by decide)
theorem pk_515 : ¬ Nat.Prime ((515+1)^(Nat.totient (1408-515)/2) - 515) := refute_e 515 414 23 (by decide) (by decide)
theorem pk_516 : ¬ Nat.Prime ((516+1)^(Nat.totient (1408-516)/2) - 516) := refute_e 516 222 5507 (by decide) (by decide)
theorem pk_517 : ¬ Nat.Prime ((517+1)^(Nat.totient (1408-517)/2) - 517) := refute_e 517 270 3 (by decide) (by decide)
theorem pk_518 : ¬ Nat.Prime ((518+1)^(Nat.totient (1408-518)/2) - 518) := refute_e 518 176 19 (by decide) (by decide)
theorem pk_519 : ¬ Nat.Prime ((519+1)^(Nat.totient (1408-519)/2) - 519) := refute_e 519 378 7 (by decide) (by decide)
theorem pk_520 : ¬ Nat.Prime ((520+1)^(Nat.totient (1408-520)/2) - 520) := refute_e 520 144 3 (by decide) (by decide)
theorem pk_521 : ¬ Nat.Prime ((521+1)^(Nat.totient (1408-521)/2) - 521) := refute_e 521 443 11 (by decide) (by decide)
theorem pk_522 : ¬ Nat.Prime ((522+1)^(Nat.totient (1408-522)/2) - 522) := refute_e 522 221 197 (by decide) (by decide)
theorem pk_523 : ¬ Nat.Prime ((523+1)^(Nat.totient (1408-523)/2) - 523) := refute_e 523 232 3 (by decide) (by decide)
theorem pk_524 : ¬ Nat.Prime ((524+1)^(Nat.totient (1408-524)/2) - 524) := refute_e 524 192 9991387131487 (by decide) (by decide)
theorem pk_525 : ¬ Nat.Prime ((525+1)^(Nat.totient (1408-525)/2) - 525) := refute_e 525 441 13 (by decide) (by decide)
theorem pk_526 : ¬ Nat.Prime ((526+1)^(Nat.totient (1408-526)/2) - 526) := refute_e 526 126 3 (by decide) (by decide)
theorem pk_527 : ¬ Nat.Prime ((527+1)^(Nat.totient (1408-527)/2) - 527) := refute_e 527 440 7 (by decide) (by decide)
theorem pk_528 : ¬ Nat.Prime ((528+1)^(Nat.totient (1408-528)/2) - 528) := refute_e 528 160 17 (by decide) (by decide)
theorem pk_529 : ¬ Nat.Prime ((529+1)^(Nat.totient (1408-529)/2) - 529) := refute_e 529 292 3 (by decide) (by decide)
theorem pk_530 : ¬ Nat.Prime ((530+1)^(Nat.totient (1408-530)/2) - 530) := refute_e 530 219 29761 (by decide) (by decide)
theorem pk_531 : ¬ Nat.Prime ((531+1)^(Nat.totient (1408-531)/2) - 531) := refute_e 531 438 577 (by decide) (by decide)
theorem pk_532 : ¬ Nat.Prime ((532+1)^(Nat.totient (1408-532)/2) - 532) := refute_e 532 144 3 (by decide) (by decide)
theorem pk_533 : ¬ Nat.Prime ((533+1)^(Nat.totient (1408-533)/2) - 533) := refute_e 533 300 7 (by decide) (by decide)
theorem pk_534 : ¬ Nat.Prime ((534+1)^(Nat.totient (1408-534)/2) - 534) := refute_e 534 198 3337133 (by decide) (by decide)
theorem pk_535 : ¬ Nat.Prime ((535+1)^(Nat.totient (1408-535)/2) - 535) := refute_e 535 288 3 (by decide) (by decide)
theorem pk_536 : ¬ Nat.Prime ((536+1)^(Nat.totient (1408-536)/2) - 536) := refute_e 536 216 5 (by decide) (by decide)
theorem pk_537 : ¬ Nat.Prime ((537+1)^(Nat.totient (1408-537)/2) - 537) := refute_e 537 396 67 (by decide) (by decide)
theorem pk_538 : ¬ Nat.Prime ((538+1)^(Nat.totient (1408-538)/2) - 538) := refute_e 538 112 3 (by decide) (by decide)
theorem pk_539 : ¬ Nat.Prime ((539+1)^(Nat.totient (1408-539)/2) - 539) := refute_e 539 390 313333 (by decide) (by decide)
theorem pk_540 : ¬ Nat.Prime ((540+1)^(Nat.totient (1408-540)/2) - 540) := refute_e 540 180 7 (by decide) (by decide)
theorem pk_541 : ¬ Nat.Prime ((541+1)^(Nat.totient (1408-541)/2) - 541) := refute_e 541 272 3 (by decide) (by decide)
theorem pk_542 : ¬ Nat.Prime ((542+1)^(Nat.totient (1408-542)/2) - 542) := refute_e 542 216 149 (by decide) (by decide)
theorem pk_543 : ¬ Nat.Prime ((543+1)^(Nat.totient (1408-543)/2) - 543) := refute_e 543 344 7 (by decide) (by decide)
theorem pk_544 : ¬ Nat.Prime ((544+1)^(Nat.totient (1408-544)/2) - 544) := refute_e 544 144 3 (by decide) (by decide)
theorem pk_545 : ¬ Nat.Prime ((545+1)^(Nat.totient (1408-545)/2) - 545) := refute_e 545 431 107 (by decide) (by decide)
theorem pk_546 : ¬ Nat.Prime ((546+1)^(Nat.totient (1408-546)/2) - 546) := refute_e 546 215 19 (by decide) (by decide)
theorem pk_547 : ¬ Nat.Prime ((547+1)^(Nat.totient (1408-547)/2) - 547) := refute_e 547 240 3 (by decide) (by decide)
theorem pk_548 : ¬ Nat.Prime ((548+1)^(Nat.totient (1408-548)/2) - 548) := refute_e 548 168 25839721 (by decide) (by decide)
theorem pk_549 : ¬ Nat.Prime ((549+1)^(Nat.totient (1408-549)/2) - 549) := refute_e 549 429 503 (by decide) (by decide)
theorem pk_550 : ¬ Nat.Prime ((550+1)^(Nat.totient (1408-550)/2) - 550) := refute_e 550 120 3 (by decide) (by decide)
theorem pk_551 : ¬ Nat.Prime ((551+1)^(Nat.totient (1408-551)/2) - 551) := refute_e 551 428 5 (by decide) (by decide)
theorem pk_552 : ¬ Nat.Prime ((552+1)^(Nat.totient (1408-552)/2) - 552) := refute_e 552 212 31 (by decide) (by decide)
theorem pk_553 : ¬ Nat.Prime ((553+1)^(Nat.totient (1408-553)/2) - 553) := refute_e 553 216 3 (by decide) (by decide)
theorem pk_554 : ¬ Nat.Prime ((554+1)^(Nat.totient (1408-554)/2) - 554) := refute_e 554 180 7 (by decide) (by decide)
theorem pk_555 : ¬ Nat.Prime ((555+1)^(Nat.totient (1408-555)/2) - 555) := refute_e 555 426 11 (by decide) (by decide)
theorem pk_556 : ¬ Nat.Prime ((556+1)^(Nat.totient (1408-556)/2) - 556) := refute_e 556 140 3 (by decide) (by decide)
theorem pk_557 : ¬ Nat.Prime ((557+1)^(Nat.totient (1408-557)/2) - 557) := refute_e 557 396 881 (by decide) (by decide)
theorem pk_558 : ¬ Nat.Prime ((558+1)^(Nat.totient (1408-558)/2) - 558) := refute_e 558 160 113 (by decide) (by decide)
theorem pk_559 : ¬ Nat.Prime ((559+1)^(Nat.totient (1408-559)/2) - 559) := refute_e 559 282 3 (by decide) (by decide)
theorem pk_560 : ¬ Nat.Prime ((560+1)^(Nat.totient (1408-560)/2) - 560) := refute_e 560 208 19 (by decide) (by decide)
theorem pk_561 : ¬ Nat.Prime ((561+1)^(Nat.totient (1408-561)/2) - 561) := refute_e 561 330 7 (by decide) (by decide)
theorem pk_562 : ¬ Nat.Prime ((562+1)^(Nat.totient (1408-562)/2) - 562) := refute_e 562 138 3 (by decide) (by decide)
theorem pk_563 : ¬ Nat.Prime ((563+1)^(Nat.totient (1408-563)/2) - 563) := refute_e 563 312 359 (by decide) (by decide)
theorem pk_564 : ¬ Nat.Prime ((564+1)^(Nat.totient (1408-564)/2) - 564) := refute_e 564 210 4231 (by decide) (by decide)
theorem pk_565 : ¬ Nat.Prime ((565+1)^(Nat.totient (1408-565)/2) - 565) := refute_e 565 280 3 (by decide) (by decide)
theorem pk_566 : ¬ Nat.Prime ((566+1)^(Nat.totient (1408-566)/2) - 566) := refute_e 566 210 55487 (by decide) (by decide)
theorem pk_567 : ¬ Nat.Prime ((567+1)^(Nat.totient (1408-567)/2) - 567) := refute_e 567 406 164778053689 (by decide) (by decide)
theorem pk_568 : ¬ Nat.Prime ((568+1)^(Nat.totient (1408-568)/2) - 568) := refute_e 568 96 3 (by decide) (by decide)
theorem pk_569 : ¬ Nat.Prime ((569+1)^(Nat.totient (1408-569)/2) - 569) := refute_e 569 419 117133 (by decide) (by decide)
theorem pk_570 : ¬ Nat.Prime ((570+1)^(Nat.totient (1408-570)/2) - 570) := refute_e 570 209 31 (by decide) (by decide)
theorem pk_571 : ¬ Nat.Prime ((571+1)^(Nat.totient (1408-571)/2) - 571) := refute_e 571 270 3 (by decide) (by decide)
theorem pk_572 : ¬ Nat.Prime ((572+1)^(Nat.totient (1408-572)/2) - 572) := refute_e 572 180 2473 (by decide) (by decide)
theorem pk_573 : ¬ Nat.Prime ((573+1)^(Nat.totient (1408-573)/2) - 573) := refute_e 573 332 67 (by decide) (by decide)
theorem pk_574 : ¬ Nat.Prime ((574+1)^(Nat.totient (1408-574)/2) - 574) := refute_e 574 138 3 (by decide) (by decide)
theorem pk_575 : ¬ Nat.Prime ((575+1)^(Nat.totient (1408-575)/2) - 575) := refute_e 575 336 7 (by decide) (by decide)
theorem pk_576 : ¬ Nat.Prime ((576+1)^(Nat.totient (1408-576)/2) - 576) := refute_e 576 192 5 (by decide) (by decide)
theorem pk_577 : ¬ Nat.Prime ((577+1)^(Nat.totient (1408-577)/2) - 577) := refute_e 577 276 3 (by decide) (by decide)
theorem pk_578 : ¬ Nat.Prime ((578+1)^(Nat.totient (1408-578)/2) - 578) := refute_e 578 164 7 (by decide) (by decide)
theorem pk_579 : ¬ Nat.Prime ((579+1)^(Nat.totient (1408-579)/2) - 579) := refute_e 579 414 157 (by decide) (by decide)
theorem pk_580 : ¬ Nat.Prime ((580+1)^(Nat.totient (1408-580)/2) - 580) := refute_e 580 132 3 (by decide) (by decide)
theorem pk_581 : ¬ Nat.Prime ((581+1)^(Nat.totient (1408-581)/2) - 581) := refute_e 581 413 983 (by decide) (by decide)
theorem pk_582 : ¬ Nat.Prime ((582+1)^(Nat.totient (1408-582)/2) - 582) := refute_e 582 174 7 (by decide) (by decide)
theorem pk_583 : ¬ Nat.Prime ((583+1)^(Nat.totient (1408-583)/2) - 583) := refute_e 583 200 3 (by decide) (by decide)
theorem pk_584 : ¬ Nat.Prime ((584+1)^(Nat.totient (1408-584)/2) - 584) := refute_e 584 204 220174029260221 (by decide) (by decide)
theorem pk_585 : ¬ Nat.Prime ((585+1)^(Nat.totient (1408-585)/2) - 585) := refute_e 585 411 23 (by decide) (by decide)
theorem pk_586 : ¬ Nat.Prime ((586+1)^(Nat.totient (1408-586)/2) - 586) := refute_e 586 136 3 (by decide) (by decide)
theorem pk_587 : ¬ Nat.Prime ((587+1)^(Nat.totient (1408-587)/2) - 587) := refute_e 587 410 23 (by decide) (by decide)
theorem pk_588 : ¬ Nat.Prime ((588+1)^(Nat.totient (1408-588)/2) - 588) := refute_e 588 160 37 (by decide) (by decide)
theorem pk_589 : ¬ Nat.Prime ((589+1)^(Nat.totient (1408-589)/2) - 589) := refute_e 589 216 3 (by decide) (by decide)
theorem pk_590 : ¬ Nat.Prime ((590+1)^(Nat.totient (1408-590)/2) - 590) := refute_e 590 204 2431329877 (by decide) (by decide)
theorem pk_591 : ¬ Nat.Prime ((591+1)^(Nat.totient (1408-591)/2) - 591) := refute_e 591 378 509 (by decide) (by decide)
theorem pk_592 : ¬ Nat.Prime ((592+1)^(Nat.totient (1408-592)/2) - 592) := refute_e 592 128 3 (by decide) (by decide)
theorem pk_593 : ¬ Nat.Prime ((593+1)^(Nat.totient (1408-593)/2) - 593) := refute_e 593 324 37 (by decide) (by decide)
theorem pk_594 : ¬ Nat.Prime ((594+1)^(Nat.totient (1408-594)/2) - 594) := refute_e 594 180 233 (by decide) (by decide)
theorem pk_595 : ¬ Nat.Prime ((595+1)^(Nat.totient (1408-595)/2) - 595) := refute_e 595 270 3 (by decide) (by decide)
theorem pk_596 : ¬ Nat.Prime ((596+1)^(Nat.totient (1408-596)/2) - 596) := refute_e 596 168 5 (by decide) (by decide)
theorem pk_597 : ¬ Nat.Prime ((597+1)^(Nat.totient (1408-597)/2) - 597) := refute_e 597 405 11731 (by decide) (by decide)
theorem pk_598 : ¬ Nat.Prime ((598+1)^(Nat.totient (1408-598)/2) - 598) := refute_e 598 108 3 (by decide) (by decide)
theorem pk_599 : ¬ Nat.Prime ((599+1)^(Nat.totient (1408-599)/2) - 599) := refute_e 599 404 7 (by decide) (by decide)
theorem pk_600 : ¬ Nat.Prime ((600+1)^(Nat.totient (1408-600)/2) - 600) := refute_e 600 200 19 (by decide) (by decide)
theorem pk_601 : ¬ Nat.Prime ((601+1)^(Nat.totient (1408-601)/2) - 601) := refute_e 601 268 3 (by decide) (by decide)
theorem pk_602 : ¬ Nat.Prime ((602+1)^(Nat.totient (1408-602)/2) - 602) := refute_e 602 180 23 (by decide) (by decide)
theorem pk_603 : ¬ Nat.Prime ((603+1)^(Nat.totient (1408-603)/2) - 603) := refute_e 603 264 7 (by decide) (by decide)
theorem pk_604 : ¬ Nat.Prime ((604+1)^(Nat.totient (1408-604)/2) - 604) := refute_e 604 132 3 (by decide) (by decide)
theorem pk_605 : ¬ Nat.Prime ((605+1)^(Nat.totient (1408-605)/2) - 605) := refute_e 605 360 151 (by decide) (by decide)
theorem pk_606 : ¬ Nat.Prime ((606+1)^(Nat.totient (1408-606)/2) - 606) := refute_e 606 200 5 (by decide) (by decide)
theorem pk_607 : ¬ Nat.Prime ((607+1)^(Nat.totient (1408-607)/2) - 607) := refute_e 607 264 3 (by decide) (by decide)
theorem pk_608 : ¬ Nat.Prime ((608+1)^(Nat.totient (1408-608)/2) - 608) := refute_e 608 160 37 (by decide) (by decide)
theorem pk_609 : ¬ Nat.Prime ((609+1)^(Nat.totient (1408-609)/2) - 609) := refute_e 609 368 11 (by decide) (by decide)
theorem pk_610 : ¬ Nat.Prime ((610+1)^(Nat.totient (1408-610)/2) - 610) := refute_e 610 108 3 (by decide) (by decide)
theorem pk_611 : ¬ Nat.Prime ((611+1)^(Nat.totient (1408-611)/2) - 611) := refute_e 611 398 7 (by decide) (by decide)
theorem pk_612 : ¬ Nat.Prime ((612+1)^(Nat.totient (1408-612)/2) - 612) := refute_e 612 198 5527 (by decide) (by decide)
theorem pk_613 : ¬ Nat.Prime ((613+1)^(Nat.totient (1408-613)/2) - 613) := refute_e 613 208 3 (by decide) (by decide)
theorem pk_614 : ¬ Nat.Prime ((614+1)^(Nat.totient (1408-614)/2) - 614) := refute_e 614 198 875136707533303 (by decide) (by decide)
theorem pk_615 : ¬ Nat.Prime ((615+1)^(Nat.totient (1408-615)/2) - 615) := refute_e 615 360 197 (by decide) (by decide)
theorem pk_616 : ¬ Nat.Prime ((616+1)^(Nat.totient (1408-616)/2) - 616) := refute_e 616 120 3 (by decide) (by decide)
theorem pk_617 : ¬ Nat.Prime ((617+1)^(Nat.totient (1408-617)/2) - 617) := refute_e 617 336 7 (by decide) (by decide)
theorem pk_618 : ¬ Nat.Prime ((618+1)^(Nat.totient (1408-618)/2) - 618) := refute_e 618 156 269 (by decide) (by decide)
theorem pk_619 : ¬ Nat.Prime ((619+1)^(Nat.totient (1408-619)/2) - 619) := refute_e 619 262 3 (by decide) (by decide)
theorem pk_620 : ¬ Nat.Prime ((620+1)^(Nat.totient (1408-620)/2) - 620) := refute_e 620 196 139 (by decide) (by decide)
theorem pk_621 : ¬ Nat.Prime ((621+1)^(Nat.totient (1408-621)/2) - 621) := refute_fermat 621 393 828285108688786698165058898674162329072485650017267606437734068087106771682894681553158441693464528092634367864583390025997946836668499510922027934599465491598072338891113082324650594875369739192993116601859120257967357639523844209648310436576377961565346602849198774800726960064640892063088051212389115355151321890716315897435730154378118944403792964767901692491795955302748816855597291227323298288554831035947270288596490462424474385409873523633758313592885981551243077495838627627656885147939595327803843796226392694152741019610248558397377635181689955480914907734253084801902942595325481086051820582354776452986924277811652825724180339125791043762049469656033474362341246825748746800845005884707263643426480268868201111852708743034205294735374686751327386503009058779167197113436823582179198884311506076357293102518916198359938456507494676669796288715189017943957828349696177934578251561895228771977668882196064265811532503973577500419116963903823091225794721234331371169327966987701554632761122479406380490235540673767069746445749592706548015378173515550785718986966658952042053941534531828986 (by decide) (by norm_num) (by norm_num) (by norm_num) (by decide) (by reduce_mod_char)
theorem pk_622 : ¬ Nat.Prime ((622+1)^(Nat.totient (1408-622)/2) - 622) := refute_e 622 130 3 (by decide) (by decide)
theorem pk_623 : ¬ Nat.Prime ((623+1)^(Nat.totient (1408-623)/2) - 623) := refute_fermat 623 312 32753508995401242458657723316178133719270472188197474087727093125258832420839067612125583144456693905742973932362934420702946103047333965947232663390544478372336850623671715616531442042357097474224086209955340105390432908741598377783168811485955344282310626607813561974341114500471104338624222950730178016644100453798552820166187315751494932217542417642462134963073934572279704912877249519932422284017593879594200883833280362185648259822255350517471805545095097753687843199240915260366318523833850799269010230089826153845625296339342093557557962628029067508329335105687845174274258959096389982544657343556093578749176218644380717946080056057955406822970049817621168978027113550765453190488618960077686585805329876694984367707991421349021844740685900113537627513896025432978107913386013014641351222990448141894623515627728442971197450664352171928958573241087691125169316619 (by decide) (by norm_num) (by norm_num) (by norm_num) (by decide) (by reduce_mod_char)
theorem pk_624 : ¬ Nat.Prime ((624+1)^(Nat.totient (1408-624)/2) - 624) := refute_e 624 168 7 (by decide) (by decide)
theorem pk_625 : ¬ Nat.Prime ((625+1)^(Nat.totient (1408-625)/2) - 625) := refute_e 625 252 3 (by decide) (by decide)
theorem pk_626 : ¬ Nat.Prime ((626+1)^(Nat.totient (1408-626)/2) - 626) := refute_e 626 176 5 (by decide) (by decide)
theorem pk_627 : ¬ Nat.Prime ((627+1)^(Nat.totient (1408-627)/2) - 627) := refute_e 627 350 7 (by decide) (by decide)
theorem pk_628 : ¬ Nat.Prime ((628+1)^(Nat.totient (1408-628)/2) - 628) := refute_e 628 96 3 (by decide) (by decide)
theorem pk_629 : ¬ Nat.Prime ((629+1)^(Nat.totient (1408-629)/2) - 629) := refute_e 629 360 1213 (by decide) (by decide)
theorem pk_630 : ¬ Nat.Prime ((630+1)^(Nat.totient (1408-630)/2) - 630) := refute_e 630 194 11 (by decide) (by decide)
theorem pk_631 : ¬ Nat.Prime ((631+1)^(Nat.totient (1408-631)/2) - 631) := refute_e 631 216 3 (by decide) (by decide)
theorem pk_632 : ¬ Nat.Prime ((632+1)^(Nat.totient (1408-632)/2) - 632) := refute_e 632 192 53824369 (by decide) (by decide)
theorem pk_633 : ¬ Nat.Prime ((633+1)^(Nat.totient (1408-633)/2) - 633) := refute_e 633 300 17 (by decide) (by decide)
theorem pk_634 : ¬ Nat.Prime ((634+1)^(Nat.totient (1408-634)/2) - 634) := refute_e 634 126 3 (by decide) (by decide)
theorem pk_635 : ¬ Nat.Prime ((635+1)^(Nat.totient (1408-635)/2) - 635) := refute_e 635 386 103 (by decide) (by decide)
theorem pk_636 : ¬ Nat.Prime ((636+1)^(Nat.totient (1408-636)/2) - 636) := refute_e 636 192 5 (by decide) (by decide)
theorem pk_637 : ¬ Nat.Prime ((637+1)^(Nat.totient (1408-637)/2) - 637) := refute_e 637 256 3 (by decide) (by decide)
theorem pk_638 : ¬ Nat.Prime ((638+1)^(Nat.totient (1408-638)/2) - 638) := refute_e 638 120 7 (by decide) (by decide)
theorem pk_639 : ¬ Nat.Prime ((639+1)^(Nat.totient (1408-639)/2) - 639) := refute_e 639 384 127 (by decide) (by decide)
theorem pk_640 : ¬ Nat.Prime ((640+1)^(Nat.totient (1408-640)/2) - 640) := refute_e 640 128 3 (by decide) (by decide)
theorem pk_641 : ¬ Nat.Prime ((641+1)^(Nat.totient (1408-641)/2) - 641) := refute_e 641 348 5 (by decide) (by decide)
theorem pk_642 : ¬ Nat.Prime ((642+1)^(Nat.totient (1408-642)/2) - 642) := refute_e 642 191 5 (by decide) (by decide)
theorem pk_643 : ¬ Nat.Prime ((643+1)^(Nat.totient (1408-643)/2) - 643) := refute_e 643 192 3 (by decide) (by decide)
theorem pk_644 : ¬ Nat.Prime ((644+1)^(Nat.totient (1408-644)/2) - 644) := refute_e 644 190 1027547 (by decide) (by decide)
theorem pk_645 : ¬ Nat.Prime ((645+1)^(Nat.totient (1408-645)/2) - 645) := refute_e 645 324 7 (by decide) (by decide)
theorem pk_646 : ¬ Nat.Prime ((646+1)^(Nat.totient (1408-646)/2) - 646) := refute_e 646 126 3 (by decide) (by decide)
theorem pk_647 : ¬ Nat.Prime ((647+1)^(Nat.totient (1408-647)/2) - 647) := refute_e 647 380 211 (by decide) (by decide)
theorem pk_648 : ¬ Nat.Prime ((648+1)^(Nat.totient (1408-648)/2) - 648) := refute_e 648 144 1249 (by decide) (by decide)
theorem pk_649 : ¬ Nat.Prime ((649+1)^(Nat.totient (1408-649)/2) - 649) := refute_e 649 220 3 (by decide) (by decide)
theorem pk_650 : ¬ Nat.Prime ((650+1)^(Nat.totient (1408-650)/2) - 650) := refute_e 650 189 20231 (by decide) (by decide)
theorem pk_651 : ¬ Nat.Prime ((651+1)^(Nat.totient (1408-651)/2) - 651) := refute_e 651 378 173 (by decide) (by decide)
theorem pk_652 : ¬ Nat.Prime ((652+1)^(Nat.totient (1408-652)/2) - 652) := refute_e 652 108 3 (by decide) (by decide)
theorem pk_653 : ¬ Nat.Prime ((653+1)^(Nat.totient (1408-653)/2) - 653) := refute_e 653 300 59 (by decide) (by decide)
theorem pk_654 : ¬ Nat.Prime ((654+1)^(Nat.totient (1408-654)/2) - 654) := refute_e 654 168 641 (by decide) (by decide)
theorem pk_655 : ¬ Nat.Prime ((655+1)^(Nat.totient (1408-655)/2) - 655) := refute_e 655 250 3 (by decide) (by decide)
theorem pk_656 : ¬ Nat.Prime ((656+1)^(Nat.totient (1408-656)/2) - 656) := refute_e 656 184 5 (by decide) (by decide)
theorem pk_657 : ¬ Nat.Prime ((657+1)^(Nat.totient (1408-657)/2) - 657) := refute_e 657 375 5 (by decide) (by decide)
theorem pk_658 : ¬ Nat.Prime ((658+1)^(Nat.totient (1408-658)/2) - 658) := refute_e 658 100 3 (by decide) (by decide)
theorem pk_659 : ¬ Nat.Prime ((659+1)^(Nat.totient (1408-659)/2) - 659) := refute_e 659 318 7 (by decide) (by decide)
theorem pk_660 : ¬ Nat.Prime ((660+1)^(Nat.totient (1408-660)/2) - 660) := refute_e 660 160 967 (by decide) (by decide)
theorem pk_661 : ¬ Nat.Prime ((661+1)^(Nat.totient (1408-661)/2) - 661) := refute_e 661 246 3 (by decide) (by decide)
theorem pk_662 : ¬ Nat.Prime ((662+1)^(Nat.totient (1408-662)/2) - 662) := refute_e 662 186 29 (by decide) (by decide)
theorem pk_663 : ¬ Nat.Prime ((663+1)^(Nat.totient (1408-663)/2) - 663) := refute_e 663 296 37 (by decide) (by decide)
theorem pk_664 : ¬ Nat.Prime ((664+1)^(Nat.totient (1408-664)/2) - 664) := refute_e 664 120 3 (by decide) (by decide)
theorem pk_665 : ¬ Nat.Prime ((665+1)^(Nat.totient (1408-665)/2) - 665) := refute_fermat 665 371 954143987574337544712419828855147622781948856173855137227495057212481064189700067277837584136292177141928174464697026667240967983292032145025730987262326821578717179222952235836070345670872415664854157619525606210176664547800279849894109868207681636188018521510272253594359382911143401820080261924008155835982434768364628291562869895023962130374587909442212565662554686347468141928946093261974593352781325444694422227949894718966218907918180214891898149232480496295616179466018171093287262326080855024944712132175018350274408635299893984686135709358289812965534606380490125539996278874582641582860846317864032706803907326632874585888961738421471079612496244421982631538183291090682371403729028449660981536810488375092855592381643306564029877598240251305412625869348582771740273514998945407511374865475832642476303750038719886108947881738434144564969453960992396778369791204496015664165303010681926423791782945556535899658246738438956235443867560610171287636614285301397805485553017935668711083070581254846913494628423519207726617893383112790866208 (by decide) (by norm_num) (by norm_num) (by norm_num) (by decide) (by reduce_mod_char)
theorem pk_666 : ¬ Nat.Prime ((666+1)^(Nat.totient (1408-666)/2) - 666) := refute_e 666 156 5 (by decide) (by decide)
theorem pk_667 : ¬ Nat.Prime ((667+1)^(Nat.totient (1408-667)/2) - 667) := refute_e 667 216 3 (by decide) (by decide)
theorem pk_668 : ¬ Nat.Prime ((668+1)^(Nat.totient (1408-668)/2) - 668) := refute_e 668 144 65003 (by decide) (by decide)
theorem pk_669 : ¬ Nat.Prime ((669+1)^(Nat.totient (1408-669)/2) - 669) := refute_e 669 369 2633 (by decide) (by decide)
theorem pk_670 : ¬ Nat.Prime ((670+1)^(Nat.totient (1408-670)/2) - 670) := refute_e 670 120 3 (by decide) (by decide)
theorem pk_671 : ¬ Nat.Prime ((671+1)^(Nat.totient (1408-671)/2) - 671) := refute_e 671 330 67 (by decide) (by decide)
theorem pk_672 : ¬ Nat.Prime ((672+1)^(Nat.totient (1408-672)/2) - 672) := refute_e 672 176 13 (by decide) (by decide)
theorem pk_673 : ¬ Nat.Prime ((673+1)^(Nat.totient (1408-673)/2) - 673) := refute_e 673 168 3 (by decide) (by decide)
theorem pk_674 : ¬ Nat.Prime ((674+1)^(Nat.totient (1408-674)/2) - 674) := refute_e 674 183 61 (by decide) (by decide)
theorem pk_675 : ¬ Nat.Prime ((675+1)^(Nat.totient (1408-675)/2) - 675) := refute_e 675 366 83 (by decide) (by decide)
theorem pk_676 : ¬ Nat.Prime ((676+1)^(Nat.totient (1408-676)/2) - 676) := refute_e 676 120 3 (by decide) (by decide)
theorem pk_677 : ¬ Nat.Prime ((677+1)^(Nat.totient (1408-677)/2) - 677) := refute_e 677 336 13 (by decide) (by decide)
theorem pk_678 : ¬ Nat.Prime ((678+1)^(Nat.totient (1408-678)/2) - 678) := refute_e 678 144 49633 (by decide) (by decide)
theorem pk_679 : ¬ Nat.Prime ((679+1)^(Nat.totient (1408-679)/2) - 679) := refute_e 679 243 3739 (by decide) (by decide)
theorem pk_680 : ¬ Nat.Prime ((680+1)^(Nat.totient (1408-680)/2) - 680) := refute_e 680 144 7 (by decide) (by decide)
theorem pk_681 : ¬ Nat.Prime ((681+1)^(Nat.totient (1408-681)/2) - 681) := refute_e 681 363 1657 (by decide) (by decide)
theorem pk_682 : ¬ Nat.Prime ((682+1)^(Nat.totient (1408-682)/2) - 682) := refute_e 682 110 3 (by decide) (by decide)
theorem pk_683 : ¬ Nat.Prime ((683+1)^(Nat.totient (1408-683)/2) - 683) := refute_e 683 280 11 (by decide) (by decide)
theorem pk_684 : ¬ Nat.Prime ((684+1)^(Nat.totient (1408-684)/2) - 684) := refute_e 684 180 353 (by decide) (by decide)
theorem pk_685 : ¬ Nat.Prime ((685+1)^(Nat.totient (1408-685)/2) - 685) := refute_e 685 240 3 (by decide) (by decide)
theorem pk_686 : ¬ Nat.Prime ((686+1)^(Nat.totient (1408-686)/2) - 686) := refute_e 686 171 8480101831221593587555037690681150088635996746650662222954952167515196943695521337314605064757933803187483751223495308897826982501751804273789371516132929885818056938469341513911548286380617835981622241693351667390058668654817843419146859871985488439110549897802332455250347464008848495505304449743180100637472598538638964519998686998567544739936240289521209162425421828147157469133384201697244157193860651550711336769377048624543260721040776127463567931841478297351 (by decide) (by decide)
theorem pk_687 : ¬ Nat.Prime ((687+1)^(Nat.totient (1408-687)/2) - 687) := refute_e 687 306 7 (by decide) (by decide)
theorem pk_688 : ¬ Nat.Prime ((688+1)^(Nat.totient (1408-688)/2) - 688) := refute_e 688 96 3 (by decide) (by decide)
theorem pk_689 : ¬ Nat.Prime ((689+1)^(Nat.totient (1408-689)/2) - 689) := refute_e 689 359 11 (by decide) (by decide)
theorem pk_690 : ¬ Nat.Prime ((690+1)^(Nat.totient (1408-690)/2) - 690) := refute_e 690 179 127 (by decide) (by decide)
theorem pk_691 : ¬ Nat.Prime ((691+1)^(Nat.totient (1408-691)/2) - 691) := refute_e 691 238 3 (by decide) (by decide)
theorem pk_692 : ¬ Nat.Prime ((692+1)^(Nat.totient (1408-692)/2) - 692) := refute_e 692 178 31 (by decide) (by decide)
theorem pk_693 : ¬ Nat.Prime ((693+1)^(Nat.totient (1408-693)/2) - 693) := refute_e 693 240 17675830619209207 (by decide) (by decide)
theorem pk_694 : ¬ Nat.Prime ((694+1)^(Nat.totient (1408-694)/2) - 694) := refute_e 694 96 3 (by decide) (by decide)
theorem pk_695 : ¬ Nat.Prime ((695+1)^(Nat.totient (1408-695)/2) - 695) := refute_e 695 330 2285367971 (by decide) (by decide)
theorem pk_696 : ¬ Nat.Prime ((696+1)^(Nat.totient (1408-696)/2) - 696) := refute_e 696 176 5 (by decide) (by decide)
theorem pk_697 : ¬ Nat.Prime ((697+1)^(Nat.totient (1408-697)/2) - 697) := refute_e 697 234 3 (by decide) (by decide)
theorem pk_698 : ¬ Nat.Prime ((698+1)^(Nat.totient (1408-698)/2) - 698) := refute_e 698 140 13 (by decide) (by decide)
theorem pk_699 : ¬ Nat.Prime ((699+1)^(Nat.totient (1408-699)/2) - 699) := refute_e 699 354 71 (by decide) (by decide)
theorem pk_700 : ¬ Nat.Prime ((700+1)^(Nat.totient (1408-700)/2) - 700) := refute_e 700 116 3 (by decide) (by decide)
theorem pk_701 : ¬ Nat.Prime ((701+1)^(Nat.totient (1408-701)/2) - 701) := refute_e 701 300 5 (by decide) (by decide)
theorem pk_702 : ¬ Nat.Prime ((702+1)^(Nat.totient (1408-702)/2) - 702) := refute_e 702 176 7 (by decide) (by decide)
theorem pk_703 : ¬ Nat.Prime ((703+1)^(Nat.totient (1408-703)/2) - 703) := refute_e 703 184 3 (by decide) (by decide)
theorem pk_704 : ¬ Nat.Prime ((704+1)^(Nat.totient (1408-704)/2) - 704) := refute_e 704 160 57091857692651921456752641318773077694397683059404190082527527467822733144694017451564658598930721644852343944514966129996831320241491244185589991230506921328073885972602294223741272683684966898303366825291530026465545576413391061316633822349815540822030176985588688010774698823647072006274356379421778331506658504544387989450695468894768492021849299555289935033219732871490959477321593636546625222967925339249210301908571853716686514398750428719 (by decide) (by decide)
theorem pk_705 : ¬ Nat.Prime ((705+1)^(Nat.totient (1408-705)/2) - 705) := refute_e 705 324 1699 (by decide) (by decide)
theorem pk_706 : ¬ Nat.Prime ((706+1)^(Nat.totient (1408-706)/2) - 706) := refute_e 706 108 3 (by decide) (by decide)
theorem pk_707 : ¬ Nat.Prime ((707+1)^(Nat.totient (1408-707)/2) - 707) := refute_e 707 350 19 (by decide) (by decide)
theorem pk_708 : ¬ Nat.Prime ((708+1)^(Nat.totient (1408-708)/2) - 708) := refute_e 708 120 7 (by decide) (by decide)
theorem pk_709 : ¬ Nat.Prime ((709+1)^(Nat.totient (1408-709)/2) - 709) := refute_e 709 232 3 (by decide) (by decide)
theorem pk_710 : ¬ Nat.Prime ((710+1)^(Nat.totient (1408-710)/2) - 710) := refute_e 710 174 521 (by decide) (by decide)
theorem pk_711 : ¬ Nat.Prime ((711+1)^(Nat.totient (1408-711)/2) - 711) := refute_e 711 320 5 (by decide) (by decide)
theorem pk_712 : ¬ Nat.Prime ((712+1)^(Nat.totient (1408-712)/2) - 712) := refute_e 712 112 3 (by decide) (by decide)
theorem pk_713 : ¬ Nat.Prime ((713+1)^(Nat.totient (1408-713)/2) - 713) := refute_e 713 276 367 (by decide) (by decide)
theorem pk_714 : ¬ Nat.Prime ((714+1)^(Nat.totient (1408-714)/2) - 714) := refute_e 714 173 83073589 (by decide) (by decide)
theorem pk_715 : ¬ Nat.Prime ((715+1)^(Nat.totient (1408-715)/2) - 715) := refute_e 715 180 3 (by decide) (by decide)
theorem pk_716 : ¬ Nat.Prime ((716+1)^(Nat.totient (1408-716)/2) - 716) := refute_e 716 172 5 (by decide) (by decide)
theorem pk_717 : ¬ Nat.Prime ((717+1)^(Nat.totient (1408-717)/2) - 717) := refute_e 717 345 125749039001743 (by decide) (by decide)
theorem pk_718 : ¬ Nat.Prime ((718+1)^(Nat.totient (1408-718)/2) - 718) := refute_e 718 88 3 (by decide) (by decide)
theorem pk_719 : ¬ Nat.Prime ((719+1)^(Nat.totient (1408-719)/2) - 719) := refute_e 719 312 252319 (by decide) (by decide)
theorem pk_720 : ¬ Nat.Prime ((720+1)^(Nat.totient (1408-720)/2) - 720) := refute_e 720 168 109 (by decide) (by decide)
theorem pk_721 : ¬ Nat.Prime ((721+1)^(Nat.totient (1408-721)/2) - 721) := refute_e 721 228 3 (by decide) (by decide)
theorem pk_722 : ¬ Nat.Prime ((722+1)^(Nat.totient (1408-722)/2) - 722) := refute_e 722 147 5 (by decide) (by decide)
theorem pk_723 : ¬ Nat.Prime ((723+1)^(Nat.totient (1408-723)/2) - 723) := refute_e 723 272 7 (by decide) (by decide)
theorem pk_724 : ¬ Nat.Prime ((724+1)^(Nat.totient (1408-724)/2) - 724) := refute_e 724 108 3 (by decide) (by decide)
theorem pk_725 : ¬ Nat.Prime ((725+1)^(Nat.totient (1408-725)/2) - 725) := refute_e 725 341 1321 (by decide) (by decide)
theorem pk_726 : ¬ Nat.Prime ((726+1)^(Nat.totient (1408-726)/2) - 726) := refute_e 726 150 97 (by decide) (by decide)
theorem pk_727 : ¬ Nat.Prime ((727+1)^(Nat.totient (1408-727)/2) - 727) := refute_e 727 226 3 (by decide) (by decide)
theorem pk_728 : ¬ Nat.Prime ((728+1)^(Nat.totient (1408-728)/2) - 728) := refute_e 728 128 89 (by decide) (by decide)
theorem pk_729 : ¬ Nat.Prime ((729+1)^(Nat.totient (1408-729)/2) - 729) := refute_e 729 288 7 (by decide) (by decide)
theorem pk_730 : ¬ Nat.Prime ((730+1)^(Nat.totient (1408-730)/2) - 730) := refute_e 730 112 3 (by decide) (by decide)
theorem pk_731 : ¬ Nat.Prime ((731+1)^(Nat.totient (1408-731)/2) - 731) := refute_e 731 338 13 (by decide) (by decide)
theorem pk_732 : ¬ Nat.Prime ((732+1)^(Nat.totient (1408-732)/2) - 732) := refute_e 732 156 67 (by decide) (by decide)
theorem pk_733 : ¬ Nat.Prime ((733+1)^(Nat.totient (1408-733)/2) - 733) := refute_e 733 180 3 (by decide) (by decide)
theorem pk_734 : ¬ Nat.Prime ((734+1)^(Nat.totient (1408-734)/2) - 734) := refute_e 734 168 807015961 (by decide) (by decide)
theorem pk_735 : ¬ Nat.Prime ((735+1)^(Nat.totient (1408-735)/2) - 735) := refute_e 735 336 455513 (by decide) (by decide)
theorem pk_736 : ¬ Nat.Prime ((736+1)^(Nat.totient (1408-736)/2) - 736) := refute_e 736 96 3 (by decide) (by decide)
theorem pk_737 : ¬ Nat.Prime ((737+1)^(Nat.totient (1408-737)/2) - 737) := refute_e 737 300 79138649 (by decide) (by decide)
theorem pk_738 : ¬ Nat.Prime ((738+1)^(Nat.totient (1408-738)/2) - 738) := refute_e 738 132 67 (by decide) (by decide)
theorem pk_739 : ¬ Nat.Prime ((739+1)^(Nat.totient (1408-739)/2) - 739) := refute_e 739 222 3 (by decide) (by decide)
theorem pk_740 : ¬ Nat.Prime ((740+1)^(Nat.totient (1408-740)/2) - 740) := refute_e 740 166 17 (by decide) (by decide)
theorem pk_741 : ¬ Nat.Prime ((741+1)^(Nat.totient (1408-741)/2) - 741) := refute_e 741 308 5 (by decide) (by decide)
theorem pk_742 : ¬ Nat.Prime ((742+1)^(Nat.totient (1408-742)/2) - 742) := refute_e 742 108 3 (by decide) (by decide)
theorem pk_743 : ¬ Nat.Prime ((743+1)^(Nat.totient (1408-743)/2) - 743) := refute_e 743 216 7 (by decide) (by decide)
theorem pk_744 : ¬ Nat.Prime ((744+1)^(Nat.totient (1408-744)/2) - 744) := refute_e 744 164 7 (by decide) (by decide)
theorem pk_745 : ¬ Nat.Prime ((745+1)^(Nat.totient (1408-745)/2) - 745) := refute_e 745 192 3 (by decide) (by decide)
theorem pk_746 : ¬ Nat.Prime ((746+1)^(Nat.totient (1408-746)/2) - 746) := refute_e 746 165 13 (by decide) (by decide)
theorem pk_747 : ¬ Nat.Prime ((747+1)^(Nat.totient (1408-747)/2) - 747) := refute_e 747 330 43 (by decide) (by decide)
theorem pk_748 : ¬ Nat.Prime ((748+1)^(Nat.totient (1408-748)/2) - 748) := refute_e 748 80 3 (by decide) (by decide)
theorem pk_749 : ¬ Nat.Prime ((749+1)^(Nat.totient (1408-749)/2) - 749) := refute_e 749 329 41 (by decide) (by decide)
theorem pk_750 : ¬ Nat.Prime ((750+1)^(Nat.totient (1408-750)/2) - 750) := refute_e 750 138 7 (by decide) (by decide)
theorem pk_751 : ¬ Nat.Prime ((751+1)^(Nat.totient (1408-751)/2) - 751) := refute_e 751 216 3 (by decide) (by decide)
theorem pk_752 : ¬ Nat.Prime ((752+1)^(Nat.totient (1408-752)/2) - 752) := refute_e 752 160 1083007 (by decide) (by decide)
theorem pk_753 : ¬ Nat.Prime ((753+1)^(Nat.totient (1408-753)/2) - 753) := refute_e 753 260 7 (by decide) (by decide)
theorem pk_754 : ¬ Nat.Prime ((754+1)^(Nat.totient (1408-754)/2) - 754) := refute_e 754 108 3 (by decide) (by decide)
theorem pk_755 : ¬ Nat.Prime ((755+1)^(Nat.totient (1408-755)/2) - 755) := refute_e 755 326 379 (by decide) (by decide)
theorem pk_756 : ¬ Nat.Prime ((756+1)^(Nat.totient (1408-756)/2) - 756) := refute_e 756 162 1601995309205306348920027114221154222017949139104050575983534446715214936186612381009704062448300136442041446252480832291471305682578159712575428806659865227035872537343952379487840117862293242162246288680918598964271177695409935523415811188752752444741534782369853400167110511589496161790560822913415647313488849827199087011220195863969584254683610184420340296535924440203572607383588265552753983337925588908620068331880235787981914260352071 (by decide) (by decide)
theorem pk_757 : ¬ Nat.Prime ((757+1)^(Nat.totient (1408-757)/2) - 757) := refute_e 757 180 3 (by decide) (by decide)
theorem pk_758 : ¬ Nat.Prime ((758+1)^(Nat.totient (1408-758)/2) - 758) := refute_e 758 120 53 (by decide) (by decide)
theorem pk_759 : ¬ Nat.Prime ((759+1)^(Nat.totient (1408-759)/2) - 759) := refute_e 759 290 53 (by decide) (by decide)
theorem pk_760 : ¬ Nat.Prime ((760+1)^(Nat.totient (1408-760)/2) - 760) := refute_e 760 108 3 (by decide) (by decide)
theorem pk_761 : ¬ Nat.Prime ((761+1)^(Nat.totient (1408-761)/2) - 761) := refute_e 761 323 1187 (by decide) (by decide)
theorem pk_762 : ¬ Nat.Prime ((762+1)^(Nat.totient (1408-762)/2) - 762) := refute_e 762 144 11 (by decide) (by decide)
theorem pk_763 : ¬ Nat.Prime ((763+1)^(Nat.totient (1408-763)/2) - 763) := refute_e 763 168 3 (by decide) (by decide)
theorem pk_764 : ¬ Nat.Prime ((764+1)^(Nat.totient (1408-764)/2) - 764) := refute_e 764 132 7 (by decide) (by decide)
theorem pk_765 : ¬ Nat.Prime ((765+1)^(Nat.totient (1408-765)/2) - 765) := refute_e 765 321 56009 (by decide) (by decide)
theorem pk_766 : ¬ Nat.Prime ((766+1)^(Nat.totient (1408-766)/2) - 766) := refute_e 766 106 3 (by decide) (by decide)
theorem pk_767 : ¬ Nat.Prime ((767+1)^(Nat.totient (1408-767)/2) - 767) := refute_e 767 320 7 (by decide) (by decide)
theorem pk_768 : ¬ Nat.Prime ((768+1)^(Nat.totient (1408-768)/2) - 768) := refute_e 768 128 23 (by decide) (by decide)
theorem pk_769 : ¬ Nat.Prime ((769+1)^(Nat.totient (1408-769)/2) - 769) := refute_e 769 210 3 (by decide) (by decide)
theorem pk_770 : ¬ Nat.Prime ((770+1)^(Nat.totient (1408-770)/2) - 770) := refute_e 770 140 13 (by decide) (by decide)
theorem pk_771 : ¬ Nat.Prime ((771+1)^(Nat.totient (1408-771)/2) - 771) := refute_e 771 252 5 (by decide) (by decide)
theorem pk_772 : ¬ Nat.Prime ((772+1)^(Nat.totient (1408-772)/2) - 772) := refute_e 772 104 3 (by decide) (by decide)
theorem pk_773 : ¬ Nat.Prime ((773+1)^(Nat.totient (1408-773)/2) - 773) := refute_e 773 252 3928667 (by decide) (by decide)
theorem pk_774 : ¬ Nat.Prime ((774+1)^(Nat.totient (1408-774)/2) - 774) := refute_e 774 158 7 (by decide) (by decide)
theorem pk_775 : ¬ Nat.Prime ((775+1)^(Nat.totient (1408-775)/2) - 775) := refute_e 775 210 3 (by decide) (by decide)
theorem pk_776 : ¬ Nat.Prime ((776+1)^(Nat.totient (1408-776)/2) - 776) := refute_e 776 156 5 (by decide) (by decide)
theorem pk_777 : ¬ Nat.Prime ((777+1)^(Nat.totient (1408-777)/2) - 777) := refute_e 777 315 5 (by decide) (by decide)
theorem pk_778 : ¬ Nat.Prime ((778+1)^(Nat.totient (1408-778)/2) - 778) := refute_e 778 72 3 (by decide) (by decide)
theorem pk_779 : ¬ Nat.Prime ((779+1)^(Nat.totient (1408-779)/2) - 779) := refute_e 779 288 23433201349 (by decide) (by decide)
theorem pk_780 : ¬ Nat.Prime ((780+1)^(Nat.totient (1408-780)/2) - 780) := refute_e 780 156 70373 (by decide) (by decide)
theorem pk_781 : ¬ Nat.Prime ((781+1)^(Nat.totient (1408-781)/2) - 781) := refute_e 781 180 3 (by decide) (by decide)
theorem pk_782 : ¬ Nat.Prime ((782+1)^(Nat.totient (1408-782)/2) - 782) := refute_e 782 156 48242807 (by decide) (by decide)
theorem pk_783 : ¬ Nat.Prime ((783+1)^(Nat.totient (1408-783)/2) - 783) := refute_e 783 250 3089 (by decide) (by decide)
theorem pk_784 : ¬ Nat.Prime ((784+1)^(Nat.totient (1408-784)/2) - 784) := refute_e 784 96 3 (by decide) (by decide)
theorem pk_785 : ¬ Nat.Prime ((785+1)^(Nat.totient (1408-785)/2) - 785) := refute_e 785 264 7 (by decide) (by decide)
theorem pk_786 : ¬ Nat.Prime ((786+1)^(Nat.totient (1408-786)/2) - 786) := refute_e 786 155 79865708714758299126286420431085094566871250546284869009375579587763334574611528779721026876733538187850550268756371294484282181766928294806631667780200761504798957102774392242908753677657767602796411231376200931052047028351104652816359311231826014851093627703902587990814617370048889908272923239645446429142952592673778927823829742038707833564925486460237690572556819218897530959659002430559608372797453790162639110528355473 (by decide) (by decide)
theorem pk_787 : ¬ Nat.Prime ((787+1)^(Nat.totient (1408-787)/2) - 787) := refute_e 787 198 3 (by decide) (by decide)
theorem pk_788 : ¬ Nat.Prime ((788+1)^(Nat.totient (1408-788)/2) - 788) := refute_e 788 120 31377349 (by decide) (by decide)
theorem pk_789 : ¬ Nat.Prime ((789+1)^(Nat.totient (1408-789)/2) - 789) := refute_e 789 309 21599 (by decide) (by decide)
theorem pk_790 : ¬ Nat.Prime ((790+1)^(Nat.totient (1408-790)/2) - 790) := refute_e 790 102 3 (by decide) (by decide)
theorem pk_791 : ¬ Nat.Prime ((791+1)^(Nat.totient (1408-791)/2) - 791) := refute_e 791 308 5 (by decide) (by decide)
theorem pk_792 : ¬ Nat.Prime ((792+1)^(Nat.totient (1408-792)/2) - 792) := refute_e 792 120 7 (by decide) (by decide)
theorem pk_793 : ¬ Nat.Prime ((793+1)^(Nat.totient (1408-793)/2) - 793) := refute_e 793 160 3 (by decide) (by decide)
theorem pk_794 : ¬ Nat.Prime ((794+1)^(Nat.totient (1408-794)/2) - 794) := refute_e 794 153 173 (by decide) (by decide)
theorem pk_795 : ¬ Nat.Prime ((795+1)^(Nat.totient (1408-795)/2) - 795) := refute_e 795 306 401 (by decide) (by decide)
theorem pk_796 : ¬ Nat.Prime ((796+1)^(Nat.totient (1408-796)/2) - 796) := refute_e 796 96 3 (by decide) (by decide)
theorem pk_797 : ¬ Nat.Prime ((797+1)^(Nat.totient (1408-797)/2) - 797) := refute_e 797 276 11 (by decide) (by decide)
theorem pk_798 : ¬ Nat.Prime ((798+1)^(Nat.totient (1408-798)/2) - 798) := refute_e 798 120 97 (by decide) (by decide)
theorem pk_799 : ¬ Nat.Prime ((799+1)^(Nat.totient (1408-799)/2) - 799) := refute_e 799 168 3 (by decide) (by decide)
theorem pk_800 : ¬ Nat.Prime ((800+1)^(Nat.totient (1408-800)/2) - 800) := refute_e 800 144 17 (by decide) (by decide)
theorem pk_801 : ¬ Nat.Prime ((801+1)^(Nat.totient (1408-801)/2) - 801) := refute_e 801 303 29 (by decide) (by decide)
theorem pk_802 : ¬ Nat.Prime ((802+1)^(Nat.totient (1408-802)/2) - 802) := refute_e 802 100 3 (by decide) (by decide)
theorem pk_803 : ¬ Nat.Prime ((803+1)^(Nat.totient (1408-803)/2) - 803) := refute_e 803 220 17 (by decide) (by decide)
theorem pk_804 : ¬ Nat.Prime ((804+1)^(Nat.totient (1408-804)/2) - 804) := refute_e 804 150 11 (by decide) (by decide)
theorem pk_805 : ¬ Nat.Prime ((805+1)^(Nat.totient (1408-805)/2) - 805) := refute_e 805 198 3 (by decide) (by decide)
theorem pk_806 : ¬ Nat.Prime ((806+1)^(Nat.totient (1408-806)/2) - 806) := refute_e 806 126 7 (by decide) (by decide)
theorem pk_807 : ¬ Nat.Prime ((807+1)^(Nat.totient (1408-807)/2) - 807) := refute_e 807 300 13 (by decide) (by decide)
theorem pk_808 : ¬ Nat.Prime ((808+1)^(Nat.totient (1408-808)/2) - 808) := refute_e 808 80 3 (by decide) (by decide)
theorem pk_809 : ¬ Nat.Prime ((809+1)^(Nat.totient (1408-809)/2) - 809) := refute_e 809 299 2759059 (by decide) (by decide)
theorem pk_810 : ¬ Nat.Prime ((810+1)^(Nat.totient (1408-810)/2) - 810) := refute_e 810 132 14815891427 (by decide) (by decide)
theorem pk_811 : ¬ Nat.Prime ((811+1)^(Nat.totient (1408-811)/2) - 811) := refute_e 811 198 3 (by decide) (by decide)
theorem pk_812 : ¬ Nat.Prime ((812+1)^(Nat.totient (1408-812)/2) - 812) := refute_e 812 148 17 (by decide) (by decide)
theorem pk_813 : ¬ Nat.Prime ((813+1)^(Nat.totient (1408-813)/2) - 813) := refute_e 813 192 7 (by decide) (by decide)
theorem pk_814 : ¬ Nat.Prime ((814+1)^(Nat.totient (1408-814)/2) - 814) := refute_e 814 90 3 (by decide) (by decide)
theorem pk_815 : ¬ Nat.Prime ((815+1)^(Nat.totient (1408-815)/2) - 815) := refute_e 815 296 13 (by decide) (by decide)
theorem pk_816 : ¬ Nat.Prime ((816+1)^(Nat.totient (1408-816)/2) - 816) := refute_e 816 144 5 (by decide) (by decide)
theorem pk_817 : ¬ Nat.Prime ((817+1)^(Nat.totient (1408-817)/2) - 817) := refute_e 817 196 3 (by decide) (by decide)
theorem pk_818 : ¬ Nat.Prime ((818+1)^(Nat.totient (1408-818)/2) - 818) := refute_e 818 116 18869 (by decide) (by decide)
theorem pk_819 : ¬ Nat.Prime ((819+1)^(Nat.totient (1408-819)/2) - 819) := refute_e 819 270 577349 (by decide) (by decide)
theorem pk_820 : ¬ Nat.Prime ((820+1)^(Nat.totient (1408-820)/2) - 820) := refute_e 820 84 3 (by decide) (by decide)
theorem pk_821 : ¬ Nat.Prime ((821+1)^(Nat.totient (1408-821)/2) - 821) := refute_e 821 293 59 (by decide) (by decide)
theorem pk_822 : ¬ Nat.Prime ((822+1)^(Nat.totient (1408-822)/2) - 822) := refute_e 822 146 13 (by decide) (by decide)
theorem pk_823 : ¬ Nat.Prime ((823+1)^(Nat.totient (1408-823)/2) - 823) := refute_e 823 144 3 (by decide) (by decide)
theorem pk_824 : ¬ Nat.Prime ((824+1)^(Nat.totient (1408-824)/2) - 824) := refute_e 824 144 14831 (by decide) (by decide)
theorem pk_825 : ¬ Nat.Prime ((825+1)^(Nat.totient (1408-825)/2) - 825) := refute_e 825 260 681451 (by decide) (by decide)
theorem pk_826 : ¬ Nat.Prime ((826+1)^(Nat.totient (1408-826)/2) - 826) := refute_e 826 96 3 (by decide) (by decide)
theorem pk_827 : ¬ Nat.Prime ((827+1)^(Nat.totient (1408-827)/2) - 827) := refute_e 827 246 7 (by decide) (by decide)
theorem pk_828 : ¬ Nat.Prime ((828+1)^(Nat.totient (1408-828)/2) - 828) := refute_e 828 112 317 (by decide) (by decide)
theorem pk_829 : ¬ Nat.Prime ((829+1)^(Nat.totient (1408-829)/2) - 829) := refute_e 829 192 3 (by decide) (by decide)
theorem pk_830 : ¬ Nat.Prime ((830+1)^(Nat.totient (1408-830)/2) - 830) := refute_e 830 136 11 (by decide) (by decide)
theorem pk_831 : ¬ Nat.Prime ((831+1)^(Nat.totient (1408-831)/2) - 831) := refute_e 831 288 5 (by decide) (by decide)
theorem pk_832 : ¬ Nat.Prime ((832+1)^(Nat.totient (1408-832)/2) - 832) := refute_e 832 96 3 (by decide) (by decide)
theorem pk_833 : ¬ Nat.Prime ((833+1)^(Nat.totient (1408-833)/2) - 833) := refute_e 833 220 19 (by decide) (by decide)
theorem pk_834 : ¬ Nat.Prime ((834+1)^(Nat.totient (1408-834)/2) - 834) := refute_e 834 120 7 (by decide) (by decide)
theorem pk_835 : ¬ Nat.Prime ((835+1)^(Nat.totient (1408-835)/2) - 835) := refute_e 835 190 3 (by decide) (by decide)
theorem pk_836 : ¬ Nat.Prime ((836+1)^(Nat.totient (1408-836)/2) - 836) := refute_e 836 120 5 (by decide) (by decide)
theorem pk_837 : ¬ Nat.Prime ((837+1)^(Nat.totient (1408-837)/2) - 837) := refute_e 837 285 13 (by decide) (by decide)
theorem pk_838 : ¬ Nat.Prime ((838+1)^(Nat.totient (1408-838)/2) - 838) := refute_e 838 72 3 (by decide) (by decide)
theorem pk_839 : ¬ Nat.Prime ((839+1)^(Nat.totient (1408-839)/2) - 839) := refute_e 839 284 11 (by decide) (by decide)
theorem pk_840 : ¬ Nat.Prime ((840+1)^(Nat.totient (1408-840)/2) - 840) := refute_e 840 140 37 (by decide) (by decide)
theorem pk_841 : ¬ Nat.Prime ((841+1)^(Nat.totient (1408-841)/2) - 841) := refute_e 841 162 3 (by decide) (by decide)
theorem pk_842 : ¬ Nat.Prime ((842+1)^(Nat.totient (1408-842)/2) - 842) := refute_e 842 141 23 (by decide) (by decide)
theorem pk_843 : ¬ Nat.Prime ((843+1)^(Nat.totient (1408-843)/2) - 843) := refute_e 843 224 19 (by decide) (by decide)
theorem pk_844 : ¬ Nat.Prime ((844+1)^(Nat.totient (1408-844)/2) - 844) := refute_e 844 92 3 (by decide) (by decide)
theorem pk_845 : ¬ Nat.Prime ((845+1)^(Nat.totient (1408-845)/2) - 845) := refute_e 845 281 769 (by decide) (by decide)
theorem pk_846 : ¬ Nat.Prime ((846+1)^(Nat.totient (1408-846)/2) - 846) := refute_e 846 140 5 (by decide) (by decide)
theorem pk_847 : ¬ Nat.Prime ((847+1)^(Nat.totient (1408-847)/2) - 847) := refute_e 847 160 3 (by decide) (by decide)
theorem pk_848 : ¬ Nat.Prime ((848+1)^(Nat.totient (1408-848)/2) - 848) := refute_e 848 96 7 (by decide) (by decide)
theorem pk_849 : ¬ Nat.Prime ((849+1)^(Nat.totient (1408-849)/2) - 849) := refute_e 849 252 239543 (by decide) (by decide)
theorem pk_850 : ¬ Nat.Prime ((850+1)^(Nat.totient (1408-850)/2) - 850) := refute_e 850 90 3 (by decide) (by decide)
theorem pk_851 : ¬ Nat.Prime ((851+1)^(Nat.totient (1408-851)/2) - 851) := refute_e 851 278 7 (by decide) (by decide)
theorem pk_852 : ¬ Nat.Prime ((852+1)^(Nat.totient (1408-852)/2) - 852) := refute_fermat 852 138 230058057288676592818997824447172728182077128879408541431556158964786122741093568047718489839754707891022415476232956931544803874893387553138539987181179698749539614593979482399426004000304774387561862810507061569656510389808278147341333476552736943764352533531310135257994102404639574793962061041482552791733538630737177239372042955883934319485070836320404631441614745708376386898101971213841126861539777 (by decide) (by norm_num) (by norm_num) (by norm_num) (by decide) (by reduce_mod_char)
theorem pk_853 : ¬ Nat.Prime ((853+1)^(Nat.totient (1408-853)/2) - 853) := refute_e 853 144 3 (by decide) (by decide)
theorem pk_854 : ¬ Nat.Prime ((854+1)^(Nat.totient (1408-854)/2) - 854) := refute_e 854 138 461239 (by decide) (by decide)
theorem pk_855 : ¬ Nat.Prime ((855+1)^(Nat.totient (1408-855)/2) - 855) := refute_e 855 234 7 (by decide) (by decide)
theorem pk_856 : ¬ Nat.Prime ((856+1)^(Nat.totient (1408-856)/2) - 856) := refute_e 856 88 3 (by decide) (by decide)
theorem pk_857 : ¬ Nat.Prime ((857+1)^(Nat.totient (1408-857)/2) - 857) := refute_e 857 252 199 (by decide) (by decide)
theorem pk_858 : ¬ Nat.Prime ((858+1)^(Nat.totient (1408-858)/2) - 858) := refute_e 858 100 283 (by decide) (by decide)
theorem pk_859 : ¬ Nat.Prime ((859+1)^(Nat.totient (1408-859)/2) - 859) := refute_e 859 180 3 (by decide) (by decide)
theorem pk_860 : ¬ Nat.Prime ((860+1)^(Nat.totient (1408-860)/2) - 860) := refute_e 860 136 47 (by decide) (by decide)
theorem pk_861 : ¬ Nat.Prime ((861+1)^(Nat.totient (1408-861)/2) - 861) := refute_e 861 273 389 (by decide) (by decide)
theorem pk_862 : ¬ Nat.Prime ((862+1)^(Nat.totient (1408-862)/2) - 862) := refute_e 862 72 3 (by decide) (by decide)
theorem pk_863 : ¬ Nat.Prime ((863+1)^(Nat.totient (1408-863)/2) - 863) := refute_e 863 216 11 (by decide) (by decide)
theorem pk_864 : ¬ Nat.Prime ((864+1)^(Nat.totient (1408-864)/2) - 864) := refute_e 864 128 3767 (by decide) (by decide)
theorem pk_865 : ¬ Nat.Prime ((865+1)^(Nat.totient (1408-865)/2) - 865) := refute_e 865 180 3 (by decide) (by decide)
theorem pk_866 : ¬ Nat.Prime ((866+1)^(Nat.totient (1408-866)/2) - 866) := refute_e 866 135 76429460166893815139 (by decide) (by decide)
theorem pk_867 : ¬ Nat.Prime ((867+1)^(Nat.totient (1408-867)/2) - 867) := refute_e 867 270 6983214534878053061543 (by decide) (by decide)
theorem pk_868 : ¬ Nat.Prime ((868+1)^(Nat.totient (1408-868)/2) - 868) := refute_e 868 72 3 (by decide) (by decide)
theorem pk_869 : ¬ Nat.Prime ((869+1)^(Nat.totient (1408-869)/2) - 869) := refute_e 869 210 7 (by decide) (by decide)
theorem pk_870 : ¬ Nat.Prime ((870+1)^(Nat.totient (1408-870)/2) - 870) := refute_e 870 134 7 (by decide) (by decide)
theorem pk_871 : ¬ Nat.Prime ((871+1)^(Nat.totient (1408-871)/2) - 871) := refute_e 871 178 3 (by decide) (by decide)
theorem pk_872 : ¬ Nat.Prime ((872+1)^(Nat.totient (1408-872)/2) - 872) := refute_e 872 132 13 (by decide) (by decide)
theorem pk_873 : ¬ Nat.Prime ((873+1)^(Nat.totient (1408-873)/2) - 873) := refute_e 873 212 31 (by decide) (by decide)
theorem pk_874 : ¬ Nat.Prime ((874+1)^(Nat.totient (1408-874)/2) - 874) := refute_e 874 88 3 (by decide) (by decide)
theorem pk_875 : ¬ Nat.Prime ((875+1)^(Nat.totient (1408-875)/2) - 875) := refute_e 875 240 313 (by decide) (by decide)
theorem pk_876 : ¬ Nat.Prime ((876+1)^(Nat.totient (1408-876)/2) - 876) := refute_e 876 108 5 (by decide) (by decide)
theorem pk_877 : ¬ Nat.Prime ((877+1)^(Nat.totient (1408-877)/2) - 877) := refute_e 877 174 3 (by decide) (by decide)
theorem pk_878 : ¬ Nat.Prime ((878+1)^(Nat.totient (1408-878)/2) - 878) := refute_e 878 104 7933 (by decide) (by decide)
theorem pk_879 : ¬ Nat.Prime ((879+1)^(Nat.totient (1408-879)/2) - 879) := refute_e 879 253 10711 (by decide) (by decide)
theorem pk_880 : ¬ Nat.Prime ((880+1)^(Nat.totient (1408-880)/2) - 880) := refute_e 880 80 3 (by decide) (by decide)
theorem pk_881 : ¬ Nat.Prime ((881+1)^(Nat.totient (1408-881)/2) - 881) := refute_e 881 240 5 (by decide) (by decide)
theorem pk_882 : ¬ Nat.Prime ((882+1)^(Nat.totient (1408-882)/2) - 882) := refute_e 882 131 5 (by decide) (by decide)
theorem pk_883 : ¬ Nat.Prime ((883+1)^(Nat.totient (1408-883)/2) - 883) := refute_e 883 120 3 (by decide) (by decide)
theorem pk_884 : ¬ Nat.Prime ((884+1)^(Nat.totient (1408-884)/2) - 884) := refute_e 884 130 35027 (by decide) (by decide)
theorem pk_885 : ¬ Nat.Prime ((885+1)^(Nat.totient (1408-885)/2) - 885) := refute_e 885 261 5789657 (by decide) (by decide)
theorem pk_886 : ¬ Nat.Prime ((886+1)^(Nat.totient (1408-886)/2) - 886) := refute_e 886 84 3 (by decide) (by decide)
theorem pk_887 : ¬ Nat.Prime ((887+1)^(Nat.totient (1408-887)/2) - 887) := refute_e 887 260 13 (by decide) (by decide)
theorem pk_888 : ¬ Nat.Prime ((888+1)^(Nat.totient (1408-888)/2) - 888) := refute_e 888 96 3524779 (by decide) (by decide)
theorem pk_889 : ¬ Nat.Prime ((889+1)^(Nat.totient (1408-889)/2) - 889) := refute_e 889 172 3 (by decide) (by decide)
theorem pk_890 : ¬ Nat.Prime ((890+1)^(Nat.totient (1408-890)/2) - 890) := refute_e 890 108 7 (by decide) (by decide)
theorem pk_891 : ¬ Nat.Prime ((891+1)^(Nat.totient (1408-891)/2) - 891) := refute_e 891 230 7 (by decide) (by decide)
theorem pk_892 : ¬ Nat.Prime ((892+1)^(Nat.totient (1408-892)/2) - 892) := refute_e 892 84 3 (by decide) (by decide)
theorem pk_893 : ¬ Nat.Prime ((893+1)^(Nat.totient (1408-893)/2) - 893) := refute_e 893 204 1823357 (by decide) (by decide)
theorem pk_894 : ¬ Nat.Prime ((894+1)^(Nat.totient (1408-894)/2) - 894) := refute_e 894 128 800131 (by decide) (by decide)
theorem pk_895 : ¬ Nat.Prime ((895+1)^(Nat.totient (1408-895)/2) - 895) := refute_e 895 162 3 (by decide) (by decide)
theorem pk_896 : ¬ Nat.Prime ((896+1)^(Nat.totient (1408-896)/2) - 896) := refute_e 896 128 5 (by decide) (by decide)
theorem pk_897 : ¬ Nat.Prime ((897+1)^(Nat.totient (1408-897)/2) - 897) := refute_e 897 216 7 (by decide) (by decide)
theorem pk_898 : ¬ Nat.Prime ((898+1)^(Nat.totient (1408-898)/2) - 898) := refute_e 898 64 3 (by decide) (by decide)
theorem pk_899 : ¬ Nat.Prime ((899+1)^(Nat.totient (1408-899)/2) - 899) := refute_e 899 254 67943 (by decide) (by decide)
theorem pk_900 : ¬ Nat.Prime ((900+1)^(Nat.totient (1408-900)/2) - 900) := refute_e 900 126 1163 (by decide) (by decide)
theorem pk_901 : ¬ Nat.Prime ((901+1)^(Nat.totient (1408-901)/2) - 901) := refute_e 901 156 3 (by decide) (by decide)
theorem pk_902 : ¬ Nat.Prime ((902+1)^(Nat.totient (1408-902)/2) - 902) := refute_e 902 110 199 (by decide) (by decide)
theorem pk_903 : ¬ Nat.Prime ((903+1)^(Nat.totient (1408-903)/2) - 903) := refute_e 903 200 11 (by decide) (by decide)
theorem pk_904 : ¬ Nat.Prime ((904+1)^(Nat.totient (1408-904)/2) - 904) := refute_e 904 72 3 (by decide) (by decide)
theorem pk_905 : ¬ Nat.Prime ((905+1)^(Nat.totient (1408-905)/2) - 905) := refute_e 905 251 3793 (by decide) (by decide)
theorem pk_906 : ¬ Nat.Prime ((906+1)^(Nat.totient (1408-906)/2) - 906) := refute_e 906 125 355171 (by decide) (by decide)
theorem pk_907 : ¬ Nat.Prime ((907+1)^(Nat.totient (1408-907)/2) - 907) := refute_e 907 166 3 (by decide) (by decide)
theorem pk_908 : ¬ Nat.Prime ((908+1)^(Nat.totient (1408-908)/2) - 908) := refute_e 908 100 5477 (by decide) (by decide)
theorem pk_909 : ¬ Nat.Prime ((909+1)^(Nat.totient (1408-909)/2) - 909) := refute_e 909 249 11 (by decide) (by decide)
theorem pk_910 : ¬ Nat.Prime ((910+1)^(Nat.totient (1408-910)/2) - 910) := refute_e 910 82 3 (by decide) (by decide)
theorem pk_911 : ¬ Nat.Prime ((911+1)^(Nat.totient (1408-911)/2) - 911) := refute_e 911 210 7 (by decide) (by decide)
theorem pk_912 : ¬ Nat.Prime ((912+1)^(Nat.totient (1408-912)/2) - 912) := refute_e 912 120 3092435830090367 (by decide) (by decide)
theorem pk_913 : ¬ Nat.Prime ((913+1)^(Nat.totient (1408-913)/2) - 913) := refute_e 913 120 3 (by decide) (by decide)
theorem pk_914 : ¬ Nat.Prime ((914+1)^(Nat.totient (1408-914)/2) - 914) := refute_fermat 914 108 16085480282051169682006291463464260828069782052241061005331263995314337902665705886784744712055537437271853264356104872123050391436465748313433622722766284636202204542326751319749513115507708747469679456315437367234200034667280563315881434624438597153980872215225792771550174125261523897149567454264746604148771903324282 (by decide) (by norm_num) (by norm_num) (by norm_num) (by decide) (by reduce_mod_char)
theorem pk_915 : ¬ Nat.Prime ((915+1)^(Nat.totient (1408-915)/2) - 915) := refute_e 915 224 838141 (by decide) (by decide)
theorem pk_916 : ¬ Nat.Prime ((916+1)^(Nat.totient (1408-916)/2) - 916) := refute_e 916 80 3 (by decide) (by decide)
theorem pk_917 : ¬ Nat.Prime ((917+1)^(Nat.totient (1408-917)/2) - 917) := refute_e 917 245 1667 (by decide) (by decide)
theorem pk_918 : ¬ Nat.Prime ((918+1)^(Nat.totient (1408-918)/2) - 918) := refute_e 918 84 7 (by decide) (by decide)
theorem pk_919 : ¬ Nat.Prime ((919+1)^(Nat.totient (1408-919)/2) - 919) := refute_e 919 162 3 (by decide) (by decide)
theorem pk_920 : ¬ Nat.Prime ((920+1)^(Nat.totient (1408-920)/2) - 920) := refute_e 920 120 107 (by decide) (by decide)
theorem pk_921 : ¬ Nat.Prime ((921+1)^(Nat.totient (1408-921)/2) - 921) := refute_e 921 243 6047 (by decide) (by decide)
theorem pk_922 : ¬ Nat.Prime ((922+1)^(Nat.totient (1408-922)/2) - 922) := refute_e 922 81 10039 (by decide) (by decide)
theorem pk_923 : ¬ Nat.Prime ((923+1)^(Nat.totient (1408-923)/2) - 923) := refute_e 923 192 569 (by decide) (by decide)
theorem pk_924 : ¬ Nat.Prime ((924+1)^(Nat.totient (1408-924)/2) - 924) := refute_e 924 110 31 (by decide) (by decide)
theorem pk_925 : ¬ Nat.Prime ((925+1)^(Nat.totient (1408-925)/2) - 925) := refute_e 925 132 3 (by decide) (by decide)
theorem pk_926 : ¬ Nat.Prime ((926+1)^(Nat.totient (1408-926)/2) - 926) := refute_e 926 120 5 (by decide) (by decide)
theorem pk_927 : ¬ Nat.Prime ((927+1)^(Nat.totient (1408-927)/2) - 927) := refute_e 927 216 3413 (by decide) (by decide)
theorem pk_928 : ¬ Nat.Prime ((928+1)^(Nat.totient (1408-928)/2) - 928) := refute_e 928 64 3 (by decide) (by decide)
theorem pk_929 : ¬ Nat.Prime ((929+1)^(Nat.totient (1408-929)/2) - 929) := refute_e 929 239 887 (by decide) (by decide)
theorem pk_930 : ¬ Nat.Prime ((930+1)^(Nat.totient (1408-930)/2) - 930) := refute_e 930 119 59 (by decide) (by decide)
theorem pk_931 : ¬ Nat.Prime ((931+1)^(Nat.totient (1408-931)/2) - 931) := refute_e 931 156 3 (by decide) (by decide)
theorem pk_932 : ¬ Nat.Prime ((932+1)^(Nat.totient (1408-932)/2) - 932) := refute_e 932 96 7 (by decide) (by decide)
theorem pk_933 : ¬ Nat.Prime ((933+1)^(Nat.totient (1408-933)/2) - 933) := refute_e 933 180 1579 (by decide) (by decide)
theorem pk_934 : ¬ Nat.Prime ((934+1)^(Nat.totient (1408-934)/2) - 934) := refute_e 934 78 3 (by decide) (by decide)
theorem pk_935 : ¬ Nat.Prime ((935+1)^(Nat.totient (1408-935)/2) - 935) := refute_e 935 210 293 (by decide) (by decide)
theorem pk_936 : ¬ Nat.Prime ((936+1)^(Nat.totient (1408-936)/2) - 936) := refute_e 936 116 5 (by decide) (by decide)
theorem pk_937 : ¬ Nat.Prime ((937+1)^(Nat.totient (1408-937)/2) - 937) := refute_e 937 156 3 (by decide) (by decide)
theorem pk_938 : ¬ Nat.Prime ((938+1)^(Nat.totient (1408-938)/2) - 938) := refute_e 938 92 19 (by decide) (by decide)
theorem pk_939 : ¬ Nat.Prime ((939+1)^(Nat.totient (1408-939)/2) - 939) := refute_e 939 198 7 (by decide) (by decide)
theorem pk_940 : ¬ Nat.Prime ((940+1)^(Nat.totient (1408-940)/2) - 940) := refute_e 940 72 3 (by decide) (by decide)
theorem pk_941 : ¬ Nat.Prime ((941+1)^(Nat.totient (1408-941)/2) - 941) := refute_e 941 233 271 (by decide) (by decide)
theorem pk_942 : ¬ Nat.Prime ((942+1)^(Nat.totient (1408-942)/2) - 942) := refute_e 942 116 7 (by decide) (by decide)
theorem pk_943 : ¬ Nat.Prime ((943+1)^(Nat.totient (1408-943)/2) - 943) := refute_e 943 120 3 (by decide) (by decide)
theorem pk_944 : ¬ Nat.Prime ((944+1)^(Nat.totient (1408-944)/2) - 944) := refute_e 944 112 47917 (by decide) (by decide)
theorem pk_945 : ¬ Nat.Prime ((945+1)^(Nat.totient (1408-945)/2) - 945) := refute_e 945 231 29 (by decide) (by decide)
theorem pk_946 : ¬ Nat.Prime ((946+1)^(Nat.totient (1408-946)/2) - 946) := refute_e 946 60 3 (by decide) (by decide)
theorem pk_947 : ¬ Nat.Prime ((947+1)^(Nat.totient (1408-947)/2) - 947) := refute_e 947 230 7 (by decide) (by decide)
theorem pk_948 : ¬ Nat.Prime ((948+1)^(Nat.totient (1408-948)/2) - 948) := refute_e 948 88 2437 (by decide) (by decide)
theorem pk_949 : ¬ Nat.Prime ((949+1)^(Nat.totient (1408-949)/2) - 949) := refute_e 949 144 3 (by decide) (by decide)
theorem pk_950 : ¬ Nat.Prime ((950+1)^(Nat.totient (1408-950)/2) - 950) := refute_e 950 114 1753 (by decide) (by decide)
theorem pk_951 : ¬ Nat.Prime ((951+1)^(Nat.totient (1408-951)/2) - 951) := refute_e 951 228 5 (by decide) (by decide)
theorem pk_952 : ¬ Nat.Prime ((952+1)^(Nat.totient (1408-952)/2) - 952) := refute_e 952 72 3 (by decide) (by decide)
theorem pk_953 : ¬ Nat.Prime ((953+1)^(Nat.totient (1408-953)/2) - 953) := refute_e 953 144 7 (by decide) (by decide)
theorem pk_954 : ¬ Nat.Prime ((954+1)^(Nat.totient (1408-954)/2) - 954) := refute_e 954 113 10847 (by decide) (by decide)
theorem pk_955 : ¬ Nat.Prime ((955+1)^(Nat.totient (1408-955)/2) - 955) := refute_e 955 150 3 (by decide) (by decide)
theorem pk_956 : ¬ Nat.Prime ((956+1)^(Nat.totient (1408-956)/2) - 956) := refute_e 956 112 5 (by decide) (by decide)
theorem pk_957 : ¬ Nat.Prime ((957+1)^(Nat.totient (1408-957)/2) - 957) := refute_e 957 200 19 (by decide) (by decide)
theorem pk_958 : ¬ Nat.Prime ((958+1)^(Nat.totient (1408-958)/2) - 958) := refute_e 958 60 3 (by decide) (by decide)
theorem pk_959 : ¬ Nat.Prime ((959+1)^(Nat.totient (1408-959)/2) - 959) := refute_e 959 224 37 (by decide) (by decide)
theorem pk_960 : ¬ Nat.Prime ((960+1)^(Nat.totient (1408-960)/2) - 960) := refute_e 960 96 7 (by decide) (by decide)
theorem pk_961 : ¬ Nat.Prime ((961+1)^(Nat.totient (1408-961)/2) - 961) := refute_e 961 148 3 (by decide) (by decide)
theorem pk_962 : ¬ Nat.Prime ((962+1)^(Nat.totient (1408-962)/2) - 962) := refute_e 962 111 5 (by decide) (by decide)
theorem pk_963 : ¬ Nat.Prime ((963+1)^(Nat.totient (1408-963)/2) - 963) := refute_e 963 176 7 (by decide) (by decide)
theorem pk_964 : ¬ Nat.Prime ((964+1)^(Nat.totient (1408-964)/2) - 964) := refute_e 964 72 3 (by decide) (by decide)
theorem pk_965 : ¬ Nat.Prime ((965+1)^(Nat.totient (1408-965)/2) - 965) := refute_e 965 221 481192237 (by decide) (by decide)
theorem pk_966 : ¬ Nat.Prime ((966+1)^(Nat.totient (1408-966)/2) - 966) := refute_e 966 96 5 (by decide) (by decide)
theorem pk_967 : ¬ Nat.Prime ((967+1)^(Nat.totient (1408-967)/2) - 967) := refute_e 967 126 3 (by decide) (by decide)
theorem pk_968 : ¬ Nat.Prime ((968+1)^(Nat.totient (1408-968)/2) - 968) := refute_e 968 80 7 (by decide) (by decide)
theorem pk_969 : ¬ Nat.Prime ((969+1)^(Nat.totient (1408-969)/2) - 969) := refute_e 969 219 89 (by decide) (by decide)
theorem pk_970 : ¬ Nat.Prime ((970+1)^(Nat.totient (1408-970)/2) - 970) := refute_e 970 72 3 (by decide) (by decide)
theorem pk_971 : ¬ Nat.Prime ((971+1)^(Nat.totient (1408-971)/2) - 971) := refute_e 971 198 52769837016241073 (by decide) (by decide)
theorem pk_972 : ¬ Nat.Prime ((972+1)^(Nat.totient (1408-972)/2) - 972) := refute_e 972 108 11 (by decide) (by decide)
theorem pk_973 : ¬ Nat.Prime ((973+1)^(Nat.totient (1408-973)/2) - 973) := refute_e 973 112 3 (by decide) (by decide)
theorem pk_974 : ¬ Nat.Prime ((974+1)^(Nat.totient (1408-974)/2) - 974) := refute_e 974 90 7 (by decide) (by decide)
theorem pk_975 : ¬ Nat.Prime ((975+1)^(Nat.totient (1408-975)/2) - 975) := refute_e 975 216 23 (by decide) (by decide)
theorem pk_976 : ¬ Nat.Prime ((976+1)^(Nat.totient (1408-976)/2) - 976) := refute_e 976 72 3 (by decide) (by decide)
theorem pk_977 : ¬ Nat.Prime ((977+1)^(Nat.totient (1408-977)/2) - 977) := refute_e 977 215 5 (by decide) (by decide)
theorem pk_978 : ¬ Nat.Prime ((978+1)^(Nat.totient (1408-978)/2) - 978) := refute_e 978 84 27434893 (by decide) (by decide)
theorem pk_979 : ¬ Nat.Prime ((979+1)^(Nat.totient (1408-979)/2) - 979) := refute_e 979 120 3 (by decide) (by decide)
theorem pk_980 : ¬ Nat.Prime ((980+1)^(Nat.totient (1408-980)/2) - 980) := refute_e 980 106 45181 (by decide) (by decide)
theorem pk_981 : ¬ Nat.Prime ((981+1)^(Nat.totient (1408-981)/2) - 981) := refute_e 981 180 5 (by decide) (by decide)
theorem pk_982 : ¬ Nat.Prime ((982+1)^(Nat.totient (1408-982)/2) - 982) := refute_e 982 70 3 (by decide) (by decide)
theorem pk_983 : ¬ Nat.Prime ((983+1)^(Nat.totient (1408-983)/2) - 983) := refute_e 983 160 179 (by decide) (by decide)
theorem pk_984 : ¬ Nat.Prime ((984+1)^(Nat.totient (1408-984)/2) - 984) := refute_e 984 104 7 (by decide) (by decide)
theorem pk_985 : ¬ Nat.Prime ((985+1)^(Nat.totient (1408-985)/2) - 985) := refute_e 985 138 3 (by decide) (by decide)
theorem pk_986 : ¬ Nat.Prime ((986+1)^(Nat.totient (1408-986)/2) - 986) := refute_fermat 986 105 56612423800338300361911592608796556887983956890602394115184015105341005980646545871491642729630827402098310526425228689468352609026899992172595828797409606203342624751592467424595053402471335198616217958100177341119983153688603413902068078863351308887034037923686576714215632670687711086531046142354598314931901117 (by decide) (by norm_num) (by norm_num) (by norm_num) (by decide) (by reduce_mod_char)
theorem pk_987 : ¬ Nat.Prime ((987+1)^(Nat.totient (1408-987)/2) - 987) := refute_e 987 210 191 (by decide) (by decide)
theorem pk_988 : ¬ Nat.Prime ((988+1)^(Nat.totient (1408-988)/2) - 988) := refute_e 988 48 3 (by decide) (by decide)
theorem pk_989 : ¬ Nat.Prime ((989+1)^(Nat.totient (1408-989)/2) - 989) := refute_e 989 209 271 (by decide) (by decide)
theorem pk_990 : ¬ Nat.Prime ((990+1)^(Nat.totient (1408-990)/2) - 990) := refute_e 990 90 47 (by decide) (by decide)
theorem pk_991 : ¬ Nat.Prime ((991+1)^(Nat.totient (1408-991)/2) - 991) := refute_e 991 138 3 (by decide) (by decide)
theorem pk_992 : ¬ Nat.Prime ((992+1)^(Nat.totient (1408-992)/2) - 992) := refute_e 992 96 2917 (by decide) (by decide)
theorem pk_993 : ¬ Nat.Prime ((993+1)^(Nat.totient (1408-993)/2) - 993) := refute_e 993 164 11 (by decide) (by decide)
theorem pk_994 : ¬ Nat.Prime ((994+1)^(Nat.totient (1408-994)/2) - 994) := refute_e 994 66 3 (by decide) (by decide)
theorem pk_995 : ¬ Nat.Prime ((995+1)^(Nat.totient (1408-995)/2) - 995) := refute_e 995 174 7 (by decide) (by decide)
theorem pk_996 : ¬ Nat.Prime ((996+1)^(Nat.totient (1408-996)/2) - 996) := refute_e 996 102 107 (by decide) (by decide)
theorem pk_997 : ¬ Nat.Prime ((997+1)^(Nat.totient (1408-997)/2) - 997) := refute_e 997 136 3 (by decide) (by decide)
theorem pk_998 : ¬ Nat.Prime ((998+1)^(Nat.totient (1408-998)/2) - 998) := refute_e 998 80 7 (by decide) (by decide)
theorem pk_999 : ¬ Nat.Prime ((999+1)^(Nat.totient (1408-999)/2) - 999) := refute_e 999 204 1801 (by decide) (by decide)
theorem pk_1000 : ¬ Nat.Prime ((1000+1)^(Nat.totient (1408-1000)/2) - 1000) := refute_e 1000 64 3 (by decide) (by decide)
theorem pk_1001 : ¬ Nat.Prime ((1001+1)^(Nat.totient (1408-1001)/2) - 1001) := refute_e 1001 180 5 (by decide) (by decide)
theorem pk_1002 : ¬ Nat.Prime ((1002+1)^(Nat.totient (1408-1002)/2) - 1002) := refute_e 1002 84 7 (by decide) (by decide)
theorem pk_1003 : ¬ Nat.Prime ((1003+1)^(Nat.totient (1408-1003)/2) - 1003) := refute_e 1003 108 3 (by decide) (by decide)
theorem pk_1004 : ¬ Nat.Prime ((1004+1)^(Nat.totient (1408-1004)/2) - 1004) := refute_e 1004 100 3359 (by decide) (by decide)
theorem pk_1005 : ¬ Nat.Prime ((1005+1)^(Nat.totient (1408-1005)/2) - 1005) := refute_e 1005 180 10501 (by decide) (by decide)
theorem pk_1006 : ¬ Nat.Prime ((1006+1)^(Nat.totient (1408-1006)/2) - 1006) := refute_e 1006 66 3 (by decide) (by decide)
theorem pk_1007 : ¬ Nat.Prime ((1007+1)^(Nat.totient (1408-1007)/2) - 1007) := refute_e 1007 200 1015057 (by decide) (by decide)
theorem pk_1008 : ¬ Nat.Prime ((1008+1)^(Nat.totient (1408-1008)/2) - 1008) := refute_e 1008 80 727 (by decide) (by decide)
theorem pk_1009 : ¬ Nat.Prime ((1009+1)^(Nat.totient (1408-1009)/2) - 1009) := refute_e 1009 108 3 (by decide) (by decide)
theorem pk_1010 : ¬ Nat.Prime ((1010+1)^(Nat.totient (1408-1010)/2) - 1010) := refute_e 1010 99 349 (by decide) (by decide)
theorem pk_1011 : ¬ Nat.Prime ((1011+1)^(Nat.totient (1408-1011)/2) - 1011) := refute_e 1011 198 47 (by decide) (by decide)
theorem pk_1012 : ¬ Nat.Prime ((1012+1)^(Nat.totient (1408-1012)/2) - 1012) := refute_e 1012 60 3 (by decide) (by decide)
theorem pk_1013 : ¬ Nat.Prime ((1013+1)^(Nat.totient (1408-1013)/2) - 1013) := refute_fermat 1013 156 1496606140696432848700391795044384249113992133350024260032915403363028111147140705142225342441238193194772108820747918559793020407882656877606882102546111995024558771399796158292721060122650873075277548453602729844837695158769954960675452348799807830070088124223194448429429309952689956002162737497954709128589557360813825549077462752361615003839443605391724897011838055524560385929633083584282398186142144343008509277151991051708695962724162074846966410960243521477701 (by decide) (by norm_num) (by norm_num) (by norm_num) (by decide) (by reduce_mod_char)
theorem pk_1014 : ¬ Nat.Prime ((1014+1)^(Nat.totient (1408-1014)/2) - 1014) := refute_e 1014 98 19 (by decide) (by decide)
theorem pk_1015 : ¬ Nat.Prime ((1015+1)^(Nat.totient (1408-1015)/2) - 1015) := refute_e 1015 130 3 (by decide) (by decide)
theorem pk_1016 : ¬ Nat.Prime ((1016+1)^(Nat.totient (1408-1016)/2) - 1016) := refute_e 1016 84 5 (by decide) (by decide)
theorem pk_1017 : ¬ Nat.Prime ((1017+1)^(Nat.totient (1408-1017)/2) - 1017) := refute_e 1017 176 7 (by decide) (by decide)
theorem pk_1018 : ¬ Nat.Prime ((1018+1)^(Nat.totient (1408-1018)/2) - 1018) := refute_e 1018 48 3 (by decide) (by decide)
theorem pk_1019 : ¬ Nat.Prime ((1019+1)^(Nat.totient (1408-1019)/2) - 1019) := refute_e 1019 194 7 (by decide) (by decide)
theorem pk_1020 : ¬ Nat.Prime ((1020+1)^(Nat.totient (1408-1020)/2) - 1020) := refute_e 1020 96 67 (by decide) (by decide)
theorem pk_1021 : ¬ Nat.Prime ((1021+1)^(Nat.totient (1408-1021)/2) - 1021) := refute_e 1021 126 3 (by decide) (by decide)
theorem pk_1022 : ¬ Nat.Prime ((1022+1)^(Nat.totient (1408-1022)/2) - 1022) := refute_e 1022 96 439 (by decide) (by decide)
theorem pk_1023 : ¬ Nat.Prime ((1023+1)^(Nat.totient (1408-1023)/2) - 1023) := refute_e 1023 120 7 (by decide) (by decide)
theorem pk_1024 : ¬ Nat.Prime ((1024+1)^(Nat.totient (1408-1024)/2) - 1024) := refute_e 1024 64 3 (by decide) (by decide)
theorem pk_1025 : ¬ Nat.Prime ((1025+1)^(Nat.totient (1408-1025)/2) - 1025) := refute_e 1025 191 6361 (by decide) (by decide)
theorem pk_1026 : ¬ Nat.Prime ((1026+1)^(Nat.totient (1408-1026)/2) - 1026) := refute_fermat 1026 95 3623748641850494350351721159298897977928568339421391973707230303211358691950475137820480899014530486134711915970965249794901084358455567227554581038795167909864843545870588388288492439854361945151975827007378894462240197674856887984698214818315408633601751671310496199930767367115235608 (by decide) (by norm_num) (by norm_num) (by norm_num) (by decide) (by reduce_mod_char)
theorem pk_1027 : ¬ Nat.Prime ((1027+1)^(Nat.totient (1408-1027)/2) - 1027) := refute_e 1027 126 3 (by decide) (by decide)
theorem pk_1028 : ¬ Nat.Prime ((1028+1)^(Nat.totient (1408-1028)/2) - 1028) := refute_e 1028 72 13 (by decide) (by decide)
theorem pk_1029 : ¬ Nat.Prime ((1029+1)^(Nat.totient (1408-1029)/2) - 1029) := refute_e 1029 189 59 (by decide) (by decide)
theorem pk_1030 : ¬ Nat.Prime ((1030+1)^(Nat.totient (1408-1030)/2) - 1030) := refute_e 1030 54 3 (by decide) (by decide)
theorem pk_1031 : ¬ Nat.Prime ((1031+1)^(Nat.totient (1408-1031)/2) - 1031) := refute_e 1031 168 5 (by decide) (by decide)
theorem pk_1032 : ¬ Nat.Prime ((1032+1)^(Nat.totient (1408-1032)/2) - 1032) := refute_e 1032 92 571 (by decide) (by decide)
theorem pk_1033 : ¬ Nat.Prime ((1033+1)^(Nat.totient (1408-1033)/2) - 1033) := refute_e 1033 100 3 (by decide) (by decide)
theorem pk_1034 : ¬ Nat.Prime ((1034+1)^(Nat.totient (1408-1034)/2) - 1034) := refute_e 1034 80 67 (by decide) (by decide)
theorem pk_1035 : ¬ Nat.Prime ((1035+1)^(Nat.totient (1408-1035)/2) - 1035) := refute_e 1035 186 5059 (by decide) (by decide)
theorem pk_1036 : ¬ Nat.Prime ((1036+1)^(Nat.totient (1408-1036)/2) - 1036) := refute_e 1036 60 3 (by decide) (by decide)
theorem pk_1037 : ¬ Nat.Prime ((1037+1)^(Nat.totient (1408-1037)/2) - 1037) := refute_e 1037 156 7 (by decide) (by decide)
theorem pk_1038 : ¬ Nat.Prime ((1038+1)^(Nat.totient (1408-1038)/2) - 1038) := refute_e 1038 72 17 (by decide) (by decide)
theorem pk_1039 : ¬ Nat.Prime ((1039+1)^(Nat.totient (1408-1039)/2) - 1039) := refute_e 1039 120 3 (by decide) (by decide)
theorem pk_1040 : ¬ Nat.Prime ((1040+1)^(Nat.totient (1408-1040)/2) - 1040) := refute_e 1040 88 802811 (by decide) (by decide)
theorem pk_1041 : ¬ Nat.Prime ((1041+1)^(Nat.totient (1408-1041)/2) - 1041) := refute_e 1041 183 22526887625491 (by decide) (by decide)
theorem pk_1042 : ¬ Nat.Prime ((1042+1)^(Nat.totient (1408-1042)/2) - 1042) := refute_e 1042 60 3 (by decide) (by decide)
theorem pk_1043 : ¬ Nat.Prime ((1043+1)^(Nat.totient (1408-1043)/2) - 1043) := refute_e 1043 144 41 (by decide) (by decide)
theorem pk_1044 : ¬ Nat.Prime ((1044+1)^(Nat.totient (1408-1044)/2) - 1044) := refute_e 1044 72 7 (by decide) (by decide)
theorem pk_1045 : ¬ Nat.Prime ((1045+1)^(Nat.totient (1408-1045)/2) - 1045) := refute_e 1045 110 3 (by decide) (by decide)
theorem pk_1046 : ¬ Nat.Prime ((1046+1)^(Nat.totient (1408-1046)/2) - 1046) := refute_e 1046 90 11 (by decide) (by decide)
theorem pk_1047 : ¬ Nat.Prime ((1047+1)^(Nat.totient (1408-1047)/2) - 1047) := refute_e 1047 171 5 (by decide) (by decide)
theorem pk_1048 : ¬ Nat.Prime ((1048+1)^(Nat.totient (1408-1048)/2) - 1048) := refute_e 1048 48 3 (by decide) (by decide)
theorem pk_1049 : ¬ Nat.Prime ((1049+1)^(Nat.totient (1408-1049)/2) - 1049) := refute_e 1049 179 19 (by decide) (by decide)
theorem pk_1050 : ¬ Nat.Prime ((1050+1)^(Nat.totient (1408-1050)/2) - 1050) := refute_e 1050 89 163 (by decide) (by decide)
theorem pk_1051 : ¬ Nat.Prime ((1051+1)^(Nat.totient (1408-1051)/2) - 1051) := refute_e 1051 96 3 (by decide) (by decide)
theorem pk_1052 : ¬ Nat.Prime ((1052+1)^(Nat.totient (1408-1052)/2) - 1052) := refute_e 1052 88 37 (by decide) (by decide)
theorem pk_1053 : ¬ Nat.Prime ((1053+1)^(Nat.totient (1408-1053)/2) - 1053) := refute_e 1053 140 547 (by decide) (by decide)
theorem pk_1054 : ¬ Nat.Prime ((1054+1)^(Nat.totient (1408-1054)/2) - 1054) := refute_e 1054 58 3 (by decide) (by decide)
theorem pk_1055 : ¬ Nat.Prime ((1055+1)^(Nat.totient (1408-1055)/2) - 1055) := refute_e 1055 176 17 (by decide) (by decide)
theorem pk_1056 : ¬ Nat.Prime ((1056+1)^(Nat.totient (1408-1056)/2) - 1056) := refute_e 1056 80 5 (by decide) (by decide)
theorem pk_1057 : ¬ Nat.Prime ((1057+1)^(Nat.totient (1408-1057)/2) - 1057) := refute_e 1057 108 3 (by decide) (by decide)
theorem pk_1058 : ¬ Nat.Prime ((1058+1)^(Nat.totient (1408-1058)/2) - 1058) := refute_e 1058 60 7 (by decide) (by decide)
theorem pk_1059 : ¬ Nat.Prime ((1059+1)^(Nat.totient (1408-1059)/2) - 1059) := refute_e 1059 174 11 (by decide) (by decide)
theorem pk_1060 : ¬ Nat.Prime ((1060+1)^(Nat.totient (1408-1060)/2) - 1060) := refute_e 1060 56 3 (by decide) (by decide)
theorem pk_1061 : ¬ Nat.Prime ((1061+1)^(Nat.totient (1408-1061)/2) - 1061) := refute_e 1061 173 239 (by decide) (by decide)
theorem pk_1062 : ¬ Nat.Prime ((1062+1)^(Nat.totient (1408-1062)/2) - 1062) := refute_e 1062 86 13 (by decide) (by decide)
theorem pk_1063 : ¬ Nat.Prime ((1063+1)^(Nat.totient (1408-1063)/2) - 1063) := refute_e 1063 88 3 (by decide) (by decide)
theorem pk_1064 : ¬ Nat.Prime ((1064+1)^(Nat.totient (1408-1064)/2) - 1064) := refute_e 1064 84 101 (by decide) (by decide)
theorem pk_1065 : ¬ Nat.Prime ((1065+1)^(Nat.totient (1408-1065)/2) - 1065) := refute_e 1065 147 7 (by decide) (by decide)
theorem pk_1066 : ¬ Nat.Prime ((1066+1)^(Nat.totient (1408-1066)/2) - 1066) := refute_e 1066 54 3 (by decide) (by decide)
theorem pk_1067 : ¬ Nat.Prime ((1067+1)^(Nat.totient (1408-1067)/2) - 1067) := refute_e 1067 150 23 (by decide) (by decide)
theorem pk_1068 : ¬ Nat.Prime ((1068+1)^(Nat.totient (1408-1068)/2) - 1068) := refute_e 1068 64 157 (by decide) (by decide)
theorem pk_1069 : ¬ Nat.Prime ((1069+1)^(Nat.totient (1408-1069)/2) - 1069) := refute_e 1069 112 3 (by decide) (by decide)
theorem pk_1070 : ¬ Nat.Prime ((1070+1)^(Nat.totient (1408-1070)/2) - 1070) := refute_e 1070 78 31 (by decide) (by decide)
theorem pk_1071 : ¬ Nat.Prime ((1071+1)^(Nat.totient (1408-1071)/2) - 1071) := refute_e 1071 168 5 (by decide) (by decide)
theorem pk_1072 : ¬ Nat.Prime ((1072+1)^(Nat.totient (1408-1072)/2) - 1072) := refute_e 1072 48 3 (by decide) (by decide)
theorem pk_1073 : ¬ Nat.Prime ((1073+1)^(Nat.totient (1408-1073)/2) - 1073) := refute_e 1073 132 67 (by decide) (by decide)
theorem pk_1074 : ¬ Nat.Prime ((1074+1)^(Nat.totient (1408-1074)/2) - 1074) := refute_e 1074 83 19009 (by decide) (by decide)
theorem pk_1075 : ¬ Nat.Prime ((1075+1)^(Nat.totient (1408-1075)/2) - 1075) := refute_e 1075 108 3 (by decide) (by decide)
theorem pk_1076 : ¬ Nat.Prime ((1076+1)^(Nat.totient (1408-1076)/2) - 1076) := refute_e 1076 82 13 (by decide) (by decide)
theorem pk_1077 : ¬ Nat.Prime ((1077+1)^(Nat.totient (1408-1077)/2) - 1077) := refute_e 1077 165 11681 (by decide) (by decide)
theorem pk_1078 : ¬ Nat.Prime ((1078+1)^(Nat.totient (1408-1078)/2) - 1078) := refute_e 1078 40 3 (by decide) (by decide)
theorem pk_1079 : ¬ Nat.Prime ((1079+1)^(Nat.totient (1408-1079)/2) - 1079) := refute_e 1079 138 7 (by decide) (by decide)
theorem pk_1080 : ¬ Nat.Prime ((1080+1)^(Nat.totient (1408-1080)/2) - 1080) := refute_e 1080 80 7 (by decide) (by decide)
theorem pk_1081 : ¬ Nat.Prime ((1081+1)^(Nat.totient (1408-1081)/2) - 1081) := refute_e 1081 108 3 (by decide) (by decide)
theorem pk_1082 : ¬ Nat.Prime ((1082+1)^(Nat.totient (1408-1082)/2) - 1082) := refute_e 1082 81 101 (by decide) (by decide)
theorem pk_1083 : ¬ Nat.Prime ((1083+1)^(Nat.totient (1408-1083)/2) - 1083) := refute_e 1083 120 73405368036923751977033163299531 (by decide) (by decide)
theorem pk_1084 : ¬ Nat.Prime ((1084+1)^(Nat.totient (1408-1084)/2) - 1084) := refute_e 1084 54 3 (by decide) (by decide)
theorem pk_1085 : ¬ Nat.Prime ((1085+1)^(Nat.totient (1408-1085)/2) - 1085) := refute_e 1085 144 359 (by decide) (by decide)
theorem pk_1086 : ¬ Nat.Prime ((1086+1)^(Nat.totient (1408-1086)/2) - 1086) := refute_e 1086 66 7 (by decide) (by decide)
theorem pk_1087 : ¬ Nat.Prime ((1087+1)^(Nat.totient (1408-1087)/2) - 1087) := refute_e 1087 106 3 (by decide) (by decide)
theorem pk_1088 : ¬ Nat.Prime ((1088+1)^(Nat.totient (1408-1088)/2) - 1088) := refute_e 1088 64 67 (by decide) (by decide)
theorem pk_1089 : ¬ Nat.Prime ((1089+1)^(Nat.totient (1408-1089)/2) - 1089) := refute_e 1089 140 7 (by decide) (by decide)
theorem pk_1090 : ¬ Nat.Prime ((1090+1)^(Nat.totient (1408-1090)/2) - 1090) := refute_e 1090 52 3 (by decide) (by decide)
theorem pk_1091 : ¬ Nat.Prime ((1091+1)^(Nat.totient (1408-1091)/2) - 1091) := refute_e 1091 158 3559 (by decide) (by decide)
theorem pk_1092 : ¬ Nat.Prime ((1092+1)^(Nat.totient (1408-1092)/2) - 1092) := refute_e 1092 78 763105712885013172313 (by decide) (by decide)
theorem pk_1093 : ¬ Nat.Prime ((1093+1)^(Nat.totient (1408-1093)/2) - 1093) := refute_e 1093 72 3 (by decide) (by decide)
theorem pk_1094 : ¬ Nat.Prime ((1094+1)^(Nat.totient (1408-1094)/2) - 1094) := refute_e 1094 78 4127 (by decide) (by decide)
theorem pk_1095 : ¬ Nat.Prime ((1095+1)^(Nat.totient (1408-1095)/2) - 1095) := refute_e 1095 156 61 (by decide) (by decide)
theorem pk_1096 : ¬ Nat.Prime ((1096+1)^(Nat.totient (1408-1096)/2) - 1096) := refute_e 1096 48 3 (by decide) (by decide)
theorem pk_1097 : ¬ Nat.Prime ((1097+1)^(Nat.totient (1408-1097)/2) - 1097) := refute_e 1097 155 5 (by decide) (by decide)
theorem pk_1098 : ¬ Nat.Prime ((1098+1)^(Nat.totient (1408-1098)/2) - 1098) := refute_e 1098 60 1223 (by decide) (by decide)
theorem pk_1099 : ¬ Nat.Prime ((1099+1)^(Nat.totient (1408-1099)/2) - 1099) := refute_e 1099 102 3 (by decide) (by decide)
theorem pk_1100 : ¬ Nat.Prime ((1100+1)^(Nat.totient (1408-1100)/2) - 1100) := refute_e 1100 60 7 (by decide) (by decide)
theorem pk_1101 : ¬ Nat.Prime ((1101+1)^(Nat.totient (1408-1101)/2) - 1101) := refute_e 1101 153 61 (by decide) (by decide)
theorem pk_1102 : ¬ Nat.Prime ((1102+1)^(Nat.totient (1408-1102)/2) - 1102) := refute_e 1102 48 3 (by decide) (by decide)
theorem pk_1103 : ¬ Nat.Prime ((1103+1)^(Nat.totient (1408-1103)/2) - 1103) := refute_e 1103 120 3373 (by decide) (by decide)
theorem pk_1104 : ¬ Nat.Prime ((1104+1)^(Nat.totient (1408-1104)/2) - 1104) := refute_e 1104 72 53 (by decide) (by decide)
theorem pk_1105 : ¬ Nat.Prime ((1105+1)^(Nat.totient (1408-1105)/2) - 1105) := refute_e 1105 100 3 (by decide) (by decide)
theorem pk_1106 : ¬ Nat.Prime ((1106+1)^(Nat.totient (1408-1106)/2) - 1106) := refute_e 1106 75 71 (by decide) (by decide)
theorem pk_1107 : ¬ Nat.Prime ((1107+1)^(Nat.totient (1408-1107)/2) - 1107) := refute_e 1107 126 7 (by decide) (by decide)
theorem pk_1108 : ¬ Nat.Prime ((1108+1)^(Nat.totient (1408-1108)/2) - 1108) := refute_e 1108 40 3 (by decide) (by decide)
theorem pk_1109 : ¬ Nat.Prime ((1109+1)^(Nat.totient (1408-1109)/2) - 1109) := refute_e 1109 132 98638571312861 (by decide) (by decide)
theorem pk_1110 : ¬ Nat.Prime ((1110+1)^(Nat.totient (1408-1110)/2) - 1110) := refute_e 1110 74 7 (by decide) (by decide)
theorem pk_1111 : ¬ Nat.Prime ((1111+1)^(Nat.totient (1408-1111)/2) - 1111) := refute_e 1111 90 3 (by decide) (by decide)
theorem pk_1112 : ¬ Nat.Prime ((1112+1)^(Nat.totient (1408-1112)/2) - 1112) := refute_e 1112 72 107 (by decide) (by decide)
theorem pk_1113 : ¬ Nat.Prime ((1113+1)^(Nat.totient (1408-1113)/2) - 1113) := refute_e 1113 116 19 (by decide) (by decide)
theorem pk_1114 : ¬ Nat.Prime ((1114+1)^(Nat.totient (1408-1114)/2) - 1114) := refute_e 1114 42 3 (by decide) (by decide)
theorem pk_1115 : ¬ Nat.Prime ((1115+1)^(Nat.totient (1408-1115)/2) - 1115) := refute_e 1115 146 7 (by decide) (by decide)
theorem pk_1116 : ¬ Nat.Prime ((1116+1)^(Nat.totient (1408-1116)/2) - 1116) := refute_e 1116 72 5 (by decide) (by decide)
theorem pk_1117 : ¬ Nat.Prime ((1117+1)^(Nat.totient (1408-1117)/2) - 1117) := refute_e 1117 96 3 (by decide) (by decide)
theorem pk_1118 : ¬ Nat.Prime ((1118+1)^(Nat.totient (1408-1118)/2) - 1118) := refute_e 1118 56 1251043 (by decide) (by decide)
theorem pk_1119 : ¬ Nat.Prime ((1119+1)^(Nat.totient (1408-1119)/2) - 1119) := refute_e 1119 136 6131 (by decide) (by decide)
theorem pk_1120 : ¬ Nat.Prime ((1120+1)^(Nat.totient (1408-1120)/2) - 1120) := refute_e 1120 48 3 (by decide) (by decide)
theorem pk_1121 : ¬ Nat.Prime ((1121+1)^(Nat.totient (1408-1121)/2) - 1121) := refute_e 1121 120 5 (by decide) (by decide)
theorem pk_1122 : ¬ Nat.Prime ((1122+1)^(Nat.totient (1408-1122)/2) - 1122) := refute_e 1122 60 223 (by decide) (by decide)
theorem pk_1123 : ¬ Nat.Prime ((1123+1)^(Nat.totient (1408-1123)/2) - 1123) := refute_e 1123 72 3 (by decide) (by decide)
theorem pk_1124 : ¬ Nat.Prime ((1124+1)^(Nat.totient (1408-1124)/2) - 1124) := refute_e 1124 70 631 (by decide) (by decide)
theorem pk_1125 : ¬ Nat.Prime ((1125+1)^(Nat.totient (1408-1125)/2) - 1125) := refute_e 1125 141 4313093 (by decide) (by decide)
theorem pk_1126 : ¬ Nat.Prime ((1126+1)^(Nat.totient (1408-1126)/2) - 1126) := refute_e 1126 46 3 (by decide) (by decide)
theorem pk_1127 : ¬ Nat.Prime ((1127+1)^(Nat.totient (1408-1127)/2) - 1127) := refute_e 1127 140 13 (by decide) (by decide)
theorem pk_1128 : ¬ Nat.Prime ((1128+1)^(Nat.totient (1408-1128)/2) - 1128) := refute_e 1128 48 7 (by decide) (by decide)
theorem pk_1129 : ¬ Nat.Prime ((1129+1)^(Nat.totient (1408-1129)/2) - 1129) := refute_e 1129 90 3 (by decide) (by decide)
theorem pk_1130 : ¬ Nat.Prime ((1130+1)^(Nat.totient (1408-1130)/2) - 1130) := refute_e 1130 69 17 (by decide) (by decide)
theorem pk_1131 : ¬ Nat.Prime ((1131+1)^(Nat.totient (1408-1131)/2) - 1131) := refute_e 1131 138 2693 (by decide) (by decide)
theorem pk_1132 : ¬ Nat.Prime ((1132+1)^(Nat.totient (1408-1132)/2) - 1132) := refute_e 1132 44 3 (by decide) (by decide)
theorem pk_1133 : ¬ Nat.Prime ((1133+1)^(Nat.totient (1408-1133)/2) - 1133) := refute_fermat 1133 100 117287915790587077881728188211753003842400900325028084832838612612001116519913946937638600275806081183856392356077501848022631720264097822639681319378992548686054774651873402120863842087687101671498174298445545418197844578585544282415645504339243956504464518025357358486001165784238429079106028104686512991 (by decide) (by norm_num) (by norm_num) (by norm_num) (by decide) (by reduce_mod_char)
theorem pk_1134 : ¬ Nat.Prime ((1134+1)^(Nat.totient (1408-1134)/2) - 1134) := refute_e 1134 68 13 (by decide) (by decide)
theorem pk_1135 : ¬ Nat.Prime ((1135+1)^(Nat.totient (1408-1135)/2) - 1135) := refute_e 1135 72 3 (by decide) (by decide)
theorem pk_1136 : ¬ Nat.Prime ((1136+1)^(Nat.totient (1408-1136)/2) - 1136) := refute_e 1136 64 5 (by decide) (by decide)
theorem pk_1137 : ¬ Nat.Prime ((1137+1)^(Nat.totient (1408-1137)/2) - 1137) := refute_e 1137 135 5 (by decide) (by decide)
theorem pk_1138 : ¬ Nat.Prime ((1138+1)^(Nat.totient (1408-1138)/2) - 1138) := refute_e 1138 36 3 (by decide) (by decide)
theorem pk_1139 : ¬ Nat.Prime ((1139+1)^(Nat.totient (1408-1139)/2) - 1139) := refute_e 1139 134 43 (by decide) (by decide)
theorem pk_1140 : ¬ Nat.Prime ((1140+1)^(Nat.totient (1408-1140)/2) - 1140) := refute_e 1140 66 67 (by decide) (by decide)
theorem pk_1141 : ¬ Nat.Prime ((1141+1)^(Nat.totient (1408-1141)/2) - 1141) := refute_e 1141 88 3 (by decide) (by decide)
theorem pk_1142 : ¬ Nat.Prime ((1142+1)^(Nat.totient (1408-1142)/2) - 1142) := refute_e 1142 54 7 (by decide) (by decide)
theorem pk_1143 : ¬ Nat.Prime ((1143+1)^(Nat.totient (1408-1143)/2) - 1143) := refute_e 1143 104 7 (by decide) (by decide)
theorem pk_1144 : ¬ Nat.Prime ((1144+1)^(Nat.totient (1408-1144)/2) - 1144) := refute_e 1144 40 3 (by decide) (by decide)
theorem pk_1145 : ¬ Nat.Prime ((1145+1)^(Nat.totient (1408-1145)/2) - 1145) := refute_e 1145 131 19 (by decide) (by decide)
theorem pk_1146 : ¬ Nat.Prime ((1146+1)^(Nat.totient (1408-1146)/2) - 1146) := refute_e 1146 65 61 (by decide) (by decide)
theorem pk_1147 : ¬ Nat.Prime ((1147+1)^(Nat.totient (1408-1147)/2) - 1147) := refute_e 1147 84 3 (by decide) (by decide)
theorem pk_1148 : ¬ Nat.Prime ((1148+1)^(Nat.totient (1408-1148)/2) - 1148) := refute_e 1148 48 11 (by decide) (by decide)
theorem pk_1149 : ¬ Nat.Prime ((1149+1)^(Nat.totient (1408-1149)/2) - 1149) := refute_e 1149 108 7 (by decide) (by decide)
theorem pk_1150 : ¬ Nat.Prime ((1150+1)^(Nat.totient (1408-1150)/2) - 1150) := refute_e 1150 42 3 (by decide) (by decide)
theorem pk_1151 : ¬ Nat.Prime ((1151+1)^(Nat.totient (1408-1151)/2) - 1151) := refute_e 1151 128 5 (by decide) (by decide)
theorem pk_1152 : ¬ Nat.Prime ((1152+1)^(Nat.totient (1408-1152)/2) - 1152) := refute_e 1152 64 1487593 (by decide) (by decide)
theorem pk_1153 : ¬ Nat.Prime ((1153+1)^(Nat.totient (1408-1153)/2) - 1153) := refute_e 1153 64 3 (by decide) (by decide)
theorem pk_1154 : ¬ Nat.Prime ((1154+1)^(Nat.totient (1408-1154)/2) - 1154) := refute_e 1154 63 67 (by decide) (by decide)
theorem pk_1155 : ¬ Nat.Prime ((1155+1)^(Nat.totient (1408-1155)/2) - 1155) := refute_e 1155 110 1069 (by decide) (by decide)
theorem pk_1156 : ¬ Nat.Prime ((1156+1)^(Nat.totient (1408-1156)/2) - 1156) := refute_e 1156 36 3 (by decide) (by decide)
theorem pk_1157 : ¬ Nat.Prime ((1157+1)^(Nat.totient (1408-1157)/2) - 1157) := refute_e 1157 125 284580317591 (by decide) (by decide)
theorem pk_1158 : ¬ Nat.Prime ((1158+1)^(Nat.totient (1408-1158)/2) - 1158) := refute_e 1158 50 733 (by decide) (by decide)
theorem pk_1159 : ¬ Nat.Prime ((1159+1)^(Nat.totient (1408-1159)/2) - 1159) := refute_e 1159 82 3 (by decide) (by decide)
theorem pk_1160 : ¬ Nat.Prime ((1160+1)^(Nat.totient (1408-1160)/2) - 1160) := refute_e 1160 60 17 (by decide) (by decide)
theorem pk_1161 : ¬ Nat.Prime ((1161+1)^(Nat.totient (1408-1161)/2) - 1161) := refute_e 1161 108 5 (by decide) (by decide)
theorem pk_1162 : ¬ Nat.Prime ((1162+1)^(Nat.totient (1408-1162)/2) - 1162) := refute_e 1162 40 3 (by decide) (by decide)
theorem pk_1163 : ¬ Nat.Prime ((1163+1)^(Nat.totient (1408-1163)/2) - 1163) := refute_e 1163 84 7 (by decide) (by decide)
theorem pk_1164 : ¬ Nat.Prime ((1164+1)^(Nat.totient (1408-1164)/2) - 1164) := refute_e 1164 60 937 (by decide) (by decide)
theorem pk_1165 : ¬ Nat.Prime ((1165+1)^(Nat.totient (1408-1165)/2) - 1165) := refute_e 1165 81 210284093 (by decide) (by decide)
theorem pk_1166 : ¬ Nat.Prime ((1166+1)^(Nat.totient (1408-1166)/2) - 1166) := refute_e 1166 55 941 (by decide) (by decide)
theorem pk_1167 : ¬ Nat.Prime ((1167+1)^(Nat.totient (1408-1167)/2) - 1167) := refute_e 1167 120 11 (by decide) (by decide)
theorem pk_1168 : ¬ Nat.Prime ((1168+1)^(Nat.totient (1408-1168)/2) - 1168) := refute_e 1168 32 3 (by decide) (by decide)
theorem pk_1169 : ¬ Nat.Prime ((1169+1)^(Nat.totient (1408-1169)/2) - 1169) := refute_e 1169 119 11 (by decide) (by decide)
theorem pk_1170 : ¬ Nat.Prime ((1170+1)^(Nat.totient (1408-1170)/2) - 1170) := refute_e 1170 48 7 (by decide) (by decide)
theorem pk_1171 : ¬ Nat.Prime ((1171+1)^(Nat.totient (1408-1171)/2) - 1171) := refute_e 1171 78 3 (by decide) (by decide)
theorem pk_1172 : ¬ Nat.Prime ((1172+1)^(Nat.totient (1408-1172)/2) - 1172) := refute_e 1172 58 257 (by decide) (by decide)
theorem pk_1173 : ¬ Nat.Prime ((1173+1)^(Nat.totient (1408-1173)/2) - 1173) := refute_e 1173 92 7 (by decide) (by decide)
theorem pk_1174 : ¬ Nat.Prime ((1174+1)^(Nat.totient (1408-1174)/2) - 1174) := refute_e 1174 36 3 (by decide) (by decide)
theorem pk_1175 : ¬ Nat.Prime ((1175+1)^(Nat.totient (1408-1175)/2) - 1175) := refute_e 1175 116 151 (by decide) (by decide)
theorem pk_1176 : ¬ Nat.Prime ((1176+1)^(Nat.totient (1408-1176)/2) - 1176) := refute_e 1176 56 5 (by decide) (by decide)
theorem pk_1177 : ¬ Nat.Prime ((1177+1)^(Nat.totient (1408-1177)/2) - 1177) := refute_e 1177 60 3 (by decide) (by decide)
theorem pk_1178 : ¬ Nat.Prime ((1178+1)^(Nat.totient (1408-1178)/2) - 1178) := refute_e 1178 44 7 (by decide) (by decide)
theorem pk_1179 : ¬ Nat.Prime ((1179+1)^(Nat.totient (1408-1179)/2) - 1179) := refute_e 1179 114 34589 (by decide) (by decide)
theorem pk_1180 : ¬ Nat.Prime ((1180+1)^(Nat.totient (1408-1180)/2) - 1180) := refute_e 1180 36 3 (by decide) (by decide)
theorem pk_1181 : ¬ Nat.Prime ((1181+1)^(Nat.totient (1408-1181)/2) - 1181) := refute_e 1181 113 11 (by decide) (by decide)
theorem pk_1182 : ¬ Nat.Prime ((1182+1)^(Nat.totient (1408-1182)/2) - 1182) := refute_e 1182 56 11 (by decide) (by decide)
theorem pk_1183 : ¬ Nat.Prime ((1183+1)^(Nat.totient (1408-1183)/2) - 1183) := refute_e 1183 60 3 (by decide) (by decide)
theorem pk_1184 : ¬ Nat.Prime ((1184+1)^(Nat.totient (1408-1184)/2) - 1184) := refute_e 1184 48 7 (by decide) (by decide)
theorem pk_1185 : ¬ Nat.Prime ((1185+1)^(Nat.totient (1408-1185)/2) - 1185) := refute_e 1185 111 2873228025861587828906861 (by decide) (by decide)
theorem pk_1186 : ¬ Nat.Prime ((1186+1)^(Nat.totient (1408-1186)/2) - 1186) := refute_e 1186 36 3 (by decide) (by decide)
theorem pk_1187 : ¬ Nat.Prime ((1187+1)^(Nat.totient (1408-1187)/2) - 1187) := refute_e 1187 96 281 (by decide) (by decide)
theorem pk_1188 : ¬ Nat.Prime ((1188+1)^(Nat.totient (1408-1188)/2) - 1188) := refute_e 1188 40 149 (by decide) (by decide)
theorem pk_1189 : ¬ Nat.Prime ((1189+1)^(Nat.totient (1408-1189)/2) - 1189) := refute_e 1189 72 3 (by decide) (by decide)
theorem pk_1190 : ¬ Nat.Prime ((1190+1)^(Nat.totient (1408-1190)/2) - 1190) := refute_e 1190 54 12641 (by decide) (by decide)
theorem pk_1191 : ¬ Nat.Prime ((1191+1)^(Nat.totient (1408-1191)/2) - 1191) := refute_e 1191 90 7 (by decide) (by decide)
theorem pk_1192 : ¬ Nat.Prime ((1192+1)^(Nat.totient (1408-1192)/2) - 1192) := refute_e 1192 36 3 (by decide) (by decide)
theorem pk_1193 : ¬ Nat.Prime ((1193+1)^(Nat.totient (1408-1193)/2) - 1193) := refute_e 1193 84 79 (by decide) (by decide)
theorem pk_1194 : ¬ Nat.Prime ((1194+1)^(Nat.totient (1408-1194)/2) - 1194) := refute_e 1194 53 21841 (by decide) (by decide)
theorem pk_1195 : ¬ Nat.Prime ((1195+1)^(Nat.totient (1408-1195)/2) - 1195) := refute_e 1195 70 3 (by decide) (by decide)
theorem pk_1196 : ¬ Nat.Prime ((1196+1)^(Nat.totient (1408-1196)/2) - 1196) := refute_e 1196 52 5 (by decide) (by decide)
theorem pk_1197 : ¬ Nat.Prime ((1197+1)^(Nat.totient (1408-1197)/2) - 1197) := refute_e 1197 105 110933 (by decide) (by decide)
theorem pk_1198 : ¬ Nat.Prime ((1198+1)^(Nat.totient (1408-1198)/2) - 1198) := refute_e 1198 24 3 (by decide) (by decide)
theorem pk_1199 : ¬ Nat.Prime ((1199+1)^(Nat.totient (1408-1199)/2) - 1199) := refute_e 1199 90 14771 (by decide) (by decide)
theorem pk_1200 : ¬ Nat.Prime ((1200+1)^(Nat.totient (1408-1200)/2) - 1200) := refute_e 1200 48 23 (by decide) (by decide)
theorem pk_1201 : ¬ Nat.Prime ((1201+1)^(Nat.totient (1408-1201)/2) - 1201) := refute_e 1201 66 3 (by decide) (by decide)
theorem pk_1202 : ¬ Nat.Prime ((1202+1)^(Nat.totient (1408-1202)/2) - 1202) := refute_e 1202 51 5 (by decide) (by decide)
theorem pk_1203 : ¬ Nat.Prime ((1203+1)^(Nat.totient (1408-1203)/2) - 1203) := refute_e 1203 80 31 (by decide) (by decide)
theorem pk_1204 : ¬ Nat.Prime ((1204+1)^(Nat.totient (1408-1204)/2) - 1204) := refute_e 1204 32 3 (by decide) (by decide)
theorem pk_1205 : ¬ Nat.Prime ((1205+1)^(Nat.totient (1408-1205)/2) - 1205) := refute_e 1205 84 7 (by decide) (by decide)
theorem pk_1206 : ¬ Nat.Prime ((1206+1)^(Nat.totient (1408-1206)/2) - 1206) := refute_e 1206 50 7 (by decide) (by decide)
theorem pk_1207 : ¬ Nat.Prime ((1207+1)^(Nat.totient (1408-1207)/2) - 1207) := refute_e 1207 66 3 (by decide) (by decide)
theorem pk_1208 : ¬ Nat.Prime ((1208+1)^(Nat.totient (1408-1208)/2) - 1208) := refute_e 1208 40 17 (by decide) (by decide)
theorem pk_1209 : ¬ Nat.Prime ((1209+1)^(Nat.totient (1408-1209)/2) - 1209) := refute_e 1209 99 97 (by decide) (by decide)
theorem pk_1210 : ¬ Nat.Prime ((1210+1)^(Nat.totient (1408-1210)/2) - 1210) := refute_e 1210 30 3 (by decide) (by decide)
theorem pk_1211 : ¬ Nat.Prime ((1211+1)^(Nat.totient (1408-1211)/2) - 1211) := refute_e 1211 98 541 (by decide) (by decide)
theorem pk_1212 : ¬ Nat.Prime ((1212+1)^(Nat.totient (1408-1212)/2) - 1212) := refute_e 1212 42 7 (by decide) (by decide)
theorem pk_1213 : ¬ Nat.Prime ((1213+1)^(Nat.totient (1408-1213)/2) - 1213) := refute_e 1213 48 3 (by decide) (by decide)
theorem pk_1214 : ¬ Nat.Prime ((1214+1)^(Nat.totient (1408-1214)/2) - 1214) := refute_e 1214 48 11 (by decide) (by decide)
theorem pk_1215 : ¬ Nat.Prime ((1215+1)^(Nat.totient (1408-1215)/2) - 1215) := refute_e 1215 96 11 (by decide) (by decide)
theorem pk_1216 : ¬ Nat.Prime ((1216+1)^(Nat.totient (1408-1216)/2) - 1216) := refute_e 1216 32 3 (by decide) (by decide)
theorem pk_1217 : ¬ Nat.Prime ((1217+1)^(Nat.totient (1408-1217)/2) - 1217) := refute_e 1217 95 5 (by decide) (by decide)
theorem pk_1218 : ¬ Nat.Prime ((1218+1)^(Nat.totient (1408-1218)/2) - 1218) := refute_e 1218 36 1294987 (by decide) (by decide)
theorem pk_1219 : ¬ Nat.Prime ((1219+1)^(Nat.totient (1408-1219)/2) - 1219) := refute_e 1219 54 3 (by decide) (by decide)
theorem pk_1220 : ¬ Nat.Prime ((1220+1)^(Nat.totient (1408-1220)/2) - 1220) := refute_e 1220 46 2711 (by decide) (by decide)
theorem pk_1221 : ¬ Nat.Prime ((1221+1)^(Nat.totient (1408-1221)/2) - 1221) := refute_e 1221 80 5 (by decide) (by decide)
theorem pk_1222 : ¬ Nat.Prime ((1222+1)^(Nat.totient (1408-1222)/2) - 1222) := refute_e 1222 30 3 (by decide) (by decide)
theorem pk_1223 : ¬ Nat.Prime ((1223+1)^(Nat.totient (1408-1223)/2) - 1223) := refute_e 1223 72 13 (by decide) (by decide)
theorem pk_1224 : ¬ Nat.Prime ((1224+1)^(Nat.totient (1408-1224)/2) - 1224) := refute_e 1224 44 11 (by decide) (by decide)
theorem pk_1225 : ¬ Nat.Prime ((1225+1)^(Nat.totient (1408-1225)/2) - 1225) := refute_e 1225 60 3 (by decide) (by decide)
theorem pk_1226 : ¬ Nat.Prime ((1226+1)^(Nat.totient (1408-1226)/2) - 1226) := refute_e 1226 36 5 (by decide) (by decide)
theorem pk_1227 : ¬ Nat.Prime ((1227+1)^(Nat.totient (1408-1227)/2) - 1227) := refute_e 1227 90 21017 (by decide) (by decide)
theorem pk_1228 : ¬ Nat.Prime ((1228+1)^(Nat.totient (1408-1228)/2) - 1228) := refute_e 1228 24 3 (by decide) (by decide)
theorem pk_1229 : ¬ Nat.Prime ((1229+1)^(Nat.totient (1408-1229)/2) - 1229) := refute_e 1229 89 1097 (by decide) (by decide)
theorem pk_1230 : ¬ Nat.Prime ((1230+1)^(Nat.totient (1408-1230)/2) - 1230) := refute_e 1230 44 953 (by decide) (by decide)
theorem pk_1231 : ¬ Nat.Prime ((1231+1)^(Nat.totient (1408-1231)/2) - 1231) := refute_e 1231 58 3 (by decide) (by decide)
theorem pk_1232 : ¬ Nat.Prime ((1232+1)^(Nat.totient (1408-1232)/2) - 1232) := refute_e 1232 40 19 (by decide) (by decide)
theorem pk_1233 : ¬ Nat.Prime ((1233+1)^(Nat.totient (1408-1233)/2) - 1233) := refute_e 1233 60 7 (by decide) (by decide)
theorem pk_1234 : ¬ Nat.Prime ((1234+1)^(Nat.totient (1408-1234)/2) - 1234) := refute_e 1234 28 3 (by decide) (by decide)
theorem pk_1235 : ¬ Nat.Prime ((1235+1)^(Nat.totient (1408-1235)/2) - 1235) := refute_e 1235 86 23 (by decide) (by decide)
theorem pk_1236 : ¬ Nat.Prime ((1236+1)^(Nat.totient (1408-1236)/2) - 1236) := refute_e 1236 42 1229 (by decide) (by decide)
theorem pk_1237 : ¬ Nat.Prime ((1237+1)^(Nat.totient (1408-1237)/2) - 1237) := refute_e 1237 54 3 (by decide) (by decide)
theorem pk_1238 : ¬ Nat.Prime ((1238+1)^(Nat.totient (1408-1238)/2) - 1238) := refute_e 1238 32 13 (by decide) (by decide)
theorem pk_1239 : ¬ Nat.Prime ((1239+1)^(Nat.totient (1408-1239)/2) - 1239) := refute_e 1239 78 47 (by decide) (by decide)
theorem pk_1240 : ¬ Nat.Prime ((1240+1)^(Nat.totient (1408-1240)/2) - 1240) := refute_e 1240 24 3 (by decide) (by decide)
theorem pk_1241 : ¬ Nat.Prime ((1241+1)^(Nat.totient (1408-1241)/2) - 1241) := refute_e 1241 83 29 (by decide) (by decide)
theorem pk_1242 : ¬ Nat.Prime ((1242+1)^(Nat.totient (1408-1242)/2) - 1242) := refute_e 1242 41 197 (by decide) (by decide)
theorem pk_1243 : ¬ Nat.Prime ((1243+1)^(Nat.totient (1408-1243)/2) - 1243) := refute_e 1243 40 3 (by decide) (by decide)
theorem pk_1244 : ¬ Nat.Prime ((1244+1)^(Nat.totient (1408-1244)/2) - 1244) := refute_e 1244 40 11 (by decide) (by decide)
theorem pk_1245 : ¬ Nat.Prime ((1245+1)^(Nat.totient (1408-1245)/2) - 1245) := refute_e 1245 81 23 (by decide) (by decide)
theorem pk_1246 : ¬ Nat.Prime ((1246+1)^(Nat.totient (1408-1246)/2) - 1246) := refute_e 1246 27 17 (by decide) (by decide)
theorem pk_1247 : ¬ Nat.Prime ((1247+1)^(Nat.totient (1408-1247)/2) - 1247) := refute_e 1247 66 7 (by decide) (by decide)
theorem pk_1248 : ¬ Nat.Prime ((1248+1)^(Nat.totient (1408-1248)/2) - 1248) := refute_e 1248 32 7 (by decide) (by decide)
theorem pk_1249 : ¬ Nat.Prime ((1249+1)^(Nat.totient (1408-1249)/2) - 1249) := refute_e 1249 52 3 (by decide) (by decide)
theorem pk_1250 : ¬ Nat.Prime ((1250+1)^(Nat.totient (1408-1250)/2) - 1250) := refute_e 1250 39 11 (by decide) (by decide)
theorem pk_1251 : ¬ Nat.Prime ((1251+1)^(Nat.totient (1408-1251)/2) - 1251) := refute_e 1251 78 1691710977527 (by decide) (by decide)
theorem pk_1252 : ¬ Nat.Prime ((1252+1)^(Nat.totient (1408-1252)/2) - 1252) := refute_e 1252 24 3 (by decide) (by decide)
theorem pk_1253 : ¬ Nat.Prime ((1253+1)^(Nat.totient (1408-1253)/2) - 1253) := refute_e 1253 60 3932543 (by decide) (by decide)
theorem pk_1254 : ¬ Nat.Prime ((1254+1)^(Nat.totient (1408-1254)/2) - 1254) := refute_e 1254 30 7 (by decide) (by decide)
theorem pk_1255 : ¬ Nat.Prime ((1255+1)^(Nat.totient (1408-1255)/2) - 1255) := refute_e 1255 48 3 (by decide) (by decide)
theorem pk_1256 : ¬ Nat.Prime ((1256+1)^(Nat.totient (1408-1256)/2) - 1256) := refute_e 1256 36 5 (by decide) (by decide)
theorem pk_1257 : ¬ Nat.Prime ((1257+1)^(Nat.totient (1408-1257)/2) - 1257) := refute_e 1257 75 5 (by decide) (by decide)
theorem pk_1258 : ¬ Nat.Prime ((1258+1)^(Nat.totient (1408-1258)/2) - 1258) := refute_e 1258 20 3 (by decide) (by decide)
theorem pk_1259 : ¬ Nat.Prime ((1259+1)^(Nat.totient (1408-1259)/2) - 1259) := refute_e 1259 74 937 (by decide) (by decide)
theorem pk_1260 : ¬ Nat.Prime ((1260+1)^(Nat.totient (1408-1260)/2) - 1260) := refute_e 1260 36 23 (by decide) (by decide)
theorem pk_1261 : ¬ Nat.Prime ((1261+1)^(Nat.totient (1408-1261)/2) - 1261) := refute_e 1261 42 3 (by decide) (by decide)
theorem pk_1262 : ¬ Nat.Prime ((1262+1)^(Nat.totient (1408-1262)/2) - 1262) := refute_e 1262 36 13 (by decide) (by decide)
theorem pk_1263 : ¬ Nat.Prime ((1263+1)^(Nat.totient (1408-1263)/2) - 1263) := refute_e 1263 56 389 (by decide) (by decide)
theorem pk_1264 : ¬ Nat.Prime ((1264+1)^(Nat.totient (1408-1264)/2) - 1264) := refute_e 1264 24 3 (by decide) (by decide)
theorem pk_1265 : ¬ Nat.Prime ((1265+1)^(Nat.totient (1408-1265)/2) - 1265) := refute_e 1265 60 53 (by decide) (by decide)
theorem pk_1266 : ¬ Nat.Prime ((1266+1)^(Nat.totient (1408-1266)/2) - 1266) := refute_e 1266 35 43499 (by decide) (by decide)
theorem pk_1267 : ¬ Nat.Prime ((1267+1)^(Nat.totient (1408-1267)/2) - 1267) := refute_e 1267 46 3 (by decide) (by decide)
theorem pk_1268 : ¬ Nat.Prime ((1268+1)^(Nat.totient (1408-1268)/2) - 1268) := refute_e 1268 24 7 (by decide) (by decide)
theorem pk_1269 : ¬ Nat.Prime ((1269+1)^(Nat.totient (1408-1269)/2) - 1269) := refute_e 1269 69 53 (by decide) (by decide)
theorem pk_1270 : ¬ Nat.Prime ((1270+1)^(Nat.totient (1408-1270)/2) - 1270) := refute_e 1270 22 3 (by decide) (by decide)
theorem pk_1271 : ¬ Nat.Prime ((1271+1)^(Nat.totient (1408-1271)/2) - 1271) := refute_e 1271 68 5 (by decide) (by decide)
theorem pk_1272 : ¬ Nat.Prime ((1272+1)^(Nat.totient (1408-1272)/2) - 1272) := refute_e 1272 32 569 (by decide) (by decide)
theorem pk_1273 : ¬ Nat.Prime ((1273+1)^(Nat.totient (1408-1273)/2) - 1273) := refute_e 1273 36 3 (by decide) (by decide)
theorem pk_1274 : ¬ Nat.Prime ((1274+1)^(Nat.totient (1408-1274)/2) - 1274) := refute_e 1274 33 451186444545373833293 (by decide) (by decide)
theorem pk_1275 : ¬ Nat.Prime ((1275+1)^(Nat.totient (1408-1275)/2) - 1275) := refute_e 1275 54 7 (by decide) (by decide)
theorem pk_1276 : ¬ Nat.Prime ((1276+1)^(Nat.totient (1408-1276)/2) - 1276) := refute_e 1276 20 3 (by decide) (by decide)
theorem pk_1277 : ¬ Nat.Prime ((1277+1)^(Nat.totient (1408-1277)/2) - 1277) := refute_e 1277 65 80761 (by decide) (by decide)
theorem pk_1278 : ¬ Nat.Prime ((1278+1)^(Nat.totient (1408-1278)/2) - 1278) := refute_e 1278 24 74515751 (by decide) (by decide)
theorem pk_1279 : ¬ Nat.Prime ((1279+1)^(Nat.totient (1408-1279)/2) - 1279) := refute_e 1279 42 3 (by decide) (by decide)
theorem pk_1280 : ¬ Nat.Prime ((1280+1)^(Nat.totient (1408-1280)/2) - 1280) := refute_e 1280 32 19 (by decide) (by decide)
theorem pk_1281 : ¬ Nat.Prime ((1281+1)^(Nat.totient (1408-1281)/2) - 1281) := refute_e 1281 63 863 (by decide) (by decide)
theorem pk_1282 : ¬ Nat.Prime ((1282+1)^(Nat.totient (1408-1282)/2) - 1282) := refute_e 1282 18 3 (by decide) (by decide)
theorem pk_1283 : ¬ Nat.Prime ((1283+1)^(Nat.totient (1408-1283)/2) - 1283) := refute_e 1283 50 7 (by decide) (by decide)
theorem pk_1284 : ¬ Nat.Prime ((1284+1)^(Nat.totient (1408-1284)/2) - 1284) := refute_e 1284 30 27511909 (by decide) (by decide)
theorem pk_1285 : ¬ Nat.Prime ((1285+1)^(Nat.totient (1408-1285)/2) - 1285) := refute_e 1285 40 3 (by decide) (by decide)
theorem pk_1286 : ¬ Nat.Prime ((1286+1)^(Nat.totient (1408-1286)/2) - 1286) := refute_e 1286 30 1466243 (by decide) (by decide)
theorem pk_1287 : ¬ Nat.Prime ((1287+1)^(Nat.totient (1408-1287)/2) - 1287) := refute_e 1287 55 5 (by decide) (by decide)
theorem pk_1288 : ¬ Nat.Prime ((1288+1)^(Nat.totient (1408-1288)/2) - 1288) := refute_e 1288 16 3 (by decide) (by decide)
theorem pk_1289 : ¬ Nat.Prime ((1289+1)^(Nat.totient (1408-1289)/2) - 1289) := refute_e 1289 48 7 (by decide) (by decide)
theorem pk_1290 : ¬ Nat.Prime ((1290+1)^(Nat.totient (1408-1290)/2) - 1290) := refute_e 1290 29 11 (by decide) (by decide)
theorem pk_1291 : ¬ Nat.Prime ((1291+1)^(Nat.totient (1408-1291)/2) - 1291) := refute_e 1291 36 3 (by decide) (by decide)
theorem pk_1292 : ¬ Nat.Prime ((1292+1)^(Nat.totient (1408-1292)/2) - 1292) := refute_e 1292 28 101 (by decide) (by decide)
theorem pk_1293 : ¬ Nat.Prime ((1293+1)^(Nat.totient (1408-1293)/2) - 1293) := refute_e 1293 44 139 (by decide) (by decide)
theorem pk_1294 : ¬ Nat.Prime ((1294+1)^(Nat.totient (1408-1294)/2) - 1294) := refute_e 1294 18 3 (by decide) (by decide)
theorem pk_1295 : ¬ Nat.Prime ((1295+1)^(Nat.totient (1408-1295)/2) - 1295) := refute_e 1295 56 1678321 (by decide) (by decide)
theorem pk_1296 : ¬ Nat.Prime ((1296+1)^(Nat.totient (1408-1296)/2) - 1296) := refute_e 1296 24 5 (by decide) (by decide)
theorem pk_1297 : ¬ Nat.Prime ((1297+1)^(Nat.totient (1408-1297)/2) - 1297) := refute_e 1297 36 3 (by decide) (by decide)
theorem pk_1298 : ¬ Nat.Prime ((1298+1)^(Nat.totient (1408-1298)/2) - 1298) := refute_e 1298 20 73 (by decide) (by decide)
theorem pk_1299 : ¬ Nat.Prime ((1299+1)^(Nat.totient (1408-1299)/2) - 1299) := refute_e 1299 54 198212059701460634514491 (by decide) (by decide)
theorem pk_1300 : ¬ Nat.Prime ((1300+1)^(Nat.totient (1408-1300)/2) - 1300) := refute_e 1300 18 3 (by decide) (by decide)
theorem pk_1301 : ¬ Nat.Prime ((1301+1)^(Nat.totient (1408-1301)/2) - 1301) := refute_e 1301 53 241 (by decide) (by decide)
theorem pk_1302 : ¬ Nat.Prime ((1302+1)^(Nat.totient (1408-1302)/2) - 1302) := refute_e 1302 26 67 (by decide) (by decide)
theorem pk_1303 : ¬ Nat.Prime ((1303+1)^(Nat.totient (1408-1303)/2) - 1303) := refute_e 1303 24 3 (by decide) (by decide)
theorem pk_1304 : ¬ Nat.Prime ((1304+1)^(Nat.totient (1408-1304)/2) - 1304) := refute_e 1304 24 31 (by decide) (by decide)
theorem pk_1305 : ¬ Nat.Prime ((1305+1)^(Nat.totient (1408-1305)/2) - 1305) := refute_e 1305 51 107 (by decide) (by decide)
theorem pk_1306 : ¬ Nat.Prime ((1306+1)^(Nat.totient (1408-1306)/2) - 1306) := refute_e 1306 16 3 (by decide) (by decide)
theorem pk_1307 : ¬ Nat.Prime ((1307+1)^(Nat.totient (1408-1307)/2) - 1307) := refute_e 1307 50 31 (by decide) (by decide)
theorem pk_1308 : ¬ Nat.Prime ((1308+1)^(Nat.totient (1408-1308)/2) - 1308) := refute_e 1308 20 877 (by decide) (by decide)
theorem pk_1309 : ¬ Nat.Prime ((1309+1)^(Nat.totient (1408-1309)/2) - 1309) := refute_e 1309 30 3 (by decide) (by decide)
theorem pk_1310 : ¬ Nat.Prime ((1310+1)^(Nat.totient (1408-1310)/2) - 1310) := refute_e 1310 21 7 (by decide) (by decide)
theorem pk_1311 : ¬ Nat.Prime ((1311+1)^(Nat.totient (1408-1311)/2) - 1311) := refute_e 1311 48 5 (by decide) (by decide)
theorem pk_1312 : ¬ Nat.Prime ((1312+1)^(Nat.totient (1408-1312)/2) - 1312) := refute_e 1312 16 3 (by decide) (by decide)
theorem pk_1313 : ¬ Nat.Prime ((1313+1)^(Nat.totient (1408-1313)/2) - 1313) := refute_e 1313 36 131 (by decide) (by decide)
theorem pk_1314 : ¬ Nat.Prime ((1314+1)^(Nat.totient (1408-1314)/2) - 1314) := refute_e 1314 23 37 (by decide) (by decide)
theorem pk_1315 : ¬ Nat.Prime ((1315+1)^(Nat.totient (1408-1315)/2) - 1315) := refute_e 1315 30 3 (by decide) (by decide)
theorem pk_1316 : ¬ Nat.Prime ((1316+1)^(Nat.totient (1408-1316)/2) - 1316) := refute_e 1316 22 364943 (by decide) (by decide)
theorem pk_1317 : ¬ Nat.Prime ((1317+1)^(Nat.totient (1408-1317)/2) - 1317) := refute_e 1317 36 7 (by decide) (by decide)
theorem pk_1318 : ¬ Nat.Prime ((1318+1)^(Nat.totient (1408-1318)/2) - 1318) := refute_e 1318 12 3 (by decide) (by decide)
theorem pk_1319 : ¬ Nat.Prime ((1319+1)^(Nat.totient (1408-1319)/2) - 1319) := refute_e 1319 44 47 (by decide) (by decide)
theorem pk_1320 : ¬ Nat.Prime ((1320+1)^(Nat.totient (1408-1320)/2) - 1320) := refute_e 1320 20 7 (by decide) (by decide)
theorem pk_1321 : ¬ Nat.Prime ((1321+1)^(Nat.totient (1408-1321)/2) - 1321) := refute_e 1321 28 3 (by decide) (by decide)
theorem pk_1322 : ¬ Nat.Prime ((1322+1)^(Nat.totient (1408-1322)/2) - 1322) := refute_e 1322 21 11714264907223 (by decide) (by decide)
theorem pk_1323 : ¬ Nat.Prime ((1323+1)^(Nat.totient (1408-1323)/2) - 1323) := refute_e 1323 32 61 (by decide) (by decide)
theorem pk_1324 : ¬ Nat.Prime ((1324+1)^(Nat.totient (1408-1324)/2) - 1324) := refute_e 1324 12 3 (by decide) (by decide)
theorem pk_1325 : ¬ Nat.Prime ((1325+1)^(Nat.totient (1408-1325)/2) - 1325) := refute_e 1325 41 557 (by decide) (by decide)
theorem pk_1326 : ¬ Nat.Prime ((1326+1)^(Nat.totient (1408-1326)/2) - 1326) := refute_e 1326 20 5 (by decide) (by decide)
theorem pk_1327 : ¬ Nat.Prime ((1327+1)^(Nat.totient (1408-1327)/2) - 1327) := refute_e 1327 27 5 (by decide) (by decide)
theorem pk_1328 : ¬ Nat.Prime ((1328+1)^(Nat.totient (1408-1328)/2) - 1328) := refute_e 1328 16 37 (by decide) (by decide)
theorem pk_1329 : ¬ Nat.Prime ((1329+1)^(Nat.totient (1408-1329)/2) - 1329) := refute_e 1329 39 29 (by decide) (by decide)
theorem pk_1330 : ¬ Nat.Prime ((1330+1)^(Nat.totient (1408-1330)/2) - 1330) := refute_e 1330 12 3 (by decide) (by decide)
theorem pk_1331 : ¬ Nat.Prime ((1331+1)^(Nat.totient (1408-1331)/2) - 1331) := refute_e 1331 30 7 (by decide) (by decide)
theorem pk_1332 : ¬ Nat.Prime ((1332+1)^(Nat.totient (1408-1332)/2) - 1332) := refute_e 1332 18 1033 (by decide) (by decide)
theorem pk_1333 : ¬ Nat.Prime ((1333+1)^(Nat.totient (1408-1333)/2) - 1333) := refute_e 1333 20 3 (by decide) (by decide)
theorem pk_1334 : ¬ Nat.Prime ((1334+1)^(Nat.totient (1408-1334)/2) - 1334) := refute_e 1334 18 103668911 (by decide) (by decide)
theorem pk_1335 : ¬ Nat.Prime ((1335+1)^(Nat.totient (1408-1335)/2) - 1335) := refute_e 1335 36 10650259 (by decide) (by decide)
theorem pk_1336 : ¬ Nat.Prime ((1336+1)^(Nat.totient (1408-1336)/2) - 1336) := refute_e 1336 12 3 (by decide) (by decide)
theorem pk_1337 : ¬ Nat.Prime ((1337+1)^(Nat.totient (1408-1337)/2) - 1337) := refute_e 1337 35 5 (by decide) (by decide)
theorem pk_1338 : ¬ Nat.Prime ((1338+1)^(Nat.totient (1408-1338)/2) - 1338) := refute_e 1338 12 7 (by decide) (by decide)
theorem pk_1339 : ¬ Nat.Prime ((1339+1)^(Nat.totient (1408-1339)/2) - 1339) := refute_e 1339 22 3 (by decide) (by decide)
theorem pk_1340 : ¬ Nat.Prime ((1340+1)^(Nat.totient (1408-1340)/2) - 1340) := refute_e 1340 16 23 (by decide) (by decide)
theorem pk_1341 : ¬ Nat.Prime ((1341+1)^(Nat.totient (1408-1341)/2) - 1341) := refute_e 1341 33 7893378125707 (by decide) (by decide)
theorem pk_1342 : ¬ Nat.Prime ((1342+1)^(Nat.totient (1408-1342)/2) - 1342) := refute_e 1342 10 3 (by decide) (by decide)
theorem pk_1343 : ¬ Nat.Prime ((1343+1)^(Nat.totient (1408-1343)/2) - 1343) := refute_e 1343 24 89 (by decide) (by decide)
theorem pk_1344 : ¬ Nat.Prime ((1344+1)^(Nat.totient (1408-1344)/2) - 1344) := refute_e 1344 16 17 (by decide) (by decide)
theorem pk_1345 : ¬ Nat.Prime ((1345+1)^(Nat.totient (1408-1345)/2) - 1345) := refute_e 1345 18 3 (by decide) (by decide)
theorem pk_1346 : ¬ Nat.Prime ((1346+1)^(Nat.totient (1408-1346)/2) - 1346) := refute_e 1346 15 97 (by decide) (by decide)
theorem pk_1347 : ¬ Nat.Prime ((1347+1)^(Nat.totient (1408-1347)/2) - 1347) := refute_e 1347 30 23 (by decide) (by decide)
theorem pk_1348 : ¬ Nat.Prime ((1348+1)^(Nat.totient (1408-1348)/2) - 1348) := refute_e 1348 8 3 (by decide) (by decide)
theorem pk_1349 : ¬ Nat.Prime ((1349+1)^(Nat.totient (1408-1349)/2) - 1349) := refute_e 1349 29 11 (by decide) (by decide)
theorem pk_1350 : ¬ Nat.Prime ((1350+1)^(Nat.totient (1408-1350)/2) - 1350) := refute_e 1350 14 313 (by decide) (by decide)
theorem pk_1351 : ¬ Nat.Prime ((1351+1)^(Nat.totient (1408-1351)/2) - 1351) := refute_e 1351 18 3 (by decide) (by decide)
theorem pk_1352 : ¬ Nat.Prime ((1352+1)^(Nat.totient (1408-1352)/2) - 1352) := refute_e 1352 12 7 (by decide) (by decide)
theorem pk_1353 : ¬ Nat.Prime ((1353+1)^(Nat.totient (1408-1353)/2) - 1353) := refute_e 1353 20 7 (by decide) (by decide)
theorem pk_1354 : ¬ Nat.Prime ((1354+1)^(Nat.totient (1408-1354)/2) - 1354) := refute_e 1354 9 67 (by decide) (by decide)
theorem pk_1355 : ¬ Nat.Prime ((1355+1)^(Nat.totient (1408-1355)/2) - 1355) := refute_e 1355 26 7 (by decide) (by decide)
theorem pk_1356 : ¬ Nat.Prime ((1356+1)^(Nat.totient (1408-1356)/2) - 1356) := refute_e 1356 12 5 (by decide) (by decide)
theorem pk_1357 : ¬ Nat.Prime ((1357+1)^(Nat.totient (1408-1357)/2) - 1357) := refute_e 1357 16 3 (by decide) (by decide)
theorem pk_1358 : ¬ Nat.Prime ((1358+1)^(Nat.totient (1408-1358)/2) - 1358) := refute_e 1358 10 19 (by decide) (by decide)
theorem pk_1359 : ¬ Nat.Prime ((1359+1)^(Nat.totient (1408-1359)/2) - 1359) := refute_e 1359 21 7 (by decide) (by decide)
theorem pk_1360 : ¬ Nat.Prime ((1360+1)^(Nat.totient (1408-1360)/2) - 1360) := refute_e 1360 8 3 (by decide) (by decide)
theorem pk_1361 : ¬ Nat.Prime ((1361+1)^(Nat.totient (1408-1361)/2) - 1361) := refute_e 1361 23 8243 (by decide) (by decide)
theorem pk_1362 : ¬ Nat.Prime ((1362+1)^(Nat.totient (1408-1362)/2) - 1362) := refute_e 1362 11 5 (by decide) (by decide)
theorem pk_1363 : ¬ Nat.Prime ((1363+1)^(Nat.totient (1408-1363)/2) - 1363) := refute_e 1363 12 3 (by decide) (by decide)
theorem pk_1364 : ¬ Nat.Prime ((1364+1)^(Nat.totient (1408-1364)/2) - 1364) := refute_e 1364 10 9364666105667 (by decide) (by decide)
theorem pk_1365 : ¬ Nat.Prime ((1365+1)^(Nat.totient (1408-1365)/2) - 1365) := refute_e 1365 21 3077849 (by decide) (by decide)
theorem pk_1366 : ¬ Nat.Prime ((1366+1)^(Nat.totient (1408-1366)/2) - 1366) := refute_e 1366 6 3 (by decide) (by decide)
theorem pk_1367 : ¬ Nat.Prime ((1367+1)^(Nat.totient (1408-1367)/2) - 1367) := refute_e 1367 20 7 (by decide) (by decide)
theorem pk_1368 : ¬ Nat.Prime ((1368+1)^(Nat.totient (1408-1368)/2) - 1368) := refute_e 1368 8 11 (by decide) (by decide)
theorem pk_1369 : ¬ Nat.Prime ((1369+1)^(Nat.totient (1408-1369)/2) - 1369) := refute_e 1369 12 3 (by decide) (by decide)
theorem pk_1370 : ¬ Nat.Prime ((1370+1)^(Nat.totient (1408-1370)/2) - 1370) := refute_e 1370 9 13 (by decide) (by decide)
theorem pk_1371 : ¬ Nat.Prime ((1371+1)^(Nat.totient (1408-1371)/2) - 1371) := refute_e 1371 18 596845725974037610079 (by decide) (by decide)
theorem pk_1372 : ¬ Nat.Prime ((1372+1)^(Nat.totient (1408-1372)/2) - 1372) := refute_e 1372 6 3 (by decide) (by decide)
theorem pk_1373 : ¬ Nat.Prime ((1373+1)^(Nat.totient (1408-1373)/2) - 1373) := refute_e 1373 12 7 (by decide) (by decide)
theorem pk_1374 : ¬ Nat.Prime ((1374+1)^(Nat.totient (1408-1374)/2) - 1374) := refute_e 1374 8 7 (by decide) (by decide)
theorem pk_1375 : ¬ Nat.Prime ((1375+1)^(Nat.totient (1408-1375)/2) - 1375) := refute_e 1375 10 3 (by decide) (by decide)
theorem pk_1376 : ¬ Nat.Prime ((1376+1)^(Nat.totient (1408-1376)/2) - 1376) := refute_e 1376 8 5 (by decide) (by decide)
theorem pk_1377 : ¬ Nat.Prime ((1377+1)^(Nat.totient (1408-1377)/2) - 1377) := refute_e 1377 15 5 (by decide) (by decide)
theorem pk_1378 : ¬ Nat.Prime ((1378+1)^(Nat.totient (1408-1378)/2) - 1378) := refute_e 1378 4 3 (by decide) (by decide)
theorem pk_1379 : ¬ Nat.Prime ((1379+1)^(Nat.totient (1408-1379)/2) - 1379) := refute_e 1379 14 17 (by decide) (by decide)
theorem pk_1380 : ¬ Nat.Prime ((1380+1)^(Nat.totient (1408-1380)/2) - 1380) := refute_e 1380 6 7 (by decide) (by decide)
theorem pk_1381 : ¬ Nat.Prime ((1381+1)^(Nat.totient (1408-1381)/2) - 1381) := refute_e 1381 9 127 (by decide) (by decide)
theorem pk_1382 : ¬ Nat.Prime ((1382+1)^(Nat.totient (1408-1382)/2) - 1382) := refute_e 1382 6 2351 (by decide) (by decide)
theorem pk_1383 : ¬ Nat.Prime ((1383+1)^(Nat.totient (1408-1383)/2) - 1383) := refute_e 1383 10 3413 (by decide) (by decide)
theorem pk_1384 : ¬ Nat.Prime ((1384+1)^(Nat.totient (1408-1384)/2) - 1384) := refute_e 1384 4 3 (by decide) (by decide)
theorem pk_1385 : ¬ Nat.Prime ((1385+1)^(Nat.totient (1408-1385)/2) - 1385) := refute_e 1385 11 1597 (by decide) (by decide)
theorem pk_1386 : ¬ Nat.Prime ((1386+1)^(Nat.totient (1408-1386)/2) - 1386) := refute_e 1386 5 609743 (by decide) (by decide)
theorem pk_1387 : ¬ Nat.Prime ((1387+1)^(Nat.totient (1408-1387)/2) - 1387) := refute_e 1387 6 3 (by decide) (by decide)
theorem pk_1388 : ¬ Nat.Prime ((1388+1)^(Nat.totient (1408-1388)/2) - 1388) := refute_e 1388 4 223 (by decide) (by decide)
theorem pk_1389 : ¬ Nat.Prime ((1389+1)^(Nat.totient (1408-1389)/2) - 1389) := refute_e 1389 9 11 (by decide) (by decide)
theorem pk_1390 : ¬ Nat.Prime ((1390+1)^(Nat.totient (1408-1390)/2) - 1390) := refute_e 1390 3 11 (by decide) (by decide)
theorem pk_1391 : ¬ Nat.Prime ((1391+1)^(Nat.totient (1408-1391)/2) - 1391) := refute_e 1391 8 5 (by decide) (by decide)
theorem pk_1392 : ¬ Nat.Prime ((1392+1)^(Nat.totient (1408-1392)/2) - 1392) := refute_e 1392 4 83 (by decide) (by decide)
theorem pk_1393 : ¬ Nat.Prime ((1393+1)^(Nat.totient (1408-1393)/2) - 1393) := refute_e 1393 4 3 (by decide) (by decide)
theorem pk_1394 : ¬ Nat.Prime ((1394+1)^(Nat.totient (1408-1394)/2) - 1394) := refute_e 1394 3 7 (by decide) (by decide)
theorem pk_1395 : ¬ Nat.Prime ((1395+1)^(Nat.totient (1408-1395)/2) - 1395) := refute_e 1395 6 2417 (by decide) (by decide)
theorem pk_1396 : ¬ Nat.Prime ((1396+1)^(Nat.totient (1408-1396)/2) - 1396) := refute_e 1396 2 3 (by decide) (by decide)
theorem pk_1397 : ¬ Nat.Prime ((1397+1)^(Nat.totient (1408-1397)/2) - 1397) := refute_e 1397 5 53 (by decide) (by decide)
theorem pk_1398 : ¬ Nat.Prime ((1398+1)^(Nat.totient (1408-1398)/2) - 1398) := refute_e 1398 2 19 (by decide) (by decide)
theorem pk_1399 : ¬ Nat.Prime ((1399+1)^(Nat.totient (1408-1399)/2) - 1399) := refute_e 1399 3 19 (by decide) (by decide)
theorem pk_1400 : ¬ Nat.Prime ((1400+1)^(Nat.totient (1408-1400)/2) - 1400) := refute_e 1400 2 13 (by decide) (by decide)
theorem pk_1401 : ¬ Nat.Prime ((1401+1)^(Nat.totient (1408-1401)/2) - 1401) := refute_e 1401 3 7 (by decide) (by decide)
theorem pk_1402 : ¬ Nat.Prime ((1402+1)^(Nat.totient (1408-1402)/2) - 1402) := refute_triv 1402 1 (by decide) (by decide)
theorem pk_1403 : ¬ Nat.Prime ((1403+1)^(Nat.totient (1408-1403)/2) - 1403) := refute_e 1403 2 373 (by decide) (by decide)
theorem pk_1404 : ¬ Nat.Prime ((1404+1)^(Nat.totient (1408-1404)/2) - 1404) := refute_triv 1404 1 (by decide) (by decide)
theorem pk_1405 : ¬ Nat.Prime ((1405+1)^(Nat.totient (1408-1405)/2) - 1405) := refute_triv 1405 1 (by decide) (by decide)
theorem pk_1406 : ¬ Nat.Prime ((1406+1)^(Nat.totient (1408-1406)/2) - 1406) := refute_triv 1406 0 (by decide) (by decide)
theorem pk_1407 : ¬ Nat.Prime ((1407+1)^(Nat.totient (1408-1407)/2) - 1407) := refute_triv 1407 0 (by decide) (by decide)

theorem chunk_0 (k : ℕ) (h1 : 1 ≤ k) (h2 : k ≤ 100) : ¬ Nat.Prime ((k+1)^(Nat.totient (1408 - k)/2) - k) := by
  interval_cases k
  · exact pk_1
  · exact pk_2
  · exact pk_3
  · exact pk_4
  · exact pk_5
  · exact pk_6
  · exact pk_7
  · exact pk_8
  · exact pk_9
  · exact pk_10
  · exact pk_11
  · exact pk_12
  · exact pk_13
  · exact pk_14
  · exact pk_15
  · exact pk_16
  · exact pk_17
  · exact pk_18
  · exact pk_19
  · exact pk_20
  · exact pk_21
  · exact pk_22
  · exact pk_23
  · exact pk_24
  · exact pk_25
  · exact pk_26
  · exact pk_27
  · exact pk_28
  · exact pk_29
  · exact pk_30
  · exact pk_31
  · exact pk_32
  · exact pk_33
  · exact pk_34
  · exact pk_35
  · exact pk_36
  · exact pk_37
  · exact pk_38
  · exact pk_39
  · exact pk_40
  · exact pk_41
  · exact pk_42
  · exact pk_43
  · exact pk_44
  · exact pk_45
  · exact pk_46
  · exact pk_47
  · exact pk_48
  · exact pk_49
  · exact pk_50
  · exact pk_51
  · exact pk_52
  · exact pk_53
  · exact pk_54
  · exact pk_55
  · exact pk_56
  · exact pk_57
  · exact pk_58
  · exact pk_59
  · exact pk_60
  · exact pk_61
  · exact pk_62
  · exact pk_63
  · exact pk_64
  · exact pk_65
  · exact pk_66
  · exact pk_67
  · exact pk_68
  · exact pk_69
  · exact pk_70
  · exact pk_71
  · exact pk_72
  · exact pk_73
  · exact pk_74
  · exact pk_75
  · exact pk_76
  · exact pk_77
  · exact pk_78
  · exact pk_79
  · exact pk_80
  · exact pk_81
  · exact pk_82
  · exact pk_83
  · exact pk_84
  · exact pk_85
  · exact pk_86
  · exact pk_87
  · exact pk_88
  · exact pk_89
  · exact pk_90
  · exact pk_91
  · exact pk_92
  · exact pk_93
  · exact pk_94
  · exact pk_95
  · exact pk_96
  · exact pk_97
  · exact pk_98
  · exact pk_99
  · exact pk_100

theorem chunk_1 (k : ℕ) (h1 : 101 ≤ k) (h2 : k ≤ 200) : ¬ Nat.Prime ((k+1)^(Nat.totient (1408 - k)/2) - k) := by
  interval_cases k
  · exact pk_101
  · exact pk_102
  · exact pk_103
  · exact pk_104
  · exact pk_105
  · exact pk_106
  · exact pk_107
  · exact pk_108
  · exact pk_109
  · exact pk_110
  · exact pk_111
  · exact pk_112
  · exact pk_113
  · exact pk_114
  · exact pk_115
  · exact pk_116
  · exact pk_117
  · exact pk_118
  · exact pk_119
  · exact pk_120
  · exact pk_121
  · exact pk_122
  · exact pk_123
  · exact pk_124
  · exact pk_125
  · exact pk_126
  · exact pk_127
  · exact pk_128
  · exact pk_129
  · exact pk_130
  · exact pk_131
  · exact pk_132
  · exact pk_133
  · exact pk_134
  · exact pk_135
  · exact pk_136
  · exact pk_137
  · exact pk_138
  · exact pk_139
  · exact pk_140
  · exact pk_141
  · exact pk_142
  · exact pk_143
  · exact pk_144
  · exact pk_145
  · exact pk_146
  · exact pk_147
  · exact pk_148
  · exact pk_149
  · exact pk_150
  · exact pk_151
  · exact pk_152
  · exact pk_153
  · exact pk_154
  · exact pk_155
  · exact pk_156
  · exact pk_157
  · exact pk_158
  · exact pk_159
  · exact pk_160
  · exact pk_161
  · exact pk_162
  · exact pk_163
  · exact pk_164
  · exact pk_165
  · exact pk_166
  · exact pk_167
  · exact pk_168
  · exact pk_169
  · exact pk_170
  · exact pk_171
  · exact pk_172
  · exact pk_173
  · exact pk_174
  · exact pk_175
  · exact pk_176
  · exact pk_177
  · exact pk_178
  · exact pk_179
  · exact pk_180
  · exact pk_181
  · exact pk_182
  · exact pk_183
  · exact pk_184
  · exact pk_185
  · exact pk_186
  · exact pk_187
  · exact pk_188
  · exact pk_189
  · exact pk_190
  · exact pk_191
  · exact pk_192
  · exact pk_193
  · exact pk_194
  · exact pk_195
  · exact pk_196
  · exact pk_197
  · exact pk_198
  · exact pk_199
  · exact pk_200

theorem chunk_2 (k : ℕ) (h1 : 201 ≤ k) (h2 : k ≤ 300) : ¬ Nat.Prime ((k+1)^(Nat.totient (1408 - k)/2) - k) := by
  interval_cases k
  · exact pk_201
  · exact pk_202
  · exact pk_203
  · exact pk_204
  · exact pk_205
  · exact pk_206
  · exact pk_207
  · exact pk_208
  · exact pk_209
  · exact pk_210
  · exact pk_211
  · exact pk_212
  · exact pk_213
  · exact pk_214
  · exact pk_215
  · exact pk_216
  · exact pk_217
  · exact pk_218
  · exact pk_219
  · exact pk_220
  · exact pk_221
  · exact pk_222
  · exact pk_223
  · exact pk_224
  · exact pk_225
  · exact pk_226
  · exact pk_227
  · exact pk_228
  · exact pk_229
  · exact pk_230
  · exact pk_231
  · exact pk_232
  · exact pk_233
  · exact pk_234
  · exact pk_235
  · exact pk_236
  · exact pk_237
  · exact pk_238
  · exact pk_239
  · exact pk_240
  · exact pk_241
  · exact pk_242
  · exact pk_243
  · exact pk_244
  · exact pk_245
  · exact pk_246
  · exact pk_247
  · exact pk_248
  · exact pk_249
  · exact pk_250
  · exact pk_251
  · exact pk_252
  · exact pk_253
  · exact pk_254
  · exact pk_255
  · exact pk_256
  · exact pk_257
  · exact pk_258
  · exact pk_259
  · exact pk_260
  · exact pk_261
  · exact pk_262
  · exact pk_263
  · exact pk_264
  · exact pk_265
  · exact pk_266
  · exact pk_267
  · exact pk_268
  · exact pk_269
  · exact pk_270
  · exact pk_271
  · exact pk_272
  · exact pk_273
  · exact pk_274
  · exact pk_275
  · exact pk_276
  · exact pk_277
  · exact pk_278
  · exact pk_279
  · exact pk_280
  · exact pk_281
  · exact pk_282
  · exact pk_283
  · exact pk_284
  · exact pk_285
  · exact pk_286
  · exact pk_287
  · exact pk_288
  · exact pk_289
  · exact pk_290
  · exact pk_291
  · exact pk_292
  · exact pk_293
  · exact pk_294
  · exact pk_295
  · exact pk_296
  · exact pk_297
  · exact pk_298
  · exact pk_299
  · exact pk_300

theorem chunk_3 (k : ℕ) (h1 : 301 ≤ k) (h2 : k ≤ 400) : ¬ Nat.Prime ((k+1)^(Nat.totient (1408 - k)/2) - k) := by
  interval_cases k
  · exact pk_301
  · exact pk_302
  · exact pk_303
  · exact pk_304
  · exact pk_305
  · exact pk_306
  · exact pk_307
  · exact pk_308
  · exact pk_309
  · exact pk_310
  · exact pk_311
  · exact pk_312
  · exact pk_313
  · exact pk_314
  · exact pk_315
  · exact pk_316
  · exact pk_317
  · exact pk_318
  · exact pk_319
  · exact pk_320
  · exact pk_321
  · exact pk_322
  · exact pk_323
  · exact pk_324
  · exact pk_325
  · exact pk_326
  · exact pk_327
  · exact pk_328
  · exact pk_329
  · exact pk_330
  · exact pk_331
  · exact pk_332
  · exact pk_333
  · exact pk_334
  · exact pk_335
  · exact pk_336
  · exact pk_337
  · exact pk_338
  · exact pk_339
  · exact pk_340
  · exact pk_341
  · exact pk_342
  · exact pk_343
  · exact pk_344
  · exact pk_345
  · exact pk_346
  · exact pk_347
  · exact pk_348
  · exact pk_349
  · exact pk_350
  · exact pk_351
  · exact pk_352
  · exact pk_353
  · exact pk_354
  · exact pk_355
  · exact pk_356
  · exact pk_357
  · exact pk_358
  · exact pk_359
  · exact pk_360
  · exact pk_361
  · exact pk_362
  · exact pk_363
  · exact pk_364
  · exact pk_365
  · exact pk_366
  · exact pk_367
  · exact pk_368
  · exact pk_369
  · exact pk_370
  · exact pk_371
  · exact pk_372
  · exact pk_373
  · exact pk_374
  · exact pk_375
  · exact pk_376
  · exact pk_377
  · exact pk_378
  · exact pk_379
  · exact pk_380
  · exact pk_381
  · exact pk_382
  · exact pk_383
  · exact pk_384
  · exact pk_385
  · exact pk_386
  · exact pk_387
  · exact pk_388
  · exact pk_389
  · exact pk_390
  · exact pk_391
  · exact pk_392
  · exact pk_393
  · exact pk_394
  · exact pk_395
  · exact pk_396
  · exact pk_397
  · exact pk_398
  · exact pk_399
  · exact pk_400

theorem chunk_4 (k : ℕ) (h1 : 401 ≤ k) (h2 : k ≤ 500) : ¬ Nat.Prime ((k+1)^(Nat.totient (1408 - k)/2) - k) := by
  interval_cases k
  · exact pk_401
  · exact pk_402
  · exact pk_403
  · exact pk_404
  · exact pk_405
  · exact pk_406
  · exact pk_407
  · exact pk_408
  · exact pk_409
  · exact pk_410
  · exact pk_411
  · exact pk_412
  · exact pk_413
  · exact pk_414
  · exact pk_415
  · exact pk_416
  · exact pk_417
  · exact pk_418
  · exact pk_419
  · exact pk_420
  · exact pk_421
  · exact pk_422
  · exact pk_423
  · exact pk_424
  · exact pk_425
  · exact pk_426
  · exact pk_427
  · exact pk_428
  · exact pk_429
  · exact pk_430
  · exact pk_431
  · exact pk_432
  · exact pk_433
  · exact pk_434
  · exact pk_435
  · exact pk_436
  · exact pk_437
  · exact pk_438
  · exact pk_439
  · exact pk_440
  · exact pk_441
  · exact pk_442
  · exact pk_443
  · exact pk_444
  · exact pk_445
  · exact pk_446
  · exact pk_447
  · exact pk_448
  · exact pk_449
  · exact pk_450
  · exact pk_451
  · exact pk_452
  · exact pk_453
  · exact pk_454
  · exact pk_455
  · exact pk_456
  · exact pk_457
  · exact pk_458
  · exact pk_459
  · exact pk_460
  · exact pk_461
  · exact pk_462
  · exact pk_463
  · exact pk_464
  · exact pk_465
  · exact pk_466
  · exact pk_467
  · exact pk_468
  · exact pk_469
  · exact pk_470
  · exact pk_471
  · exact pk_472
  · exact pk_473
  · exact pk_474
  · exact pk_475
  · exact pk_476
  · exact pk_477
  · exact pk_478
  · exact pk_479
  · exact pk_480
  · exact pk_481
  · exact pk_482
  · exact pk_483
  · exact pk_484
  · exact pk_485
  · exact pk_486
  · exact pk_487
  · exact pk_488
  · exact pk_489
  · exact pk_490
  · exact pk_491
  · exact pk_492
  · exact pk_493
  · exact pk_494
  · exact pk_495
  · exact pk_496
  · exact pk_497
  · exact pk_498
  · exact pk_499
  · exact pk_500

theorem chunk_5 (k : ℕ) (h1 : 501 ≤ k) (h2 : k ≤ 600) : ¬ Nat.Prime ((k+1)^(Nat.totient (1408 - k)/2) - k) := by
  interval_cases k
  · exact pk_501
  · exact pk_502
  · exact pk_503
  · exact pk_504
  · exact pk_505
  · exact pk_506
  · exact pk_507
  · exact pk_508
  · exact pk_509
  · exact pk_510
  · exact pk_511
  · exact pk_512
  · exact pk_513
  · exact pk_514
  · exact pk_515
  · exact pk_516
  · exact pk_517
  · exact pk_518
  · exact pk_519
  · exact pk_520
  · exact pk_521
  · exact pk_522
  · exact pk_523
  · exact pk_524
  · exact pk_525
  · exact pk_526
  · exact pk_527
  · exact pk_528
  · exact pk_529
  · exact pk_530
  · exact pk_531
  · exact pk_532
  · exact pk_533
  · exact pk_534
  · exact pk_535
  · exact pk_536
  · exact pk_537
  · exact pk_538
  · exact pk_539
  · exact pk_540
  · exact pk_541
  · exact pk_542
  · exact pk_543
  · exact pk_544
  · exact pk_545
  · exact pk_546
  · exact pk_547
  · exact pk_548
  · exact pk_549
  · exact pk_550
  · exact pk_551
  · exact pk_552
  · exact pk_553
  · exact pk_554
  · exact pk_555
  · exact pk_556
  · exact pk_557
  · exact pk_558
  · exact pk_559
  · exact pk_560
  · exact pk_561
  · exact pk_562
  · exact pk_563
  · exact pk_564
  · exact pk_565
  · exact pk_566
  · exact pk_567
  · exact pk_568
  · exact pk_569
  · exact pk_570
  · exact pk_571
  · exact pk_572
  · exact pk_573
  · exact pk_574
  · exact pk_575
  · exact pk_576
  · exact pk_577
  · exact pk_578
  · exact pk_579
  · exact pk_580
  · exact pk_581
  · exact pk_582
  · exact pk_583
  · exact pk_584
  · exact pk_585
  · exact pk_586
  · exact pk_587
  · exact pk_588
  · exact pk_589
  · exact pk_590
  · exact pk_591
  · exact pk_592
  · exact pk_593
  · exact pk_594
  · exact pk_595
  · exact pk_596
  · exact pk_597
  · exact pk_598
  · exact pk_599
  · exact pk_600

theorem chunk_6 (k : ℕ) (h1 : 601 ≤ k) (h2 : k ≤ 700) : ¬ Nat.Prime ((k+1)^(Nat.totient (1408 - k)/2) - k) := by
  interval_cases k
  · exact pk_601
  · exact pk_602
  · exact pk_603
  · exact pk_604
  · exact pk_605
  · exact pk_606
  · exact pk_607
  · exact pk_608
  · exact pk_609
  · exact pk_610
  · exact pk_611
  · exact pk_612
  · exact pk_613
  · exact pk_614
  · exact pk_615
  · exact pk_616
  · exact pk_617
  · exact pk_618
  · exact pk_619
  · exact pk_620
  · exact pk_621
  · exact pk_622
  · exact pk_623
  · exact pk_624
  · exact pk_625
  · exact pk_626
  · exact pk_627
  · exact pk_628
  · exact pk_629
  · exact pk_630
  · exact pk_631
  · exact pk_632
  · exact pk_633
  · exact pk_634
  · exact pk_635
  · exact pk_636
  · exact pk_637
  · exact pk_638
  · exact pk_639
  · exact pk_640
  · exact pk_641
  · exact pk_642
  · exact pk_643
  · exact pk_644
  · exact pk_645
  · exact pk_646
  · exact pk_647
  · exact pk_648
  · exact pk_649
  · exact pk_650
  · exact pk_651
  · exact pk_652
  · exact pk_653
  · exact pk_654
  · exact pk_655
  · exact pk_656
  · exact pk_657
  · exact pk_658
  · exact pk_659
  · exact pk_660
  · exact pk_661
  · exact pk_662
  · exact pk_663
  · exact pk_664
  · exact pk_665
  · exact pk_666
  · exact pk_667
  · exact pk_668
  · exact pk_669
  · exact pk_670
  · exact pk_671
  · exact pk_672
  · exact pk_673
  · exact pk_674
  · exact pk_675
  · exact pk_676
  · exact pk_677
  · exact pk_678
  · exact pk_679
  · exact pk_680
  · exact pk_681
  · exact pk_682
  · exact pk_683
  · exact pk_684
  · exact pk_685
  · exact pk_686
  · exact pk_687
  · exact pk_688
  · exact pk_689
  · exact pk_690
  · exact pk_691
  · exact pk_692
  · exact pk_693
  · exact pk_694
  · exact pk_695
  · exact pk_696
  · exact pk_697
  · exact pk_698
  · exact pk_699
  · exact pk_700

theorem chunk_7 (k : ℕ) (h1 : 701 ≤ k) (h2 : k ≤ 800) : ¬ Nat.Prime ((k+1)^(Nat.totient (1408 - k)/2) - k) := by
  interval_cases k
  · exact pk_701
  · exact pk_702
  · exact pk_703
  · exact pk_704
  · exact pk_705
  · exact pk_706
  · exact pk_707
  · exact pk_708
  · exact pk_709
  · exact pk_710
  · exact pk_711
  · exact pk_712
  · exact pk_713
  · exact pk_714
  · exact pk_715
  · exact pk_716
  · exact pk_717
  · exact pk_718
  · exact pk_719
  · exact pk_720
  · exact pk_721
  · exact pk_722
  · exact pk_723
  · exact pk_724
  · exact pk_725
  · exact pk_726
  · exact pk_727
  · exact pk_728
  · exact pk_729
  · exact pk_730
  · exact pk_731
  · exact pk_732
  · exact pk_733
  · exact pk_734
  · exact pk_735
  · exact pk_736
  · exact pk_737
  · exact pk_738
  · exact pk_739
  · exact pk_740
  · exact pk_741
  · exact pk_742
  · exact pk_743
  · exact pk_744
  · exact pk_745
  · exact pk_746
  · exact pk_747
  · exact pk_748
  · exact pk_749
  · exact pk_750
  · exact pk_751
  · exact pk_752
  · exact pk_753
  · exact pk_754
  · exact pk_755
  · exact pk_756
  · exact pk_757
  · exact pk_758
  · exact pk_759
  · exact pk_760
  · exact pk_761
  · exact pk_762
  · exact pk_763
  · exact pk_764
  · exact pk_765
  · exact pk_766
  · exact pk_767
  · exact pk_768
  · exact pk_769
  · exact pk_770
  · exact pk_771
  · exact pk_772
  · exact pk_773
  · exact pk_774
  · exact pk_775
  · exact pk_776
  · exact pk_777
  · exact pk_778
  · exact pk_779
  · exact pk_780
  · exact pk_781
  · exact pk_782
  · exact pk_783
  · exact pk_784
  · exact pk_785
  · exact pk_786
  · exact pk_787
  · exact pk_788
  · exact pk_789
  · exact pk_790
  · exact pk_791
  · exact pk_792
  · exact pk_793
  · exact pk_794
  · exact pk_795
  · exact pk_796
  · exact pk_797
  · exact pk_798
  · exact pk_799
  · exact pk_800

theorem chunk_8 (k : ℕ) (h1 : 801 ≤ k) (h2 : k ≤ 900) : ¬ Nat.Prime ((k+1)^(Nat.totient (1408 - k)/2) - k) := by
  interval_cases k
  · exact pk_801
  · exact pk_802
  · exact pk_803
  · exact pk_804
  · exact pk_805
  · exact pk_806
  · exact pk_807
  · exact pk_808
  · exact pk_809
  · exact pk_810
  · exact pk_811
  · exact pk_812
  · exact pk_813
  · exact pk_814
  · exact pk_815
  · exact pk_816
  · exact pk_817
  · exact pk_818
  · exact pk_819
  · exact pk_820
  · exact pk_821
  · exact pk_822
  · exact pk_823
  · exact pk_824
  · exact pk_825
  · exact pk_826
  · exact pk_827
  · exact pk_828
  · exact pk_829
  · exact pk_830
  · exact pk_831
  · exact pk_832
  · exact pk_833
  · exact pk_834
  · exact pk_835
  · exact pk_836
  · exact pk_837
  · exact pk_838
  · exact pk_839
  · exact pk_840
  · exact pk_841
  · exact pk_842
  · exact pk_843
  · exact pk_844
  · exact pk_845
  · exact pk_846
  · exact pk_847
  · exact pk_848
  · exact pk_849
  · exact pk_850
  · exact pk_851
  · exact pk_852
  · exact pk_853
  · exact pk_854
  · exact pk_855
  · exact pk_856
  · exact pk_857
  · exact pk_858
  · exact pk_859
  · exact pk_860
  · exact pk_861
  · exact pk_862
  · exact pk_863
  · exact pk_864
  · exact pk_865
  · exact pk_866
  · exact pk_867
  · exact pk_868
  · exact pk_869
  · exact pk_870
  · exact pk_871
  · exact pk_872
  · exact pk_873
  · exact pk_874
  · exact pk_875
  · exact pk_876
  · exact pk_877
  · exact pk_878
  · exact pk_879
  · exact pk_880
  · exact pk_881
  · exact pk_882
  · exact pk_883
  · exact pk_884
  · exact pk_885
  · exact pk_886
  · exact pk_887
  · exact pk_888
  · exact pk_889
  · exact pk_890
  · exact pk_891
  · exact pk_892
  · exact pk_893
  · exact pk_894
  · exact pk_895
  · exact pk_896
  · exact pk_897
  · exact pk_898
  · exact pk_899
  · exact pk_900

theorem chunk_9 (k : ℕ) (h1 : 901 ≤ k) (h2 : k ≤ 1000) : ¬ Nat.Prime ((k+1)^(Nat.totient (1408 - k)/2) - k) := by
  interval_cases k
  · exact pk_901
  · exact pk_902
  · exact pk_903
  · exact pk_904
  · exact pk_905
  · exact pk_906
  · exact pk_907
  · exact pk_908
  · exact pk_909
  · exact pk_910
  · exact pk_911
  · exact pk_912
  · exact pk_913
  · exact pk_914
  · exact pk_915
  · exact pk_916
  · exact pk_917
  · exact pk_918
  · exact pk_919
  · exact pk_920
  · exact pk_921
  · exact pk_922
  · exact pk_923
  · exact pk_924
  · exact pk_925
  · exact pk_926
  · exact pk_927
  · exact pk_928
  · exact pk_929
  · exact pk_930
  · exact pk_931
  · exact pk_932
  · exact pk_933
  · exact pk_934
  · exact pk_935
  · exact pk_936
  · exact pk_937
  · exact pk_938
  · exact pk_939
  · exact pk_940
  · exact pk_941
  · exact pk_942
  · exact pk_943
  · exact pk_944
  · exact pk_945
  · exact pk_946
  · exact pk_947
  · exact pk_948
  · exact pk_949
  · exact pk_950
  · exact pk_951
  · exact pk_952
  · exact pk_953
  · exact pk_954
  · exact pk_955
  · exact pk_956
  · exact pk_957
  · exact pk_958
  · exact pk_959
  · exact pk_960
  · exact pk_961
  · exact pk_962
  · exact pk_963
  · exact pk_964
  · exact pk_965
  · exact pk_966
  · exact pk_967
  · exact pk_968
  · exact pk_969
  · exact pk_970
  · exact pk_971
  · exact pk_972
  · exact pk_973
  · exact pk_974
  · exact pk_975
  · exact pk_976
  · exact pk_977
  · exact pk_978
  · exact pk_979
  · exact pk_980
  · exact pk_981
  · exact pk_982
  · exact pk_983
  · exact pk_984
  · exact pk_985
  · exact pk_986
  · exact pk_987
  · exact pk_988
  · exact pk_989
  · exact pk_990
  · exact pk_991
  · exact pk_992
  · exact pk_993
  · exact pk_994
  · exact pk_995
  · exact pk_996
  · exact pk_997
  · exact pk_998
  · exact pk_999
  · exact pk_1000

theorem chunk_10 (k : ℕ) (h1 : 1001 ≤ k) (h2 : k ≤ 1100) : ¬ Nat.Prime ((k+1)^(Nat.totient (1408 - k)/2) - k) := by
  interval_cases k
  · exact pk_1001
  · exact pk_1002
  · exact pk_1003
  · exact pk_1004
  · exact pk_1005
  · exact pk_1006
  · exact pk_1007
  · exact pk_1008
  · exact pk_1009
  · exact pk_1010
  · exact pk_1011
  · exact pk_1012
  · exact pk_1013
  · exact pk_1014
  · exact pk_1015
  · exact pk_1016
  · exact pk_1017
  · exact pk_1018
  · exact pk_1019
  · exact pk_1020
  · exact pk_1021
  · exact pk_1022
  · exact pk_1023
  · exact pk_1024
  · exact pk_1025
  · exact pk_1026
  · exact pk_1027
  · exact pk_1028
  · exact pk_1029
  · exact pk_1030
  · exact pk_1031
  · exact pk_1032
  · exact pk_1033
  · exact pk_1034
  · exact pk_1035
  · exact pk_1036
  · exact pk_1037
  · exact pk_1038
  · exact pk_1039
  · exact pk_1040
  · exact pk_1041
  · exact pk_1042
  · exact pk_1043
  · exact pk_1044
  · exact pk_1045
  · exact pk_1046
  · exact pk_1047
  · exact pk_1048
  · exact pk_1049
  · exact pk_1050
  · exact pk_1051
  · exact pk_1052
  · exact pk_1053
  · exact pk_1054
  · exact pk_1055
  · exact pk_1056
  · exact pk_1057
  · exact pk_1058
  · exact pk_1059
  · exact pk_1060
  · exact pk_1061
  · exact pk_1062
  · exact pk_1063
  · exact pk_1064
  · exact pk_1065
  · exact pk_1066
  · exact pk_1067
  · exact pk_1068
  · exact pk_1069
  · exact pk_1070
  · exact pk_1071
  · exact pk_1072
  · exact pk_1073
  · exact pk_1074
  · exact pk_1075
  · exact pk_1076
  · exact pk_1077
  · exact pk_1078
  · exact pk_1079
  · exact pk_1080
  · exact pk_1081
  · exact pk_1082
  · exact pk_1083
  · exact pk_1084
  · exact pk_1085
  · exact pk_1086
  · exact pk_1087
  · exact pk_1088
  · exact pk_1089
  · exact pk_1090
  · exact pk_1091
  · exact pk_1092
  · exact pk_1093
  · exact pk_1094
  · exact pk_1095
  · exact pk_1096
  · exact pk_1097
  · exact pk_1098
  · exact pk_1099
  · exact pk_1100

theorem chunk_11 (k : ℕ) (h1 : 1101 ≤ k) (h2 : k ≤ 1200) : ¬ Nat.Prime ((k+1)^(Nat.totient (1408 - k)/2) - k) := by
  interval_cases k
  · exact pk_1101
  · exact pk_1102
  · exact pk_1103
  · exact pk_1104
  · exact pk_1105
  · exact pk_1106
  · exact pk_1107
  · exact pk_1108
  · exact pk_1109
  · exact pk_1110
  · exact pk_1111
  · exact pk_1112
  · exact pk_1113
  · exact pk_1114
  · exact pk_1115
  · exact pk_1116
  · exact pk_1117
  · exact pk_1118
  · exact pk_1119
  · exact pk_1120
  · exact pk_1121
  · exact pk_1122
  · exact pk_1123
  · exact pk_1124
  · exact pk_1125
  · exact pk_1126
  · exact pk_1127
  · exact pk_1128
  · exact pk_1129
  · exact pk_1130
  · exact pk_1131
  · exact pk_1132
  · exact pk_1133
  · exact pk_1134
  · exact pk_1135
  · exact pk_1136
  · exact pk_1137
  · exact pk_1138
  · exact pk_1139
  · exact pk_1140
  · exact pk_1141
  · exact pk_1142
  · exact pk_1143
  · exact pk_1144
  · exact pk_1145
  · exact pk_1146
  · exact pk_1147
  · exact pk_1148
  · exact pk_1149
  · exact pk_1150
  · exact pk_1151
  · exact pk_1152
  · exact pk_1153
  · exact pk_1154
  · exact pk_1155
  · exact pk_1156
  · exact pk_1157
  · exact pk_1158
  · exact pk_1159
  · exact pk_1160
  · exact pk_1161
  · exact pk_1162
  · exact pk_1163
  · exact pk_1164
  · exact pk_1165
  · exact pk_1166
  · exact pk_1167
  · exact pk_1168
  · exact pk_1169
  · exact pk_1170
  · exact pk_1171
  · exact pk_1172
  · exact pk_1173
  · exact pk_1174
  · exact pk_1175
  · exact pk_1176
  · exact pk_1177
  · exact pk_1178
  · exact pk_1179
  · exact pk_1180
  · exact pk_1181
  · exact pk_1182
  · exact pk_1183
  · exact pk_1184
  · exact pk_1185
  · exact pk_1186
  · exact pk_1187
  · exact pk_1188
  · exact pk_1189
  · exact pk_1190
  · exact pk_1191
  · exact pk_1192
  · exact pk_1193
  · exact pk_1194
  · exact pk_1195
  · exact pk_1196
  · exact pk_1197
  · exact pk_1198
  · exact pk_1199
  · exact pk_1200

theorem chunk_12 (k : ℕ) (h1 : 1201 ≤ k) (h2 : k ≤ 1300) : ¬ Nat.Prime ((k+1)^(Nat.totient (1408 - k)/2) - k) := by
  interval_cases k
  · exact pk_1201
  · exact pk_1202
  · exact pk_1203
  · exact pk_1204
  · exact pk_1205
  · exact pk_1206
  · exact pk_1207
  · exact pk_1208
  · exact pk_1209
  · exact pk_1210
  · exact pk_1211
  · exact pk_1212
  · exact pk_1213
  · exact pk_1214
  · exact pk_1215
  · exact pk_1216
  · exact pk_1217
  · exact pk_1218
  · exact pk_1219
  · exact pk_1220
  · exact pk_1221
  · exact pk_1222
  · exact pk_1223
  · exact pk_1224
  · exact pk_1225
  · exact pk_1226
  · exact pk_1227
  · exact pk_1228
  · exact pk_1229
  · exact pk_1230
  · exact pk_1231
  · exact pk_1232
  · exact pk_1233
  · exact pk_1234
  · exact pk_1235
  · exact pk_1236
  · exact pk_1237
  · exact pk_1238
  · exact pk_1239
  · exact pk_1240
  · exact pk_1241
  · exact pk_1242
  · exact pk_1243
  · exact pk_1244
  · exact pk_1245
  · exact pk_1246
  · exact pk_1247
  · exact pk_1248
  · exact pk_1249
  · exact pk_1250
  · exact pk_1251
  · exact pk_1252
  · exact pk_1253
  · exact pk_1254
  · exact pk_1255
  · exact pk_1256
  · exact pk_1257
  · exact pk_1258
  · exact pk_1259
  · exact pk_1260
  · exact pk_1261
  · exact pk_1262
  · exact pk_1263
  · exact pk_1264
  · exact pk_1265
  · exact pk_1266
  · exact pk_1267
  · exact pk_1268
  · exact pk_1269
  · exact pk_1270
  · exact pk_1271
  · exact pk_1272
  · exact pk_1273
  · exact pk_1274
  · exact pk_1275
  · exact pk_1276
  · exact pk_1277
  · exact pk_1278
  · exact pk_1279
  · exact pk_1280
  · exact pk_1281
  · exact pk_1282
  · exact pk_1283
  · exact pk_1284
  · exact pk_1285
  · exact pk_1286
  · exact pk_1287
  · exact pk_1288
  · exact pk_1289
  · exact pk_1290
  · exact pk_1291
  · exact pk_1292
  · exact pk_1293
  · exact pk_1294
  · exact pk_1295
  · exact pk_1296
  · exact pk_1297
  · exact pk_1298
  · exact pk_1299
  · exact pk_1300

theorem chunk_13 (k : ℕ) (h1 : 1301 ≤ k) (h2 : k ≤ 1400) : ¬ Nat.Prime ((k+1)^(Nat.totient (1408 - k)/2) - k) := by
  interval_cases k
  · exact pk_1301
  · exact pk_1302
  · exact pk_1303
  · exact pk_1304
  · exact pk_1305
  · exact pk_1306
  · exact pk_1307
  · exact pk_1308
  · exact pk_1309
  · exact pk_1310
  · exact pk_1311
  · exact pk_1312
  · exact pk_1313
  · exact pk_1314
  · exact pk_1315
  · exact pk_1316
  · exact pk_1317
  · exact pk_1318
  · exact pk_1319
  · exact pk_1320
  · exact pk_1321
  · exact pk_1322
  · exact pk_1323
  · exact pk_1324
  · exact pk_1325
  · exact pk_1326
  · exact pk_1327
  · exact pk_1328
  · exact pk_1329
  · exact pk_1330
  · exact pk_1331
  · exact pk_1332
  · exact pk_1333
  · exact pk_1334
  · exact pk_1335
  · exact pk_1336
  · exact pk_1337
  · exact pk_1338
  · exact pk_1339
  · exact pk_1340
  · exact pk_1341
  · exact pk_1342
  · exact pk_1343
  · exact pk_1344
  · exact pk_1345
  · exact pk_1346
  · exact pk_1347
  · exact pk_1348
  · exact pk_1349
  · exact pk_1350
  · exact pk_1351
  · exact pk_1352
  · exact pk_1353
  · exact pk_1354
  · exact pk_1355
  · exact pk_1356
  · exact pk_1357
  · exact pk_1358
  · exact pk_1359
  · exact pk_1360
  · exact pk_1361
  · exact pk_1362
  · exact pk_1363
  · exact pk_1364
  · exact pk_1365
  · exact pk_1366
  · exact pk_1367
  · exact pk_1368
  · exact pk_1369
  · exact pk_1370
  · exact pk_1371
  · exact pk_1372
  · exact pk_1373
  · exact pk_1374
  · exact pk_1375
  · exact pk_1376
  · exact pk_1377
  · exact pk_1378
  · exact pk_1379
  · exact pk_1380
  · exact pk_1381
  · exact pk_1382
  · exact pk_1383
  · exact pk_1384
  · exact pk_1385
  · exact pk_1386
  · exact pk_1387
  · exact pk_1388
  · exact pk_1389
  · exact pk_1390
  · exact pk_1391
  · exact pk_1392
  · exact pk_1393
  · exact pk_1394
  · exact pk_1395
  · exact pk_1396
  · exact pk_1397
  · exact pk_1398
  · exact pk_1399
  · exact pk_1400

theorem chunk_14 (k : ℕ) (h1 : 1401 ≤ k) (h2 : k ≤ 1407) : ¬ Nat.Prime ((k+1)^(Nat.totient (1408 - k)/2) - k) := by
  interval_cases k
  · exact pk_1401
  · exact pk_1402
  · exact pk_1403
  · exact pk_1404
  · exact pk_1405
  · exact pk_1406
  · exact pk_1407

theorem hkey (k : ℕ) (hk0 : 0 < k) (hkub : k < 1408) : ¬ Nat.Prime ((k+1)^(Nat.totient (1408 - k)/2) - k) := by
  by_cases c0 : k ≤ 100
  · exact chunk_0 k (by omega) c0
  by_cases c1 : k ≤ 200
  · exact chunk_1 k (by omega) c1
  by_cases c2 : k ≤ 300
  · exact chunk_2 k (by omega) c2
  by_cases c3 : k ≤ 400
  · exact chunk_3 k (by omega) c3
  by_cases c4 : k ≤ 500
  · exact chunk_4 k (by omega) c4
  by_cases c5 : k ≤ 600
  · exact chunk_5 k (by omega) c5
  by_cases c6 : k ≤ 700
  · exact chunk_6 k (by omega) c6
  by_cases c7 : k ≤ 800
  · exact chunk_7 k (by omega) c7
  by_cases c8 : k ≤ 900
  · exact chunk_8 k (by omega) c8
  by_cases c9 : k ≤ 1000
  · exact chunk_9 k (by omega) c9
  by_cases c10 : k ≤ 1100
  · exact chunk_10 k (by omega) c10
  by_cases c11 : k ≤ 1200
  · exact chunk_11 k (by omega) c11
  by_cases c12 : k ≤ 1300
  · exact chunk_12 k (by omega) c12
  by_cases c13 : k ≤ 1400
  · exact chunk_13 k (by omega) c13
  exact chunk_14 k (by omega) (by omega)

theorem oeis_234360_conjecture_0.disproof :
  ¬ ((∀ n, 1 < n → 0 < a n) ∧
     (∀ n, 5 < n → ∃ k, 0 < k ∧ k < n ∧ Nat.Prime ((k + 1) ^ (Nat.totient (n - k) / 2) - k))) := by
  rintro ⟨-, hB⟩
  obtain ⟨k, hk0, hkub, hkp⟩ := hB 1408 (by norm_num)
  exact hkey k hk0 hkub hkp
