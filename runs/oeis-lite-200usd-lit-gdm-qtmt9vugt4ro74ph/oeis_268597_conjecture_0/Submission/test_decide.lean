import Mathlib

set_option maxRecDepth 50000
set_option maxHeartbeats 0

open Nat

def witness_0 (n : ℕ) : ℕ :=
  match n with
  | 0 => 1
  | 1 => 4
  | 2 => 9
  | 3 => 8
  | 4 => 25
  | 5 => 18
  | 6 => 15
  | 7 => 16
  | 8 => 21
  | 9 => 50
  | 10 => 35
  | 11 => 36
  | 12 => 33
  | 13 => 98
  | 14 => 39
  | 15 => 32
  | 16 => 65
  | 17 => 54
  | 18 => 51
  | 19 => 100
  | 20 => 45
  | 21 => 70
  | 22 => 95
  | 23 => 72
  | 24 => 69
  | 25 => 338
  | 26 => 63
  | 27 => 196
  | 28 => 161
  | 29 => 110
  | 30 => 87
  | 31 => 64
  | 32 => 93
  | 33 => 130
  | 34 => 75
  | 35 => 108
  | 36 => 217
  | 37 => 182
  | 38 => 99
  | 39 => 200
  | 40 => 185
  | 41 => 170
  | 42 => 123
  | 43 => 140
  | 44 => 117
  | 45 => 190
  | 46 => 215
  | 47 => 144
  | 48 => 141
  | 49 => 250
  | 50 => 235
  | 51 => 676
  | 52 => 329
  | 53 => 162
  | 54 => 159
  | 55 => 392
  | 56 => 153
  | 57 => 322
  | 58 => 371
  | 59 => 220
  | 60 => 177
  | 61 => 494
  | 62 => 135
  | 63 => 128
  | 64 => 305
  | 65 => 290
  | 66 => 427
  | 67 => 260
  | 68 => 201
  | 69 => 310
  | 70 => 335
  | 71 => 216
  | 72 => 213
  | 73 => 434
  | 74 => 207
  | 75 => 364
  | 76 => 245
  | 77 => 638
  | 78 => 511
  | 79 => 400
  | 80 => 189
  | 81 => 370
  | 82 => 395
  | 83 => 340
  | 84 => 249
  | 85 => 518
  | 86 => 415
  | 87 => 280
  | 88 => 581
  | 89 => 410
  | 90 => 267
  | 91 => 380
  | 92 => 261
  | 93 => 430
  | 94 => 623
  | 95 => 288
  | 96 => 1501
  | 97 => 602
  | 98 => 279
  | 99 => 500
  | _ => 1

def witness_1 (n : ℕ) : ℕ :=
  match n with
  | 100 => 485
  | 101 => 462
  | 102 => 303
  | 103 => 1352
  | 104 => 225
  | 105 => 658
  | 106 => 515
  | 107 => 324
  | 108 => 321
  | 109 => 350
  | 110 => 231
  | 111 => 784
  | 112 => 545
  | 113 => 530
  | 114 => 339
  | 115 => 644
  | 116 => 297
  | 117 => 742
  | 118 => 539
  | 119 => 440
  | 120 => 1331
  | 121 => 1634
  | 122 => 1243
  | 123 => 988
  | 124 => 625
  | 125 => 510
  | 126 => 255
  | 127 => 256
  | 128 => 273
  | 129 => 610
  | 130 => 635
  | 131 => 580
  | 132 => 393
  | 133 => 854
  | 134 => 351
  | 135 => 520
  | 136 => 917
  | 137 => 570
  | 138 => 411
  | 139 => 620
  | 140 => 285
  | 141 => 670
  | 142 => 363
  | 143 => 432
  | 144 => 385
  | 145 => 938
  | 146 => 423
  | 147 => 868
  | 148 => 1529
  | 149 => 550
  | 150 => 447
  | 151 => 728
  | 152 => 453
  | 153 => 490
  | 154 => 755
  | 155 => 1276
  | 156 => 1057
  | 157 => 1022
  | 158 => 471
  | 159 => 800
  | 160 => 785
  | 161 => 486
  | 162 => 1099
  | 163 => 740
  | 164 => 357
  | 165 => 790
  | 166 => 455
  | 167 => 680
  | 168 => 345
  | 169 => 650
  | 170 => 459
  | 171 => 1036
  | 172 => 1169
  | 173 => 830
  | 174 => 375
  | 175 => 560
  | 176 => 865
  | 177 => 1162
  | 178 => 1211
  | 179 => 820
  | 180 => 537
  | 181 => 2054
  | 182 => 399
  | 183 => 760
  | 184 => 905
  | 185 => 890
  | 186 => 847
  | 187 => 860
  | 188 => 405
  | 189 => 1246
  | 190 => 1991
  | 191 => 576
  | 192 => 573
  | 193 => 3002
  | 194 => 507
  | 195 => 1204
  | 196 => 965
  | 197 => 870
  | 198 => 591
  | 199 => 1000
  | _ => 1

def witness_2 (n : ℕ) : ℕ :=
  match n with
  | 200 => 597
  | 201 => 970
  | 202 => 995
  | 203 => 924
  | 204 => 925
  | 205 => 1358
  | 206 => 603
  | 207 => 2704
  | 208 => 2189
  | 209 => 850
  | 210 => 435
  | 211 => 1316
  | 212 => 633
  | 213 => 1030
  | 214 => 1055
  | 215 => 648
  | 216 => 1477
  | 217 => 1442
  | 218 => 483
  | 219 => 700
  | 220 => 845
  | 221 => 1070
  | 222 => 2743
  | 223 => 1568
  | 224 => 465
  | 225 => 1090
  | 226 => 1115
  | 227 => 1060
  | 228 => 681
  | 229 => 950
  | 230 => 687
  | 231 => 1288
  | 232 => 665
  | 233 => 1130
  | 234 => 699
  | 235 => 1484
  | 236 => 1165
  | 237 => 1078
  | 238 => 1631
  | 239 => 880
  | 240 => 561
  | 241 => 2662
  | 242 => 567
  | 243 => 3268
  | 244 => 1205
  | 245 => 1110
  | 246 => 1183
  | 247 => 1976
  | 248 => 1785
  | 249 => 1250
  | 250 => 2651
  | 251 => 1020
  | 252 => 753
  | 253 => 4142
  | 254 => 747
  | 255 => 512
  | 256 => 1757
  | 257 => 1554
  | 258 => 771
  | 259 => 1220
  | 260 => 1285
  | 261 => 1270
  | 262 => 1799
  | 263 => 1160
  | 264 => 789
  | 265 => 1274
  | 266 => 555
  | 267 => 1708
  | 268 => 1841
  | 269 => 1150
  | 270 => 807
  | 271 => 1040
  | 272 => 609
  | 273 => 1834
  | 274 => 875
  | 275 => 1140
  | 276 => 805
  | 277 => 3302
  | 278 => 663
  | 279 => 1240
  | 280 => 1001
  | 281 => 1290
  | 282 => 843
  | 283 => 1340
  | 284 => 849
  | 285 => 1390
  | 286 => 1415
  | 287 => 864
  | 288 => 1981
  | 289 => 1946
  | 290 => 651
  | 291 => 1876
  | 292 => 3113
  | 293 => 1806
  | 294 => 615
  | 295 => 1736
  | 296 => 837
  | 297 => 3058
  | 298 => 1859
  | 299 => 1100
  | _ => 1

def witness_3 (n : ℕ) : ℕ :=
  match n with
  | 300 => 1813
  | 301 => 3614
  | 302 => 2415
  | 303 => 1456
  | 304 => 3809
  | 305 => 1386
  | 306 => 8587
  | 307 => 980
  | 308 => 645
  | 309 => 1510
  | 310 => 1535
  | 311 => 2552
  | 312 => 933
  | 313 => 2114
  | 314 => 675
  | 315 => 2044
  | 316 => 1565
  | 317 => 1974
  | 318 => 759
  | 319 => 1600
  | 320 => 1585
  | 321 => 1570
  | 322 => 867
  | 323 => 972
  | 324 => 1045
  | 325 => 2198
  | 326 => 963
  | 327 => 1480
  | 328 => 2009
  | 329 => 1210
  | 330 => 5947
  | 331 => 1580
  | 332 => 693
  | 333 => 1630
  | 334 => 1655
  | 335 => 1360
  | 336 => 705
  | 337 => 2282
  | 338 => 1011
  | 339 => 1300
  | 340 => 1685
  | 341 => 1590
  | 342 => 1015
  | 343 => 2072
  | 344 => 777
  | 345 => 2338
  | 346 => 3707
  | 347 => 1660
  | 348 => 1041
  | 349 => 1550
  | 350 => 891
  | 351 => 1120
  | 352 => 1745
  | 353 => 1730
  | 354 => 1059
  | 355 => 2324
  | 356 => 1445
  | 357 => 2422
  | 358 => 2471
  | 359 => 1640
  | 360 => 1077
  | 361 => 6194
  | 362 => 1795
  | 363 => 4108
  | 364 => 1085
  | 365 => 1790
  | 366 => 6631
  | 367 => 1520
  | 368 => 897
  | 369 => 1810
  | 370 => 1235
  | 371 => 1780
  | 372 => 2569
  | 373 => 1694
  | 374 => 1119
  | 375 => 1720
  | 376 => 1865
  | 377 => 1530
  | 378 => 795
  | 379 => 2492
  | 380 => 765
  | 381 => 3982
  | 382 => 1463
  | 383 => 1152
  | 384 => 1149
  | 385 => 4706
  | 386 => 819
  | 387 => 6004
  | 388 => 2681
  | 389 => 1830
  | 390 => 1167
  | 391 => 2408
  | 392 => 969
  | 393 => 1930
  | 394 => 1547
  | 395 => 1740
  | 396 => 957
  | 397 => 2702
  | 398 => 903
  | 399 => 2000
  | _ => 1

def witness_4 (n : ℕ) : ℕ :=
  match n with
  | 400 => 1985
  | 401 => 1970
  | 402 => 1203
  | 403 => 1940
  | 404 => 1053
  | 405 => 1990
  | 406 => 2807
  | 407 => 1848
  | 408 => 5161
  | 409 => 1850
  | 410 => 1227
  | 411 => 2716
  | 412 => 2045
  | 413 => 1710
  | 414 => 1975
  | 415 => 5408
  | 416 => 1233
  | 417 => 4378
  | 418 => 4499
  | 419 => 1700
  | 420 => 885
  | 421 => 5174
  | 422 => 855
  | 423 => 2632
  | 424 => 1625
  | 425 => 2010
  | 426 => 2947
  | 427 => 2060
  | 428 => 1089
  | 429 => 2110
  | 430 => 1295
  | 431 => 1296
  | 432 => 1293
  | 433 => 2954
  | 434 => 915
  | 435 => 2884
  | 436 => 1805
  | 437 => 2814
  | 438 => 1495
  | 439 => 1400
  | 440 => 1029
  | 441 => 1690
  | 442 => 2195
  | 443 => 2140
  | 444 => 1329
  | 445 => 5486
  | 446 => 2215
  | 447 => 3136
  | 448 => 3101
  | 449 => 2050
  | 450 => 1347
  | 451 => 2180
  | 452 => 1341
  | 453 => 2230
  | 454 => 2891
  | 455 => 2120
  | 456 => 8341
  | 457 => 3122
  | 458 => 1131
  | 459 => 1900
  | 460 => 2285
  | 461 => 2190
  | 462 => 1383
  | 463 => 2576
  | 464 => 1389
  | 465 => 2290
  | 466 => 2315
  | 467 => 2260
  | 468 => 1173
  | 469 => 1430
  | 470 => 2335
  | 471 => 2968
  | 472 => 3269
  | 473 => 2330
  | 474 => 1435
  | 475 => 2156
  | 476 => 1005
  | 477 => 3262
  | 478 => 6071
  | 479 => 1760
  | 480 => 1437
  | 481 => 5954
  | 482 => 2395
  | 483 => 5324
  | 484 => 3353
  | 485 => 1458
  | 486 => 14167
  | 487 => 6536
  | 488 => 1113
  | 489 => 2410
  | 490 => 2435
  | 491 => 2220
  | 492 => 1473
  | 493 => 2366
  | 494 => 1071
  | 495 => 3952
  | 496 => 1505
  | 497 => 2370
  | 498 => 6331
  | 499 => 2500
  | _ => 1

def witness_5 (n : ℕ) : ℕ :=
  match n with
  | 500 => 1221
  | 501 => 5302
  | 502 => 2495
  | 503 => 2040
  | 504 => 1065
  | 505 => 3146
  | 506 => 1035
  | 507 => 8284
  | 508 => 2093
  | 509 => 2350
  | 510 => 1527
  | 511 => 1024
  | 512 => 1377
  | 513 => 3514
  | 514 => 3563
  | 515 => 3108
  | 516 => 4477
  | 517 => 3038
  | 518 => 1095
  | 519 => 2440
  | 520 => 6617
  | 521 => 2490
  | 522 => 1563
  | 523 => 2540
  | 524 => 1125
  | 525 => 3598
  | 526 => 2615
  | 527 => 2320
  | 528 => 3661
  | 529 => 16946
  | 530 => 5731
  | 531 => 2548
  | 532 => 2261
  | 533 => 2630
  | 534 => 2575
  | 535 => 3416
  | 536 => 8857
  | 537 => 3682
  | 538 => 1715
  | 539 => 2300
  | 540 => 1645
  | 541 => 14942
  | 542 => 1239
  | 543 => 2080
  | 544 => 2705
  | 545 => 2690
  | 546 => 1955
  | 547 => 3668
  | 548 => 1197
  | 549 => 1750
  | 550 => 2735
  | 551 => 2280
  | 552 => 1353
  | 553 => 3794
  | 554 => 2675
  | 555 => 6604
  | 556 => 2717
  | 557 => 2670
  | 558 => 1671
  | 559 => 2480
  | 560 => 1185
  | 561 => 2002
  | 562 => 3899
  | 563 => 2580
  | 564 => 1689
  | 565 => 3878
  | 566 => 1215
  | 567 => 2680
  | 568 => 3941
  | 569 => 2650
  | 570 => 1707
  | 571 => 2780
  | 572 => 1713
  | 573 => 2830
  | 574 => 1587
  | 575 => 1728
  | 576 => 3997
  | 577 => 3962
  | 578 => 1419
  | 579 => 3892
  | 580 => 2885
  | 581 => 6182
  | 582 => 1479
  | 583 => 3752
  | 584 => 1521
  | 585 => 6226
  | 586 => 2387
  | 587 => 3612
  | 588 => 1245
  | 589 => 1870
  | 590 => 2935
  | 591 => 3472
  | 592 => 4109
  | 593 => 2610
  | 594 => 1779
  | 595 => 6116
  | 596 => 1773
  | 597 => 3718
  | 598 => 4151
  | 599 => 2200
  | _ => 1

def witness_6 (n : ℕ) : ℕ :=
  match n with
  | 600 => 1797
  | 601 => 3626
  | 602 => 1791
  | 603 => 7228
  | 604 => 3005
  | 605 => 2910
  | 606 => 1855
  | 607 => 2912
  | 608 => 1821
  | 609 => 7618
  | 610 => 3035
  | 611 => 2772
  | 612 => 4249
  | 613 => 17174
  | 614 => 1407
  | 615 => 1960
  | 616 => 3065
  | 617 => 4074
  | 618 => 1851
  | 619 => 3020
  | 620 => 1581
  | 621 => 3070
  | 622 => 2639
  | 623 => 5104
  | 624 => 2737
  | 625 => 4298
  | 626 => 5687
  | 627 => 4228
  | 628 => 6809
  | 629 => 2550
  | 630 => 1335
  | 631 => 4088
  | 632 => 1305
  | 633 => 3130
  | 634 => 1275
  | 635 => 3948
  | 636 => 4417
  | 637 => 4382
  | 638 => 1599
  | 639 => 3200
  | 640 => 6941
  | 641 => 3090
  | 642 => 1923
  | 643 => 3140
  | 644 => 1653
  | 645 => 4438
  | 646 => 3215
  | 647 => 1944
  | 648 => 1941
  | 649 => 2090
  | 650 => 1491
  | 651 => 4396
  | 652 => 4529
  | 653 => 4326
  | 654 => 1959
  | 655 => 2960
  | 656 => 1449
  | 657 => 4018
  | 658 => 4571
  | 659 => 2420
  | 660 => 1977
  | 661 => 11894
  | 662 => 1983
  | 663 => 3160
  | 664 => 3305
  | 665 => 3210
  | 666 => 3703
  | 667 => 3260
  | 668 => 1533
  | 669 => 3310
  | 670 => 7271
  | 671 => 2720
  | 672 => 2065
  | 673 => 2210
  | 674 => 1395
  | 675 => 4564
  | 676 => 2405
  | 677 => 3270
  | 678 => 2031
  | 679 => 2600
  | 680 => 3385
  | 681 => 3370
  | 682 => 3059
  | 683 => 3180
  | 684 => 2049
  | 685 => 4214
  | 686 => 1455
  | 687 => 4144
  | 688 => 2849
  | 689 => 2850
  | 690 => 12787
  | 691 => 4676
  | 692 => 2061
  | 693 => 7414
  | 694 => 2135
  | 695 => 3320
  | 696 => 4837
  | 697 => 2618
  | 698 => 7035
  | 699 => 3100
  | _ => 1

def witness_7 (n : ℕ) : ℕ :=
  match n with
  | 700 => 7601
  | 701 => 3390
  | 702 => 2103
  | 703 => 2240
  | 704 => 1425
  | 705 => 3490
  | 706 => 4907
  | 707 => 3460
  | 708 => 1749
  | 709 => 3350
  | 710 => 2127
  | 711 => 4648
  | 712 => 3545
  | 713 => 2890
  | 714 => 1515
  | 715 => 4844
  | 716 => 11917
  | 717 => 4942
  | 718 => 7799
  | 719 => 3280
  | 720 => 2157
  | 721 => 9074
  | 722 => 1659
  | 723 => 12388
  | 724 => 1925
  | 725 => 3590
  | 726 => 13471
  | 727 => 8216
  | 728 => 1545
  | 729 => 5026
  | 730 => 3635
  | 731 => 3580
  | 732 => 5089
  | 733 => 13262
  | 734 => 1887
  | 735 => 3040
  | 736 => 3665
  | 737 => 3330
  | 738 => 2755
  | 739 => 3620
  | 740 => 2217
  | 741 => 2470
  | 742 => 3695
  | 743 => 3560
  | 744 => 2229
  | 745 => 5138
  | 746 => 3715
  | 747 => 3388
  | 748 => 4949
  | 749 => 2750
  | 750 => 9607
  | 751 => 3440
  | 752 => 2253
  | 753 => 3730
  | 754 => 3755
  | 755 => 3060
  | 756 => 1605
  | 757 => 5222
  | 758 => 1743
  | 759 => 4984
  | 760 => 2345
  | 761 => 12426
  | 762 => 2283
  | 763 => 7964
  | 764 => 2241
  | 765 => 2926
  | 766 => 5327
  | 767 => 2304
  | 768 => 2001
  | 769 => 2450
  | 770 => 1635
  | 771 => 9412
  | 772 => 3845
  | 773 => 3830
  | 774 => 2319
  | 775 => 12008
  | 776 => 1617
  | 777 => 5362
  | 778 => 2795
  | 779 => 3660
  | 780 => 4301
  | 781 => 4046
  | 782 => 8503
  | 783 => 4816
  | 784 => 2945
  | 785 => 3810
  | 786 => 1947
  | 787 => 3860
  | 788 => 2361
  | 789 => 3094
  | 790 => 3311
  | 791 => 3480
  | 792 => 5509
  | 793 => 14402
  | 794 => 2367
  | 795 => 5404
  | 796 => 8657
  | 797 => 3822
  | 798 => 1695
  | 799 => 4000
  | _ => 1

def witness_8 (n : ℕ) : ℕ :=
  match n with
  | 800 => 1665
  | 801 => 3970
  | 802 => 5579
  | 803 => 3940
  | 804 => 2485
  | 805 => 5558
  | 806 => 8295
  | 807 => 3880
  | 808 => 3689
  | 809 => 3450
  | 810 => 2091
  | 811 => 3980
  | 812 => 1869
  | 813 => 5614
  | 814 => 4055
  | 815 => 3696
  | 816 => 5677
  | 817 => 10322
  | 818 => 1827
  | 819 => 3700
  | 820 => 8921
  | 821 => 5502
  | 822 => 2463
  | 823 => 5432
  | 824 => 2469
  | 825 => 4090
  | 826 => 2555
  | 827 => 3420
  | 828 => 2481
  | 829 => 3950
  | 830 => 2487
  | 831 => 10816
  | 832 => 3773
  | 833 => 9906
  | 834 => 2275
  | 835 => 8756
  | 836 => 1989
  | 837 => 8998
  | 838 => 9119
  | 839 => 3400
  | 840 => 2517
  | 841 => 10634
  | 842 => 4195
  | 843 => 10348
  | 844 => 1725
  | 845 => 3870
  | 846 => 3055
  | 847 => 5264
  | 848 => 2193
  | 849 => 3250
  | 850 => 3731
  | 851 => 4020
  | 852 => 25513
  | 853 => 5894
  | 854 => 2547
  | 855 => 4120
  | 856 => 4265
  | 857 => 4170
  | 858 => 2571
  | 859 => 4220
  | 860 => 2577
  | 861 => 2590
  | 862 => 4295
  | 863 => 2592
  | 864 => 2589
  | 865 => 3458
  | 866 => 4315
  | 867 => 5908
  | 868 => 6041
  | 869 => 4150
  | 870 => 3335
  | 871 => 5768
  | 872 => 1953
  | 873 => 3610
  | 874 => 1875
  | 875 => 5628
  | 876 => 16321
  | 877 => 2990
  | 878 => 2631
  | 879 => 2800
  | 880 => 4385
  | 881 => 5418
  | 882 => 2643
  | 883 => 3380
  | 884 => 1845
  | 885 => 4390
  | 886 => 4415
  | 887 => 4280
  | 888 => 2661
  | 889 => 6146
  | 890 => 2211
  | 891 => 10972
  | 892 => 2765
  | 893 => 4430
  | 894 => 11479
  | 895 => 6272
  | 896 => 1905
  | 897 => 6202
  | 898 => 2523
  | 899 => 4100
  | _ => 1

def witness_9 (n : ℕ) : ℕ :=
  match n with
  | 900 => 10693
  | 901 => 3542
  | 902 => 1911
  | 903 => 4360
  | 904 => 16853
  | 905 => 4490
  | 906 => 27187
  | 907 => 4460
  | 908 => 2301
  | 909 => 5782
  | 910 => 4535
  | 911 => 4240
  | 912 => 2733
  | 913 => 16682
  | 914 => 4475
  | 915 => 6244
  | 916 => 6377
  | 917 => 4158
  | 918 => 11791
  | 919 => 3800
  | 920 => 2121
  | 921 => 4570
  | 922 => 3515
  | 923 => 4380
  | 924 => 1965
  | 925 => 3230
  | 926 => 1935
  | 927 => 5152
  | 928 => 5681
  | 929 => 4450
  | 930 => 2787
  | 931 => 4580
  | 932 => 4645
  | 933 => 4630
  | 934 => 6503
  | 935 => 4520
  | 936 => 2905
  | 937 => 5978
  | 938 => 2163
  | 939 => 2860
  | 940 => 4685
  | 941 => 4670
  | 942 => 2343
  | 943 => 5936
  | 944 => 2025
  | 945 => 6538
  | 946 => 4403
  | 947 => 4660
  | 948 => 2841
  | 949 => 2870
  | 950 => 4735
  | 951 => 4312
  | 952 => 6629
  | 953 => 5922
  | 954 => 2859
  | 955 => 6524
  | 956 => 2277
  | 957 => 12142
  | 958 => 6419
  | 959 => 3520
  | 960 => 4081
  | 961 => 17594
  | 962 => 10483
  | 963 => 11908
  | 964 => 4277
  | 965 => 4710
  | 966 => 2055
  | 967 => 10648
  | 968 => 2409
  | 969 => 6706
  | 970 => 4835
  | 971 => 2916
  | 972 => 2913
  | 973 => 28334
  | 974 => 2247
  | 975 => 13072
  | 976 => 6797
  | 977 => 6594
  | 978 => 2931
  | 979 => 4820
  | 980 => 2085
  | 981 => 4870
  | 982 => 6839
  | 983 => 4440
  | 984 => 2949
  | 985 => 6818
  | 986 => 4915
  | 987 => 4732
  | 988 => 6881
  | 989 => 4350
  | 990 => 67087
  | 991 => 7904
  | 992 => 2289
  | 993 => 3010
  | 994 => 4955
  | 995 => 4740
  | 996 => 5797
  | 997 => 12662
  | 998 => 2079
  | 999 => 5000
  | _ => 1

def witness (n : ℕ) : ℕ :=
  if n < 100 then witness_0 n
  else if n < 200 then witness_1 n
  else if n < 300 then witness_2 n
  else if n < 400 then witness_3 n
  else if n < 500 then witness_4 n
  else if n < 600 then witness_5 n
  else if n < 700 then witness_6 n
  else if n < 800 then witness_7 n
  else if n < 900 then witness_8 n
  else if n < 1000 then witness_9 n
  else 1

lemma witness_pos_and_mod_0 (n : ℕ) (h2 : n < 100) : witness n > 0 ∧ (witness n - 1) % Nat.totient (witness n) = n := by
  by_cases h_mid : n < 50
  · by_cases h_mid : n < 25
    · by_cases h_mid : n < 13
      · by_cases h_mid : n < 7
        · by_cases h_mid : n < 4
          · by_cases h_mid : n < 2
            · by_cases h_mid : n < 1
              · have : n = 0 := by omega
                subst this
                decide
              · have : n = 1 := by omega
                subst this
                decide
            · by_cases h_mid : n < 3
              · have : n = 2 := by omega
                subst this
                decide
              · have : n = 3 := by omega
                subst this
                decide
          · by_cases h_mid : n < 6
            · by_cases h_mid : n < 5
              · have : n = 4 := by omega
                subst this
                decide
              · have : n = 5 := by omega
                subst this
                decide
            · have : n = 6 := by omega
              subst this
              decide
        · by_cases h_mid : n < 10
          · by_cases h_mid : n < 9
            · by_cases h_mid : n < 8
              · have : n = 7 := by omega
                subst this
                decide
              · have : n = 8 := by omega
                subst this
                decide
            · have : n = 9 := by omega
              subst this
              decide
          · by_cases h_mid : n < 12
            · by_cases h_mid : n < 11
              · have : n = 10 := by omega
                subst this
                decide
              · have : n = 11 := by omega
                subst this
                decide
            · have : n = 12 := by omega
              subst this
              decide
      · by_cases h_mid : n < 19
        · by_cases h_mid : n < 16
          · by_cases h_mid : n < 15
            · by_cases h_mid : n < 14
              · have : n = 13 := by omega
                subst this
                decide
              · have : n = 14 := by omega
                subst this
                decide
            · have : n = 15 := by omega
              subst this
              decide
          · by_cases h_mid : n < 18
            · by_cases h_mid : n < 17
              · have : n = 16 := by omega
                subst this
                decide
              · have : n = 17 := by omega
                subst this
                decide
            · have : n = 18 := by omega
              subst this
              decide
        · by_cases h_mid : n < 22
          · by_cases h_mid : n < 21
            · by_cases h_mid : n < 20
              · have : n = 19 := by omega
                subst this
                decide
              · have : n = 20 := by omega
                subst this
                decide
            · have : n = 21 := by omega
              subst this
              decide
          · by_cases h_mid : n < 24
            · by_cases h_mid : n < 23
              · have : n = 22 := by omega
                subst this
                decide
              · have : n = 23 := by omega
                subst this
                decide
            · have : n = 24 := by omega
              subst this
              decide
    · by_cases h_mid : n < 38
      · by_cases h_mid : n < 32
        · by_cases h_mid : n < 29
          · by_cases h_mid : n < 27
            · by_cases h_mid : n < 26
              · have : n = 25 := by omega
                subst this
                decide
              · have : n = 26 := by omega
                subst this
                decide
            · by_cases h_mid : n < 28
              · have : n = 27 := by omega
                subst this
                decide
              · have : n = 28 := by omega
                subst this
                decide
          · by_cases h_mid : n < 31
            · by_cases h_mid : n < 30
              · have : n = 29 := by omega
                subst this
                decide
              · have : n = 30 := by omega
                subst this
                decide
            · have : n = 31 := by omega
              subst this
              decide
        · by_cases h_mid : n < 35
          · by_cases h_mid : n < 34
            · by_cases h_mid : n < 33
              · have : n = 32 := by omega
                subst this
                decide
              · have : n = 33 := by omega
                subst this
                decide
            · have : n = 34 := by omega
              subst this
              decide
          · by_cases h_mid : n < 37
            · by_cases h_mid : n < 36
              · have : n = 35 := by omega
                subst this
                decide
              · have : n = 36 := by omega
                subst this
                decide
            · have : n = 37 := by omega
              subst this
              decide
      · by_cases h_mid : n < 44
        · by_cases h_mid : n < 41
          · by_cases h_mid : n < 40
            · by_cases h_mid : n < 39
              · have : n = 38 := by omega
                subst this
                decide
              · have : n = 39 := by omega
                subst this
                decide
            · have : n = 40 := by omega
              subst this
              decide
          · by_cases h_mid : n < 43
            · by_cases h_mid : n < 42
              · have : n = 41 := by omega
                subst this
                decide
              · have : n = 42 := by omega
                subst this
                decide
            · have : n = 43 := by omega
              subst this
              decide
        · by_cases h_mid : n < 47
          · by_cases h_mid : n < 46
            · by_cases h_mid : n < 45
              · have : n = 44 := by omega
                subst this
                decide
              · have : n = 45 := by omega
                subst this
                decide
            · have : n = 46 := by omega
              subst this
              decide
          · by_cases h_mid : n < 49
            · by_cases h_mid : n < 48
              · have : n = 47 := by omega
                subst this
                decide
              · have : n = 48 := by omega
                subst this
                decide
            · have : n = 49 := by omega
              subst this
              decide
  · by_cases h_mid : n < 75
    · by_cases h_mid : n < 63
      · by_cases h_mid : n < 57
        · by_cases h_mid : n < 54
          · by_cases h_mid : n < 52
            · by_cases h_mid : n < 51
              · have : n = 50 := by omega
                subst this
                decide
              · have : n = 51 := by omega
                subst this
                decide
            · by_cases h_mid : n < 53
              · have : n = 52 := by omega
                subst this
                decide
              · have : n = 53 := by omega
                subst this
                decide
          · by_cases h_mid : n < 56
            · by_cases h_mid : n < 55
              · have : n = 54 := by omega
                subst this
                decide
              · have : n = 55 := by omega
                subst this
                decide
            · have : n = 56 := by omega
              subst this
              decide
        · by_cases h_mid : n < 60
          · by_cases h_mid : n < 59
            · by_cases h_mid : n < 58
              · have : n = 57 := by omega
                subst this
                decide
              · have : n = 58 := by omega
                subst this
                decide
            · have : n = 59 := by omega
              subst this
              decide
          · by_cases h_mid : n < 62
            · by_cases h_mid : n < 61
              · have : n = 60 := by omega
                subst this
                decide
              · have : n = 61 := by omega
                subst this
                decide
            · have : n = 62 := by omega
              subst this
              decide
      · by_cases h_mid : n < 69
        · by_cases h_mid : n < 66
          · by_cases h_mid : n < 65
            · by_cases h_mid : n < 64
              · have : n = 63 := by omega
                subst this
                decide
              · have : n = 64 := by omega
                subst this
                decide
            · have : n = 65 := by omega
              subst this
              decide
          · by_cases h_mid : n < 68
            · by_cases h_mid : n < 67
              · have : n = 66 := by omega
                subst this
                decide
              · have : n = 67 := by omega
                subst this
                decide
            · have : n = 68 := by omega
              subst this
              decide
        · by_cases h_mid : n < 72
          · by_cases h_mid : n < 71
            · by_cases h_mid : n < 70
              · have : n = 69 := by omega
                subst this
                decide
              · have : n = 70 := by omega
                subst this
                decide
            · have : n = 71 := by omega
              subst this
              decide
          · by_cases h_mid : n < 74
            · by_cases h_mid : n < 73
              · have : n = 72 := by omega
                subst this
                decide
              · have : n = 73 := by omega
                subst this
                decide
            · have : n = 74 := by omega
              subst this
              decide
    · by_cases h_mid : n < 88
      · by_cases h_mid : n < 82
        · by_cases h_mid : n < 79
          · by_cases h_mid : n < 77
            · by_cases h_mid : n < 76
              · have : n = 75 := by omega
                subst this
                decide
              · have : n = 76 := by omega
                subst this
                decide
            · by_cases h_mid : n < 78
              · have : n = 77 := by omega
                subst this
                decide
              · have : n = 78 := by omega
                subst this
                decide
          · by_cases h_mid : n < 81
            · by_cases h_mid : n < 80
              · have : n = 79 := by omega
                subst this
                decide
              · have : n = 80 := by omega
                subst this
                decide
            · have : n = 81 := by omega
              subst this
              decide
        · by_cases h_mid : n < 85
          · by_cases h_mid : n < 84
            · by_cases h_mid : n < 83
              · have : n = 82 := by omega
                subst this
                decide
              · have : n = 83 := by omega
                subst this
                decide
            · have : n = 84 := by omega
              subst this
              decide
          · by_cases h_mid : n < 87
            · by_cases h_mid : n < 86
              · have : n = 85 := by omega
                subst this
                decide
              · have : n = 86 := by omega
                subst this
                decide
            · have : n = 87 := by omega
              subst this
              decide
      · by_cases h_mid : n < 94
        · by_cases h_mid : n < 91
          · by_cases h_mid : n < 90
            · by_cases h_mid : n < 89
              · have : n = 88 := by omega
                subst this
                decide
              · have : n = 89 := by omega
                subst this
                decide
            · have : n = 90 := by omega
              subst this
              decide
          · by_cases h_mid : n < 93
            · by_cases h_mid : n < 92
              · have : n = 91 := by omega
                subst this
                decide
              · have : n = 92 := by omega
                subst this
                decide
            · have : n = 93 := by omega
              subst this
              decide
        · by_cases h_mid : n < 97
          · by_cases h_mid : n < 96
            · by_cases h_mid : n < 95
              · have : n = 94 := by omega
                subst this
                decide
              · have : n = 95 := by omega
                subst this
                decide
            · have : n = 96 := by omega
              subst this
              decide
          · by_cases h_mid : n < 99
            · by_cases h_mid : n < 98
              · have : n = 97 := by omega
                subst this
                decide
              · have : n = 98 := by omega
                subst this
                decide
            · have : n = 99 := by omega
              subst this
              decide

lemma witness_pos_and_mod_1 (n : ℕ) (h1 : 100 ≤ n) (h2 : n < 200) : witness n > 0 ∧ (witness n - 1) % Nat.totient (witness n) = n := by
  by_cases h_mid : n < 150
  · by_cases h_mid : n < 125
    · by_cases h_mid : n < 113
      · by_cases h_mid : n < 107
        · by_cases h_mid : n < 104
          · by_cases h_mid : n < 102
            · by_cases h_mid : n < 101
              · have : n = 100 := by omega
                subst this
                decide
              · have : n = 101 := by omega
                subst this
                decide
            · by_cases h_mid : n < 103
              · have : n = 102 := by omega
                subst this
                decide
              · have : n = 103 := by omega
                subst this
                decide
          · by_cases h_mid : n < 106
            · by_cases h_mid : n < 105
              · have : n = 104 := by omega
                subst this
                decide
              · have : n = 105 := by omega
                subst this
                decide
            · have : n = 106 := by omega
              subst this
              decide
        · by_cases h_mid : n < 110
          · by_cases h_mid : n < 109
            · by_cases h_mid : n < 108
              · have : n = 107 := by omega
                subst this
                decide
              · have : n = 108 := by omega
                subst this
                decide
            · have : n = 109 := by omega
              subst this
              decide
          · by_cases h_mid : n < 112
            · by_cases h_mid : n < 111
              · have : n = 110 := by omega
                subst this
                decide
              · have : n = 111 := by omega
                subst this
                decide
            · have : n = 112 := by omega
              subst this
              decide
      · by_cases h_mid : n < 119
        · by_cases h_mid : n < 116
          · by_cases h_mid : n < 115
            · by_cases h_mid : n < 114
              · have : n = 113 := by omega
                subst this
                decide
              · have : n = 114 := by omega
                subst this
                decide
            · have : n = 115 := by omega
              subst this
              decide
          · by_cases h_mid : n < 118
            · by_cases h_mid : n < 117
              · have : n = 116 := by omega
                subst this
                decide
              · have : n = 117 := by omega
                subst this
                decide
            · have : n = 118 := by omega
              subst this
              decide
        · by_cases h_mid : n < 122
          · by_cases h_mid : n < 121
            · by_cases h_mid : n < 120
              · have : n = 119 := by omega
                subst this
                decide
              · have : n = 120 := by omega
                subst this
                decide
            · have : n = 121 := by omega
              subst this
              decide
          · by_cases h_mid : n < 124
            · by_cases h_mid : n < 123
              · have : n = 122 := by omega
                subst this
                decide
              · have : n = 123 := by omega
                subst this
                decide
            · have : n = 124 := by omega
              subst this
              decide
    · by_cases h_mid : n < 138
      · by_cases h_mid : n < 132
        · by_cases h_mid : n < 129
          · by_cases h_mid : n < 127
            · by_cases h_mid : n < 126
              · have : n = 125 := by omega
                subst this
                decide
              · have : n = 126 := by omega
                subst this
                decide
            · by_cases h_mid : n < 128
              · have : n = 127 := by omega
                subst this
                decide
              · have : n = 128 := by omega
                subst this
                decide
          · by_cases h_mid : n < 131
            · by_cases h_mid : n < 130
              · have : n = 129 := by omega
                subst this
                decide
              · have : n = 130 := by omega
                subst this
                decide
            · have : n = 131 := by omega
              subst this
              decide
        · by_cases h_mid : n < 135
          · by_cases h_mid : n < 134
            · by_cases h_mid : n < 133
              · have : n = 132 := by omega
                subst this
                decide
              · have : n = 133 := by omega
                subst this
                decide
            · have : n = 134 := by omega
              subst this
              decide
          · by_cases h_mid : n < 137
            · by_cases h_mid : n < 136
              · have : n = 135 := by omega
                subst this
                decide
              · have : n = 136 := by omega
                subst this
                decide
            · have : n = 137 := by omega
              subst this
              decide
      · by_cases h_mid : n < 144
        · by_cases h_mid : n < 141
          · by_cases h_mid : n < 140
            · by_cases h_mid : n < 139
              · have : n = 138 := by omega
                subst this
                decide
              · have : n = 139 := by omega
                subst this
                decide
            · have : n = 140 := by omega
              subst this
              decide
          · by_cases h_mid : n < 143
            · by_cases h_mid : n < 142
              · have : n = 141 := by omega
                subst this
                decide
              · have : n = 142 := by omega
                subst this
                decide
            · have : n = 143 := by omega
              subst this
              decide
        · by_cases h_mid : n < 147
          · by_cases h_mid : n < 146
            · by_cases h_mid : n < 145
              · have : n = 144 := by omega
                subst this
                decide
              · have : n = 145 := by omega
                subst this
                decide
            · have : n = 146 := by omega
              subst this
              decide
          · by_cases h_mid : n < 149
            · by_cases h_mid : n < 148
              · have : n = 147 := by omega
                subst this
                decide
              · have : n = 148 := by omega
                subst this
                decide
            · have : n = 149 := by omega
              subst this
              decide
  · by_cases h_mid : n < 175
    · by_cases h_mid : n < 163
      · by_cases h_mid : n < 157
        · by_cases h_mid : n < 154
          · by_cases h_mid : n < 152
            · by_cases h_mid : n < 151
              · have : n = 150 := by omega
                subst this
                decide
              · have : n = 151 := by omega
                subst this
                decide
            · by_cases h_mid : n < 153
              · have : n = 152 := by omega
                subst this
                decide
              · have : n = 153 := by omega
                subst this
                decide
          · by_cases h_mid : n < 156
            · by_cases h_mid : n < 155
              · have : n = 154 := by omega
                subst this
                decide
              · have : n = 155 := by omega
                subst this
                decide
            · have : n = 156 := by omega
              subst this
              decide
        · by_cases h_mid : n < 160
          · by_cases h_mid : n < 159
            · by_cases h_mid : n < 158
              · have : n = 157 := by omega
                subst this
                decide
              · have : n = 158 := by omega
                subst this
                decide
            · have : n = 159 := by omega
              subst this
              decide
          · by_cases h_mid : n < 162
            · by_cases h_mid : n < 161
              · have : n = 160 := by omega
                subst this
                decide
              · have : n = 161 := by omega
                subst this
                decide
            · have : n = 162 := by omega
              subst this
              decide
      · by_cases h_mid : n < 169
        · by_cases h_mid : n < 166
          · by_cases h_mid : n < 165
            · by_cases h_mid : n < 164
              · have : n = 163 := by omega
                subst this
                decide
              · have : n = 164 := by omega
                subst this
                decide
            · have : n = 165 := by omega
              subst this
              decide
          · by_cases h_mid : n < 168
            · by_cases h_mid : n < 167
              · have : n = 166 := by omega
                subst this
                decide
              · have : n = 167 := by omega
                subst this
                decide
            · have : n = 168 := by omega
              subst this
              decide
        · by_cases h_mid : n < 172
          · by_cases h_mid : n < 171
            · by_cases h_mid : n < 170
              · have : n = 169 := by omega
                subst this
                decide
              · have : n = 170 := by omega
                subst this
                decide
            · have : n = 171 := by omega
              subst this
              decide
          · by_cases h_mid : n < 174
            · by_cases h_mid : n < 173
              · have : n = 172 := by omega
                subst this
                decide
              · have : n = 173 := by omega
                subst this
                decide
            · have : n = 174 := by omega
              subst this
              decide
    · by_cases h_mid : n < 188
      · by_cases h_mid : n < 182
        · by_cases h_mid : n < 179
          · by_cases h_mid : n < 177
            · by_cases h_mid : n < 176
              · have : n = 175 := by omega
                subst this
                decide
              · have : n = 176 := by omega
                subst this
                decide
            · by_cases h_mid : n < 178
              · have : n = 177 := by omega
                subst this
                decide
              · have : n = 178 := by omega
                subst this
                decide
          · by_cases h_mid : n < 181
            · by_cases h_mid : n < 180
              · have : n = 179 := by omega
                subst this
                decide
              · have : n = 180 := by omega
                subst this
                decide
            · have : n = 181 := by omega
              subst this
              decide
        · by_cases h_mid : n < 185
          · by_cases h_mid : n < 184
            · by_cases h_mid : n < 183
              · have : n = 182 := by omega
                subst this
                decide
              · have : n = 183 := by omega
                subst this
                decide
            · have : n = 184 := by omega
              subst this
              decide
          · by_cases h_mid : n < 187
            · by_cases h_mid : n < 186
              · have : n = 185 := by omega
                subst this
                decide
              · have : n = 186 := by omega
                subst this
                decide
            · have : n = 187 := by omega
              subst this
              decide
      · by_cases h_mid : n < 194
        · by_cases h_mid : n < 191
          · by_cases h_mid : n < 190
            · by_cases h_mid : n < 189
              · have : n = 188 := by omega
                subst this
                decide
              · have : n = 189 := by omega
                subst this
                decide
            · have : n = 190 := by omega
              subst this
              decide
          · by_cases h_mid : n < 193
            · by_cases h_mid : n < 192
              · have : n = 191 := by omega
                subst this
                decide
              · have : n = 192 := by omega
                subst this
                decide
            · have : n = 193 := by omega
              subst this
              decide
        · by_cases h_mid : n < 197
          · by_cases h_mid : n < 196
            · by_cases h_mid : n < 195
              · have : n = 194 := by omega
                subst this
                decide
              · have : n = 195 := by omega
                subst this
                decide
            · have : n = 196 := by omega
              subst this
              decide
          · by_cases h_mid : n < 199
            · by_cases h_mid : n < 198
              · have : n = 197 := by omega
                subst this
                decide
              · have : n = 198 := by omega
                subst this
                decide
            · have : n = 199 := by omega
              subst this
              decide

lemma witness_pos_and_mod_2 (n : ℕ) (h1 : 200 ≤ n) (h2 : n < 300) : witness n > 0 ∧ (witness n - 1) % Nat.totient (witness n) = n := by
  by_cases h_mid : n < 250
  · by_cases h_mid : n < 225
    · by_cases h_mid : n < 213
      · by_cases h_mid : n < 207
        · by_cases h_mid : n < 204
          · by_cases h_mid : n < 202
            · by_cases h_mid : n < 201
              · have : n = 200 := by omega
                subst this
                decide
              · have : n = 201 := by omega
                subst this
                decide
            · by_cases h_mid : n < 203
              · have : n = 202 := by omega
                subst this
                decide
              · have : n = 203 := by omega
                subst this
                decide
          · by_cases h_mid : n < 206
            · by_cases h_mid : n < 205
              · have : n = 204 := by omega
                subst this
                decide
              · have : n = 205 := by omega
                subst this
                decide
            · have : n = 206 := by omega
              subst this
              decide
        · by_cases h_mid : n < 210
          · by_cases h_mid : n < 209
            · by_cases h_mid : n < 208
              · have : n = 207 := by omega
                subst this
                decide
              · have : n = 208 := by omega
                subst this
                decide
            · have : n = 209 := by omega
              subst this
              decide
          · by_cases h_mid : n < 212
            · by_cases h_mid : n < 211
              · have : n = 210 := by omega
                subst this
                decide
              · have : n = 211 := by omega
                subst this
                decide
            · have : n = 212 := by omega
              subst this
              decide
      · by_cases h_mid : n < 219
        · by_cases h_mid : n < 216
          · by_cases h_mid : n < 215
            · by_cases h_mid : n < 214
              · have : n = 213 := by omega
                subst this
                decide
              · have : n = 214 := by omega
                subst this
                decide
            · have : n = 215 := by omega
              subst this
              decide
          · by_cases h_mid : n < 218
            · by_cases h_mid : n < 217
              · have : n = 216 := by omega
                subst this
                decide
              · have : n = 217 := by omega
                subst this
                decide
            · have : n = 218 := by omega
              subst this
              decide
        · by_cases h_mid : n < 222
          · by_cases h_mid : n < 221
            · by_cases h_mid : n < 220
              · have : n = 219 := by omega
                subst this
                decide
              · have : n = 220 := by omega
                subst this
                decide
            · have : n = 221 := by omega
              subst this
              decide
          · by_cases h_mid : n < 224
            · by_cases h_mid : n < 223
              · have : n = 222 := by omega
                subst this
                decide
              · have : n = 223 := by omega
                subst this
                decide
            · have : n = 224 := by omega
              subst this
              decide
    · by_cases h_mid : n < 238
      · by_cases h_mid : n < 232
        · by_cases h_mid : n < 229
          · by_cases h_mid : n < 227
            · by_cases h_mid : n < 226
              · have : n = 225 := by omega
                subst this
                decide
              · have : n = 226 := by omega
                subst this
                decide
            · by_cases h_mid : n < 228
              · have : n = 227 := by omega
                subst this
                decide
              · have : n = 228 := by omega
                subst this
                decide
          · by_cases h_mid : n < 231
            · by_cases h_mid : n < 230
              · have : n = 229 := by omega
                subst this
                decide
              · have : n = 230 := by omega
                subst this
                decide
            · have : n = 231 := by omega
              subst this
              decide
        · by_cases h_mid : n < 235
          · by_cases h_mid : n < 234
            · by_cases h_mid : n < 233
              · have : n = 232 := by omega
                subst this
                decide
              · have : n = 233 := by omega
                subst this
                decide
            · have : n = 234 := by omega
              subst this
              decide
          · by_cases h_mid : n < 237
            · by_cases h_mid : n < 236
              · have : n = 235 := by omega
                subst this
                decide
              · have : n = 236 := by omega
                subst this
                decide
            · have : n = 237 := by omega
              subst this
              decide
      · by_cases h_mid : n < 244
        · by_cases h_mid : n < 241
          · by_cases h_mid : n < 240
            · by_cases h_mid : n < 239
              · have : n = 238 := by omega
                subst this
                decide
              · have : n = 239 := by omega
                subst this
                decide
            · have : n = 240 := by omega
              subst this
              decide
          · by_cases h_mid : n < 243
            · by_cases h_mid : n < 242
              · have : n = 241 := by omega
                subst this
                decide
              · have : n = 242 := by omega
                subst this
                decide
            · have : n = 243 := by omega
              subst this
              decide
        · by_cases h_mid : n < 247
          · by_cases h_mid : n < 246
            · by_cases h_mid : n < 245
              · have : n = 244 := by omega
                subst this
                decide
              · have : n = 245 := by omega
                subst this
                decide
            · have : n = 246 := by omega
              subst this
              decide
          · by_cases h_mid : n < 249
            · by_cases h_mid : n < 248
              · have : n = 247 := by omega
                subst this
                decide
              · have : n = 248 := by omega
                subst this
                decide
            · have : n = 249 := by omega
              subst this
              decide
  · by_cases h_mid : n < 275
    · by_cases h_mid : n < 263
      · by_cases h_mid : n < 257
        · by_cases h_mid : n < 254
          · by_cases h_mid : n < 252
            · by_cases h_mid : n < 251
              · have : n = 250 := by omega
                subst this
                decide
              · have : n = 251 := by omega
                subst this
                decide
            · by_cases h_mid : n < 253
              · have : n = 252 := by omega
                subst this
                decide
              · have : n = 253 := by omega
                subst this
                decide
          · by_cases h_mid : n < 256
            · by_cases h_mid : n < 255
              · have : n = 254 := by omega
                subst this
                decide
              · have : n = 255 := by omega
                subst this
                decide
            · have : n = 256 := by omega
              subst this
              decide
        · by_cases h_mid : n < 260
          · by_cases h_mid : n < 259
            · by_cases h_mid : n < 258
              · have : n = 257 := by omega
                subst this
                decide
              · have : n = 258 := by omega
                subst this
                decide
            · have : n = 259 := by omega
              subst this
              decide
          · by_cases h_mid : n < 262
            · by_cases h_mid : n < 261
              · have : n = 260 := by omega
                subst this
                decide
              · have : n = 261 := by omega
                subst this
                decide
            · have : n = 262 := by omega
              subst this
              decide
      · by_cases h_mid : n < 269
        · by_cases h_mid : n < 266
          · by_cases h_mid : n < 265
            · by_cases h_mid : n < 264
              · have : n = 263 := by omega
                subst this
                decide
              · have : n = 264 := by omega
                subst this
                decide
            · have : n = 265 := by omega
              subst this
              decide
          · by_cases h_mid : n < 268
            · by_cases h_mid : n < 267
              · have : n = 266 := by omega
                subst this
                decide
              · have : n = 267 := by omega
                subst this
                decide
            · have : n = 268 := by omega
              subst this
              decide
        · by_cases h_mid : n < 272
          · by_cases h_mid : n < 271
            · by_cases h_mid : n < 270
              · have : n = 269 := by omega
                subst this
                decide
              · have : n = 270 := by omega
                subst this
                decide
            · have : n = 271 := by omega
              subst this
              decide
          · by_cases h_mid : n < 274
            · by_cases h_mid : n < 273
              · have : n = 272 := by omega
                subst this
                decide
              · have : n = 273 := by omega
                subst this
                decide
            · have : n = 274 := by omega
              subst this
              decide
    · by_cases h_mid : n < 288
      · by_cases h_mid : n < 282
        · by_cases h_mid : n < 279
          · by_cases h_mid : n < 277
            · by_cases h_mid : n < 276
              · have : n = 275 := by omega
                subst this
                decide
              · have : n = 276 := by omega
                subst this
                decide
            · by_cases h_mid : n < 278
              · have : n = 277 := by omega
                subst this
                decide
              · have : n = 278 := by omega
                subst this
                decide
          · by_cases h_mid : n < 281
            · by_cases h_mid : n < 280
              · have : n = 279 := by omega
                subst this
                decide
              · have : n = 280 := by omega
                subst this
                decide
            · have : n = 281 := by omega
              subst this
              decide
        · by_cases h_mid : n < 285
          · by_cases h_mid : n < 284
            · by_cases h_mid : n < 283
              · have : n = 282 := by omega
                subst this
                decide
              · have : n = 283 := by omega
                subst this
                decide
            · have : n = 284 := by omega
              subst this
              decide
          · by_cases h_mid : n < 287
            · by_cases h_mid : n < 286
              · have : n = 285 := by omega
                subst this
                decide
              · have : n = 286 := by omega
                subst this
                decide
            · have : n = 287 := by omega
              subst this
              decide
      · by_cases h_mid : n < 294
        · by_cases h_mid : n < 291
          · by_cases h_mid : n < 290
            · by_cases h_mid : n < 289
              · have : n = 288 := by omega
                subst this
                decide
              · have : n = 289 := by omega
                subst this
                decide
            · have : n = 290 := by omega
              subst this
              decide
          · by_cases h_mid : n < 293
            · by_cases h_mid : n < 292
              · have : n = 291 := by omega
                subst this
                decide
              · have : n = 292 := by omega
                subst this
                decide
            · have : n = 293 := by omega
              subst this
              decide
        · by_cases h_mid : n < 297
          · by_cases h_mid : n < 296
            · by_cases h_mid : n < 295
              · have : n = 294 := by omega
                subst this
                decide
              · have : n = 295 := by omega
                subst this
                decide
            · have : n = 296 := by omega
              subst this
              decide
          · by_cases h_mid : n < 299
            · by_cases h_mid : n < 298
              · have : n = 297 := by omega
                subst this
                decide
              · have : n = 298 := by omega
                subst this
                decide
            · have : n = 299 := by omega
              subst this
              decide

lemma witness_pos_and_mod_3 (n : ℕ) (h1 : 300 ≤ n) (h2 : n < 400) : witness n > 0 ∧ (witness n - 1) % Nat.totient (witness n) = n := by
  by_cases h_mid : n < 350
  · by_cases h_mid : n < 325
    · by_cases h_mid : n < 313
      · by_cases h_mid : n < 307
        · by_cases h_mid : n < 304
          · by_cases h_mid : n < 302
            · by_cases h_mid : n < 301
              · have : n = 300 := by omega
                subst this
                decide
              · have : n = 301 := by omega
                subst this
                decide
            · by_cases h_mid : n < 303
              · have : n = 302 := by omega
                subst this
                decide
              · have : n = 303 := by omega
                subst this
                decide
          · by_cases h_mid : n < 306
            · by_cases h_mid : n < 305
              · have : n = 304 := by omega
                subst this
                decide
              · have : n = 305 := by omega
                subst this
                decide
            · have : n = 306 := by omega
              subst this
              decide
        · by_cases h_mid : n < 310
          · by_cases h_mid : n < 309
            · by_cases h_mid : n < 308
              · have : n = 307 := by omega
                subst this
                decide
              · have : n = 308 := by omega
                subst this
                decide
            · have : n = 309 := by omega
              subst this
              decide
          · by_cases h_mid : n < 312
            · by_cases h_mid : n < 311
              · have : n = 310 := by omega
                subst this
                decide
              · have : n = 311 := by omega
                subst this
                decide
            · have : n = 312 := by omega
              subst this
              decide
      · by_cases h_mid : n < 319
        · by_cases h_mid : n < 316
          · by_cases h_mid : n < 315
            · by_cases h_mid : n < 314
              · have : n = 313 := by omega
                subst this
                decide
              · have : n = 314 := by omega
                subst this
                decide
            · have : n = 315 := by omega
              subst this
              decide
          · by_cases h_mid : n < 318
            · by_cases h_mid : n < 317
              · have : n = 316 := by omega
                subst this
                decide
              · have : n = 317 := by omega
                subst this
                decide
            · have : n = 318 := by omega
              subst this
              decide
        · by_cases h_mid : n < 322
          · by_cases h_mid : n < 321
            · by_cases h_mid : n < 320
              · have : n = 319 := by omega
                subst this
                decide
              · have : n = 320 := by omega
                subst this
                decide
            · have : n = 321 := by omega
              subst this
              decide
          · by_cases h_mid : n < 324
            · by_cases h_mid : n < 323
              · have : n = 322 := by omega
                subst this
                decide
              · have : n = 323 := by omega
                subst this
                decide
            · have : n = 324 := by omega
              subst this
              decide
    · by_cases h_mid : n < 338
      · by_cases h_mid : n < 332
        · by_cases h_mid : n < 329
          · by_cases h_mid : n < 327
            · by_cases h_mid : n < 326
              · have : n = 325 := by omega
                subst this
                decide
              · have : n = 326 := by omega
                subst this
                decide
            · by_cases h_mid : n < 328
              · have : n = 327 := by omega
                subst this
                decide
              · have : n = 328 := by omega
                subst this
                decide
          · by_cases h_mid : n < 331
            · by_cases h_mid : n < 330
              · have : n = 329 := by omega
                subst this
                decide
              · have : n = 330 := by omega
                subst this
                decide
            · have : n = 331 := by omega
              subst this
              decide
        · by_cases h_mid : n < 335
          · by_cases h_mid : n < 334
            · by_cases h_mid : n < 333
              · have : n = 332 := by omega
                subst this
                decide
              · have : n = 333 := by omega
                subst this
                decide
            · have : n = 334 := by omega
              subst this
              decide
          · by_cases h_mid : n < 337
            · by_cases h_mid : n < 336
              · have : n = 335 := by omega
                subst this
                decide
              · have : n = 336 := by omega
                subst this
                decide
            · have : n = 337 := by omega
              subst this
              decide
      · by_cases h_mid : n < 344
        · by_cases h_mid : n < 341
          · by_cases h_mid : n < 340
            · by_cases h_mid : n < 339
              · have : n = 338 := by omega
                subst this
                decide
              · have : n = 339 := by omega
                subst this
                decide
            · have : n = 340 := by omega
              subst this
              decide
          · by_cases h_mid : n < 343
            · by_cases h_mid : n < 342
              · have : n = 341 := by omega
                subst this
                decide
              · have : n = 342 := by omega
                subst this
                decide
            · have : n = 343 := by omega
              subst this
              decide
        · by_cases h_mid : n < 347
          · by_cases h_mid : n < 346
            · by_cases h_mid : n < 345
              · have : n = 344 := by omega
                subst this
                decide
              · have : n = 345 := by omega
                subst this
                decide
            · have : n = 346 := by omega
              subst this
              decide
          · by_cases h_mid : n < 349
            · by_cases h_mid : n < 348
              · have : n = 347 := by omega
                subst this
                decide
              · have : n = 348 := by omega
                subst this
                decide
            · have : n = 349 := by omega
              subst this
              decide
  · by_cases h_mid : n < 375
    · by_cases h_mid : n < 363
      · by_cases h_mid : n < 357
        · by_cases h_mid : n < 354
          · by_cases h_mid : n < 352
            · by_cases h_mid : n < 351
              · have : n = 350 := by omega
                subst this
                decide
              · have : n = 351 := by omega
                subst this
                decide
            · by_cases h_mid : n < 353
              · have : n = 352 := by omega
                subst this
                decide
              · have : n = 353 := by omega
                subst this
                decide
          · by_cases h_mid : n < 356
            · by_cases h_mid : n < 355
              · have : n = 354 := by omega
                subst this
                decide
              · have : n = 355 := by omega
                subst this
                decide
            · have : n = 356 := by omega
              subst this
              decide
        · by_cases h_mid : n < 360
          · by_cases h_mid : n < 359
            · by_cases h_mid : n < 358
              · have : n = 357 := by omega
                subst this
                decide
              · have : n = 358 := by omega
                subst this
                decide
            · have : n = 359 := by omega
              subst this
              decide
          · by_cases h_mid : n < 362
            · by_cases h_mid : n < 361
              · have : n = 360 := by omega
                subst this
                decide
              · have : n = 361 := by omega
                subst this
                decide
            · have : n = 362 := by omega
              subst this
              decide
      · by_cases h_mid : n < 369
        · by_cases h_mid : n < 366
          · by_cases h_mid : n < 365
            · by_cases h_mid : n < 364
              · have : n = 363 := by omega
                subst this
                decide
              · have : n = 364 := by omega
                subst this
                decide
            · have : n = 365 := by omega
              subst this
              decide
          · by_cases h_mid : n < 368
            · by_cases h_mid : n < 367
              · have : n = 366 := by omega
                subst this
                decide
              · have : n = 367 := by omega
                subst this
                decide
            · have : n = 368 := by omega
              subst this
              decide
        · by_cases h_mid : n < 372
          · by_cases h_mid : n < 371
            · by_cases h_mid : n < 370
              · have : n = 369 := by omega
                subst this
                decide
              · have : n = 370 := by omega
                subst this
                decide
            · have : n = 371 := by omega
              subst this
              decide
          · by_cases h_mid : n < 374
            · by_cases h_mid : n < 373
              · have : n = 372 := by omega
                subst this
                decide
              · have : n = 373 := by omega
                subst this
                decide
            · have : n = 374 := by omega
              subst this
              decide
    · by_cases h_mid : n < 388
      · by_cases h_mid : n < 382
        · by_cases h_mid : n < 379
          · by_cases h_mid : n < 377
            · by_cases h_mid : n < 376
              · have : n = 375 := by omega
                subst this
                decide
              · have : n = 376 := by omega
                subst this
                decide
            · by_cases h_mid : n < 378
              · have : n = 377 := by omega
                subst this
                decide
              · have : n = 378 := by omega
                subst this
                decide
          · by_cases h_mid : n < 381
            · by_cases h_mid : n < 380
              · have : n = 379 := by omega
                subst this
                decide
              · have : n = 380 := by omega
                subst this
                decide
            · have : n = 381 := by omega
              subst this
              decide
        · by_cases h_mid : n < 385
          · by_cases h_mid : n < 384
            · by_cases h_mid : n < 383
              · have : n = 382 := by omega
                subst this
                decide
              · have : n = 383 := by omega
                subst this
                decide
            · have : n = 384 := by omega
              subst this
              decide
          · by_cases h_mid : n < 387
            · by_cases h_mid : n < 386
              · have : n = 385 := by omega
                subst this
                decide
              · have : n = 386 := by omega
                subst this
                decide
            · have : n = 387 := by omega
              subst this
              decide
      · by_cases h_mid : n < 394
        · by_cases h_mid : n < 391
          · by_cases h_mid : n < 390
            · by_cases h_mid : n < 389
              · have : n = 388 := by omega
                subst this
                decide
              · have : n = 389 := by omega
                subst this
                decide
            · have : n = 390 := by omega
              subst this
              decide
          · by_cases h_mid : n < 393
            · by_cases h_mid : n < 392
              · have : n = 391 := by omega
                subst this
                decide
              · have : n = 392 := by omega
                subst this
                decide
            · have : n = 393 := by omega
              subst this
              decide
        · by_cases h_mid : n < 397
          · by_cases h_mid : n < 396
            · by_cases h_mid : n < 395
              · have : n = 394 := by omega
                subst this
                decide
              · have : n = 395 := by omega
                subst this
                decide
            · have : n = 396 := by omega
              subst this
              decide
          · by_cases h_mid : n < 399
            · by_cases h_mid : n < 398
              · have : n = 397 := by omega
                subst this
                decide
              · have : n = 398 := by omega
                subst this
                decide
            · have : n = 399 := by omega
              subst this
              decide

lemma witness_pos_and_mod_4 (n : ℕ) (h1 : 400 ≤ n) (h2 : n < 500) : witness n > 0 ∧ (witness n - 1) % Nat.totient (witness n) = n := by
  by_cases h_mid : n < 450
  · by_cases h_mid : n < 425
    · by_cases h_mid : n < 413
      · by_cases h_mid : n < 407
        · by_cases h_mid : n < 404
          · by_cases h_mid : n < 402
            · by_cases h_mid : n < 401
              · have : n = 400 := by omega
                subst this
                decide
              · have : n = 401 := by omega
                subst this
                decide
            · by_cases h_mid : n < 403
              · have : n = 402 := by omega
                subst this
                decide
              · have : n = 403 := by omega
                subst this
                decide
          · by_cases h_mid : n < 406
            · by_cases h_mid : n < 405
              · have : n = 404 := by omega
                subst this
                decide
              · have : n = 405 := by omega
                subst this
                decide
            · have : n = 406 := by omega
              subst this
              decide
        · by_cases h_mid : n < 410
          · by_cases h_mid : n < 409
            · by_cases h_mid : n < 408
              · have : n = 407 := by omega
                subst this
                decide
              · have : n = 408 := by omega
                subst this
                decide
            · have : n = 409 := by omega
              subst this
              decide
          · by_cases h_mid : n < 412
            · by_cases h_mid : n < 411
              · have : n = 410 := by omega
                subst this
                decide
              · have : n = 411 := by omega
                subst this
                decide
            · have : n = 412 := by omega
              subst this
              decide
      · by_cases h_mid : n < 419
        · by_cases h_mid : n < 416
          · by_cases h_mid : n < 415
            · by_cases h_mid : n < 414
              · have : n = 413 := by omega
                subst this
                decide
              · have : n = 414 := by omega
                subst this
                decide
            · have : n = 415 := by omega
              subst this
              decide
          · by_cases h_mid : n < 418
            · by_cases h_mid : n < 417
              · have : n = 416 := by omega
                subst this
                decide
              · have : n = 417 := by omega
                subst this
                decide
            · have : n = 418 := by omega
              subst this
              decide
        · by_cases h_mid : n < 422
          · by_cases h_mid : n < 421
            · by_cases h_mid : n < 420
              · have : n = 419 := by omega
                subst this
                decide
              · have : n = 420 := by omega
                subst this
                decide
            · have : n = 421 := by omega
              subst this
              decide
          · by_cases h_mid : n < 424
            · by_cases h_mid : n < 423
              · have : n = 422 := by omega
                subst this
                decide
              · have : n = 423 := by omega
                subst this
                decide
            · have : n = 424 := by omega
              subst this
              decide
    · by_cases h_mid : n < 438
      · by_cases h_mid : n < 432
        · by_cases h_mid : n < 429
          · by_cases h_mid : n < 427
            · by_cases h_mid : n < 426
              · have : n = 425 := by omega
                subst this
                decide
              · have : n = 426 := by omega
                subst this
                decide
            · by_cases h_mid : n < 428
              · have : n = 427 := by omega
                subst this
                decide
              · have : n = 428 := by omega
                subst this
                decide
          · by_cases h_mid : n < 431
            · by_cases h_mid : n < 430
              · have : n = 429 := by omega
                subst this
                decide
              · have : n = 430 := by omega
                subst this
                decide
            · have : n = 431 := by omega
              subst this
              decide
        · by_cases h_mid : n < 435
          · by_cases h_mid : n < 434
            · by_cases h_mid : n < 433
              · have : n = 432 := by omega
                subst this
                decide
              · have : n = 433 := by omega
                subst this
                decide
            · have : n = 434 := by omega
              subst this
              decide
          · by_cases h_mid : n < 437
            · by_cases h_mid : n < 436
              · have : n = 435 := by omega
                subst this
                decide
              · have : n = 436 := by omega
                subst this
                decide
            · have : n = 437 := by omega
              subst this
              decide
      · by_cases h_mid : n < 444
        · by_cases h_mid : n < 441
          · by_cases h_mid : n < 440
            · by_cases h_mid : n < 439
              · have : n = 438 := by omega
                subst this
                decide
              · have : n = 439 := by omega
                subst this
                decide
            · have : n = 440 := by omega
              subst this
              decide
          · by_cases h_mid : n < 443
            · by_cases h_mid : n < 442
              · have : n = 441 := by omega
                subst this
                decide
              · have : n = 442 := by omega
                subst this
                decide
            · have : n = 443 := by omega
              subst this
              decide
        · by_cases h_mid : n < 447
          · by_cases h_mid : n < 446
            · by_cases h_mid : n < 445
              · have : n = 444 := by omega
                subst this
                decide
              · have : n = 445 := by omega
                subst this
                decide
            · have : n = 446 := by omega
              subst this
              decide
          · by_cases h_mid : n < 449
            · by_cases h_mid : n < 448
              · have : n = 447 := by omega
                subst this
                decide
              · have : n = 448 := by omega
                subst this
                decide
            · have : n = 449 := by omega
              subst this
              decide
  · by_cases h_mid : n < 475
    · by_cases h_mid : n < 463
      · by_cases h_mid : n < 457
        · by_cases h_mid : n < 454
          · by_cases h_mid : n < 452
            · by_cases h_mid : n < 451
              · have : n = 450 := by omega
                subst this
                decide
              · have : n = 451 := by omega
                subst this
                decide
            · by_cases h_mid : n < 453
              · have : n = 452 := by omega
                subst this
                decide
              · have : n = 453 := by omega
                subst this
                decide
          · by_cases h_mid : n < 456
            · by_cases h_mid : n < 455
              · have : n = 454 := by omega
                subst this
                decide
              · have : n = 455 := by omega
                subst this
                decide
            · have : n = 456 := by omega
              subst this
              decide
        · by_cases h_mid : n < 460
          · by_cases h_mid : n < 459
            · by_cases h_mid : n < 458
              · have : n = 457 := by omega
                subst this
                decide
              · have : n = 458 := by omega
                subst this
                decide
            · have : n = 459 := by omega
              subst this
              decide
          · by_cases h_mid : n < 462
            · by_cases h_mid : n < 461
              · have : n = 460 := by omega
                subst this
                decide
              · have : n = 461 := by omega
                subst this
                decide
            · have : n = 462 := by omega
              subst this
              decide
      · by_cases h_mid : n < 469
        · by_cases h_mid : n < 466
          · by_cases h_mid : n < 465
            · by_cases h_mid : n < 464
              · have : n = 463 := by omega
                subst this
                decide
              · have : n = 464 := by omega
                subst this
                decide
            · have : n = 465 := by omega
              subst this
              decide
          · by_cases h_mid : n < 468
            · by_cases h_mid : n < 467
              · have : n = 466 := by omega
                subst this
                decide
              · have : n = 467 := by omega
                subst this
                decide
            · have : n = 468 := by omega
              subst this
              decide
        · by_cases h_mid : n < 472
          · by_cases h_mid : n < 471
            · by_cases h_mid : n < 470
              · have : n = 469 := by omega
                subst this
                decide
              · have : n = 470 := by omega
                subst this
                decide
            · have : n = 471 := by omega
              subst this
              decide
          · by_cases h_mid : n < 474
            · by_cases h_mid : n < 473
              · have : n = 472 := by omega
                subst this
                decide
              · have : n = 473 := by omega
                subst this
                decide
            · have : n = 474 := by omega
              subst this
              decide
    · by_cases h_mid : n < 488
      · by_cases h_mid : n < 482
        · by_cases h_mid : n < 479
          · by_cases h_mid : n < 477
            · by_cases h_mid : n < 476
              · have : n = 475 := by omega
                subst this
                decide
              · have : n = 476 := by omega
                subst this
                decide
            · by_cases h_mid : n < 478
              · have : n = 477 := by omega
                subst this
                decide
              · have : n = 478 := by omega
                subst this
                decide
          · by_cases h_mid : n < 481
            · by_cases h_mid : n < 480
              · have : n = 479 := by omega
                subst this
                decide
              · have : n = 480 := by omega
                subst this
                decide
            · have : n = 481 := by omega
              subst this
              decide
        · by_cases h_mid : n < 485
          · by_cases h_mid : n < 484
            · by_cases h_mid : n < 483
              · have : n = 482 := by omega
                subst this
                decide
              · have : n = 483 := by omega
                subst this
                decide
            · have : n = 484 := by omega
              subst this
              decide
          · by_cases h_mid : n < 487
            · by_cases h_mid : n < 486
              · have : n = 485 := by omega
                subst this
                decide
              · have : n = 486 := by omega
                subst this
                decide
            · have : n = 487 := by omega
              subst this
              decide
      · by_cases h_mid : n < 494
        · by_cases h_mid : n < 491
          · by_cases h_mid : n < 490
            · by_cases h_mid : n < 489
              · have : n = 488 := by omega
                subst this
                decide
              · have : n = 489 := by omega
                subst this
                decide
            · have : n = 490 := by omega
              subst this
              decide
          · by_cases h_mid : n < 493
            · by_cases h_mid : n < 492
              · have : n = 491 := by omega
                subst this
                decide
              · have : n = 492 := by omega
                subst this
                decide
            · have : n = 493 := by omega
              subst this
              decide
        · by_cases h_mid : n < 497
          · by_cases h_mid : n < 496
            · by_cases h_mid : n < 495
              · have : n = 494 := by omega
                subst this
                decide
              · have : n = 495 := by omega
                subst this
                decide
            · have : n = 496 := by omega
              subst this
              decide
          · by_cases h_mid : n < 499
            · by_cases h_mid : n < 498
              · have : n = 497 := by omega
                subst this
                decide
              · have : n = 498 := by omega
                subst this
                decide
            · have : n = 499 := by omega
              subst this
              decide

lemma witness_pos_and_mod_5 (n : ℕ) (h1 : 500 ≤ n) (h2 : n < 600) : witness n > 0 ∧ (witness n - 1) % Nat.totient (witness n) = n := by
  by_cases h_mid : n < 550
  · by_cases h_mid : n < 525
    · by_cases h_mid : n < 513
      · by_cases h_mid : n < 507
        · by_cases h_mid : n < 504
          · by_cases h_mid : n < 502
            · by_cases h_mid : n < 501
              · have : n = 500 := by omega
                subst this
                decide
              · have : n = 501 := by omega
                subst this
                decide
            · by_cases h_mid : n < 503
              · have : n = 502 := by omega
                subst this
                decide
              · have : n = 503 := by omega
                subst this
                decide
          · by_cases h_mid : n < 506
            · by_cases h_mid : n < 505
              · have : n = 504 := by omega
                subst this
                decide
              · have : n = 505 := by omega
                subst this
                decide
            · have : n = 506 := by omega
              subst this
              decide
        · by_cases h_mid : n < 510
          · by_cases h_mid : n < 509
            · by_cases h_mid : n < 508
              · have : n = 507 := by omega
                subst this
                decide
              · have : n = 508 := by omega
                subst this
                decide
            · have : n = 509 := by omega
              subst this
              decide
          · by_cases h_mid : n < 512
            · by_cases h_mid : n < 511
              · have : n = 510 := by omega
                subst this
                decide
              · have : n = 511 := by omega
                subst this
                decide
            · have : n = 512 := by omega
              subst this
              decide
      · by_cases h_mid : n < 519
        · by_cases h_mid : n < 516
          · by_cases h_mid : n < 515
            · by_cases h_mid : n < 514
              · have : n = 513 := by omega
                subst this
                decide
              · have : n = 514 := by omega
                subst this
                decide
            · have : n = 515 := by omega
              subst this
              decide
          · by_cases h_mid : n < 518
            · by_cases h_mid : n < 517
              · have : n = 516 := by omega
                subst this
                decide
              · have : n = 517 := by omega
                subst this
                decide
            · have : n = 518 := by omega
              subst this
              decide
        · by_cases h_mid : n < 522
          · by_cases h_mid : n < 521
            · by_cases h_mid : n < 520
              · have : n = 519 := by omega
                subst this
                decide
              · have : n = 520 := by omega
                subst this
                decide
            · have : n = 521 := by omega
              subst this
              decide
          · by_cases h_mid : n < 524
            · by_cases h_mid : n < 523
              · have : n = 522 := by omega
                subst this
                decide
              · have : n = 523 := by omega
                subst this
                decide
            · have : n = 524 := by omega
              subst this
              decide
    · by_cases h_mid : n < 538
      · by_cases h_mid : n < 532
        · by_cases h_mid : n < 529
          · by_cases h_mid : n < 527
            · by_cases h_mid : n < 526
              · have : n = 525 := by omega
                subst this
                decide
              · have : n = 526 := by omega
                subst this
                decide
            · by_cases h_mid : n < 528
              · have : n = 527 := by omega
                subst this
                decide
              · have : n = 528 := by omega
                subst this
                decide
          · by_cases h_mid : n < 531
            · by_cases h_mid : n < 530
              · have : n = 529 := by omega
                subst this
                decide
              · have : n = 530 := by omega
                subst this
                decide
            · have : n = 531 := by omega
              subst this
              decide
        · by_cases h_mid : n < 535
          · by_cases h_mid : n < 534
            · by_cases h_mid : n < 533
              · have : n = 532 := by omega
                subst this
                decide
              · have : n = 533 := by omega
                subst this
                decide
            · have : n = 534 := by omega
              subst this
              decide
          · by_cases h_mid : n < 537
            · by_cases h_mid : n < 536
              · have : n = 535 := by omega
                subst this
                decide
              · have : n = 536 := by omega
                subst this
                decide
            · have : n = 537 := by omega
              subst this
              decide
      · by_cases h_mid : n < 544
        · by_cases h_mid : n < 541
          · by_cases h_mid : n < 540
            · by_cases h_mid : n < 539
              · have : n = 538 := by omega
                subst this
                decide
              · have : n = 539 := by omega
                subst this
                decide
            · have : n = 540 := by omega
              subst this
              decide
          · by_cases h_mid : n < 543
            · by_cases h_mid : n < 542
              · have : n = 541 := by omega
                subst this
                decide
              · have : n = 542 := by omega
                subst this
                decide
            · have : n = 543 := by omega
              subst this
              decide
        · by_cases h_mid : n < 547
          · by_cases h_mid : n < 546
            · by_cases h_mid : n < 545
              · have : n = 544 := by omega
                subst this
                decide
              · have : n = 545 := by omega
                subst this
                decide
            · have : n = 546 := by omega
              subst this
              decide
          · by_cases h_mid : n < 549
            · by_cases h_mid : n < 548
              · have : n = 547 := by omega
                subst this
                decide
              · have : n = 548 := by omega
                subst this
                decide
            · have : n = 549 := by omega
              subst this
              decide
  · by_cases h_mid : n < 575
    · by_cases h_mid : n < 563
      · by_cases h_mid : n < 557
        · by_cases h_mid : n < 554
          · by_cases h_mid : n < 552
            · by_cases h_mid : n < 551
              · have : n = 550 := by omega
                subst this
                decide
              · have : n = 551 := by omega
                subst this
                decide
            · by_cases h_mid : n < 553
              · have : n = 552 := by omega
                subst this
                decide
              · have : n = 553 := by omega
                subst this
                decide
          · by_cases h_mid : n < 556
            · by_cases h_mid : n < 555
              · have : n = 554 := by omega
                subst this
                decide
              · have : n = 555 := by omega
                subst this
                decide
            · have : n = 556 := by omega
              subst this
              decide
        · by_cases h_mid : n < 560
          · by_cases h_mid : n < 559
            · by_cases h_mid : n < 558
              · have : n = 557 := by omega
                subst this
                decide
              · have : n = 558 := by omega
                subst this
                decide
            · have : n = 559 := by omega
              subst this
              decide
          · by_cases h_mid : n < 562
            · by_cases h_mid : n < 561
              · have : n = 560 := by omega
                subst this
                decide
              · have : n = 561 := by omega
                subst this
                decide
            · have : n = 562 := by omega
              subst this
              decide
      · by_cases h_mid : n < 569
        · by_cases h_mid : n < 566
          · by_cases h_mid : n < 565
            · by_cases h_mid : n < 564
              · have : n = 563 := by omega
                subst this
                decide
              · have : n = 564 := by omega
                subst this
                decide
            · have : n = 565 := by omega
              subst this
              decide
          · by_cases h_mid : n < 568
            · by_cases h_mid : n < 567
              · have : n = 566 := by omega
                subst this
                decide
              · have : n = 567 := by omega
                subst this
                decide
            · have : n = 568 := by omega
              subst this
              decide
        · by_cases h_mid : n < 572
          · by_cases h_mid : n < 571
            · by_cases h_mid : n < 570
              · have : n = 569 := by omega
                subst this
                decide
              · have : n = 570 := by omega
                subst this
                decide
            · have : n = 571 := by omega
              subst this
              decide
          · by_cases h_mid : n < 574
            · by_cases h_mid : n < 573
              · have : n = 572 := by omega
                subst this
                decide
              · have : n = 573 := by omega
                subst this
                decide
            · have : n = 574 := by omega
              subst this
              decide
    · by_cases h_mid : n < 588
      · by_cases h_mid : n < 582
        · by_cases h_mid : n < 579
          · by_cases h_mid : n < 577
            · by_cases h_mid : n < 576
              · have : n = 575 := by omega
                subst this
                decide
              · have : n = 576 := by omega
                subst this
                decide
            · by_cases h_mid : n < 578
              · have : n = 577 := by omega
                subst this
                decide
              · have : n = 578 := by omega
                subst this
                decide
          · by_cases h_mid : n < 581
            · by_cases h_mid : n < 580
              · have : n = 579 := by omega
                subst this
                decide
              · have : n = 580 := by omega
                subst this
                decide
            · have : n = 581 := by omega
              subst this
              decide
        · by_cases h_mid : n < 585
          · by_cases h_mid : n < 584
            · by_cases h_mid : n < 583
              · have : n = 582 := by omega
                subst this
                decide
              · have : n = 583 := by omega
                subst this
                decide
            · have : n = 584 := by omega
              subst this
              decide
          · by_cases h_mid : n < 587
            · by_cases h_mid : n < 586
              · have : n = 585 := by omega
                subst this
                decide
              · have : n = 586 := by omega
                subst this
                decide
            · have : n = 587 := by omega
              subst this
              decide
      · by_cases h_mid : n < 594
        · by_cases h_mid : n < 591
          · by_cases h_mid : n < 590
            · by_cases h_mid : n < 589
              · have : n = 588 := by omega
                subst this
                decide
              · have : n = 589 := by omega
                subst this
                decide
            · have : n = 590 := by omega
              subst this
              decide
          · by_cases h_mid : n < 593
            · by_cases h_mid : n < 592
              · have : n = 591 := by omega
                subst this
                decide
              · have : n = 592 := by omega
                subst this
                decide
            · have : n = 593 := by omega
              subst this
              decide
        · by_cases h_mid : n < 597
          · by_cases h_mid : n < 596
            · by_cases h_mid : n < 595
              · have : n = 594 := by omega
                subst this
                decide
              · have : n = 595 := by omega
                subst this
                decide
            · have : n = 596 := by omega
              subst this
              decide
          · by_cases h_mid : n < 599
            · by_cases h_mid : n < 598
              · have : n = 597 := by omega
                subst this
                decide
              · have : n = 598 := by omega
                subst this
                decide
            · have : n = 599 := by omega
              subst this
              decide

lemma witness_pos_and_mod_6 (n : ℕ) (h1 : 600 ≤ n) (h2 : n < 700) : witness n > 0 ∧ (witness n - 1) % Nat.totient (witness n) = n := by
  by_cases h_mid : n < 650
  · by_cases h_mid : n < 625
    · by_cases h_mid : n < 613
      · by_cases h_mid : n < 607
        · by_cases h_mid : n < 604
          · by_cases h_mid : n < 602
            · by_cases h_mid : n < 601
              · have : n = 600 := by omega
                subst this
                decide
              · have : n = 601 := by omega
                subst this
                decide
            · by_cases h_mid : n < 603
              · have : n = 602 := by omega
                subst this
                decide
              · have : n = 603 := by omega
                subst this
                decide
          · by_cases h_mid : n < 606
            · by_cases h_mid : n < 605
              · have : n = 604 := by omega
                subst this
                decide
              · have : n = 605 := by omega
                subst this
                decide
            · have : n = 606 := by omega
              subst this
              decide
        · by_cases h_mid : n < 610
          · by_cases h_mid : n < 609
            · by_cases h_mid : n < 608
              · have : n = 607 := by omega
                subst this
                decide
              · have : n = 608 := by omega
                subst this
                decide
            · have : n = 609 := by omega
              subst this
              decide
          · by_cases h_mid : n < 612
            · by_cases h_mid : n < 611
              · have : n = 610 := by omega
                subst this
                decide
              · have : n = 611 := by omega
                subst this
                decide
            · have : n = 612 := by omega
              subst this
              decide
      · by_cases h_mid : n < 619
        · by_cases h_mid : n < 616
          · by_cases h_mid : n < 615
            · by_cases h_mid : n < 614
              · have : n = 613 := by omega
                subst this
                decide
              · have : n = 614 := by omega
                subst this
                decide
            · have : n = 615 := by omega
              subst this
              decide
          · by_cases h_mid : n < 618
            · by_cases h_mid : n < 617
              · have : n = 616 := by omega
                subst this
                decide
              · have : n = 617 := by omega
                subst this
                decide
            · have : n = 618 := by omega
              subst this
              decide
        · by_cases h_mid : n < 622
          · by_cases h_mid : n < 621
            · by_cases h_mid : n < 620
              · have : n = 619 := by omega
                subst this
                decide
              · have : n = 620 := by omega
                subst this
                decide
            · have : n = 621 := by omega
              subst this
              decide
          · by_cases h_mid : n < 624
            · by_cases h_mid : n < 623
              · have : n = 622 := by omega
                subst this
                decide
              · have : n = 623 := by omega
                subst this
                decide
            · have : n = 624 := by omega
              subst this
              decide
    · by_cases h_mid : n < 638
      · by_cases h_mid : n < 632
        · by_cases h_mid : n < 629
          · by_cases h_mid : n < 627
            · by_cases h_mid : n < 626
              · have : n = 625 := by omega
                subst this
                decide
              · have : n = 626 := by omega
                subst this
                decide
            · by_cases h_mid : n < 628
              · have : n = 627 := by omega
                subst this
                decide
              · have : n = 628 := by omega
                subst this
                decide
          · by_cases h_mid : n < 631
            · by_cases h_mid : n < 630
              · have : n = 629 := by omega
                subst this
                decide
              · have : n = 630 := by omega
                subst this
                decide
            · have : n = 631 := by omega
              subst this
              decide
        · by_cases h_mid : n < 635
          · by_cases h_mid : n < 634
            · by_cases h_mid : n < 633
              · have : n = 632 := by omega
                subst this
                decide
              · have : n = 633 := by omega
                subst this
                decide
            · have : n = 634 := by omega
              subst this
              decide
          · by_cases h_mid : n < 637
            · by_cases h_mid : n < 636
              · have : n = 635 := by omega
                subst this
                decide
              · have : n = 636 := by omega
                subst this
                decide
            · have : n = 637 := by omega
              subst this
              decide
      · by_cases h_mid : n < 644
        · by_cases h_mid : n < 641
          · by_cases h_mid : n < 640
            · by_cases h_mid : n < 639
              · have : n = 638 := by omega
                subst this
                decide
              · have : n = 639 := by omega
                subst this
                decide
            · have : n = 640 := by omega
              subst this
              decide
          · by_cases h_mid : n < 643
            · by_cases h_mid : n < 642
              · have : n = 641 := by omega
                subst this
                decide
              · have : n = 642 := by omega
                subst this
                decide
            · have : n = 643 := by omega
              subst this
              decide
        · by_cases h_mid : n < 647
          · by_cases h_mid : n < 646
            · by_cases h_mid : n < 645
              · have : n = 644 := by omega
                subst this
                decide
              · have : n = 645 := by omega
                subst this
                decide
            · have : n = 646 := by omega
              subst this
              decide
          · by_cases h_mid : n < 649
            · by_cases h_mid : n < 648
              · have : n = 647 := by omega
                subst this
                decide
              · have : n = 648 := by omega
                subst this
                decide
            · have : n = 649 := by omega
              subst this
              decide
  · by_cases h_mid : n < 675
    · by_cases h_mid : n < 663
      · by_cases h_mid : n < 657
        · by_cases h_mid : n < 654
          · by_cases h_mid : n < 652
            · by_cases h_mid : n < 651
              · have : n = 650 := by omega
                subst this
                decide
              · have : n = 651 := by omega
                subst this
                decide
            · by_cases h_mid : n < 653
              · have : n = 652 := by omega
                subst this
                decide
              · have : n = 653 := by omega
                subst this
                decide
          · by_cases h_mid : n < 656
            · by_cases h_mid : n < 655
              · have : n = 654 := by omega
                subst this
                decide
              · have : n = 655 := by omega
                subst this
                decide
            · have : n = 656 := by omega
              subst this
              decide
        · by_cases h_mid : n < 660
          · by_cases h_mid : n < 659
            · by_cases h_mid : n < 658
              · have : n = 657 := by omega
                subst this
                decide
              · have : n = 658 := by omega
                subst this
                decide
            · have : n = 659 := by omega
              subst this
              decide
          · by_cases h_mid : n < 662
            · by_cases h_mid : n < 661
              · have : n = 660 := by omega
                subst this
                decide
              · have : n = 661 := by omega
                subst this
                decide
            · have : n = 662 := by omega
              subst this
              decide
      · by_cases h_mid : n < 669
        · by_cases h_mid : n < 666
          · by_cases h_mid : n < 665
            · by_cases h_mid : n < 664
              · have : n = 663 := by omega
                subst this
                decide
              · have : n = 664 := by omega
                subst this
                decide
            · have : n = 665 := by omega
              subst this
              decide
          · by_cases h_mid : n < 668
            · by_cases h_mid : n < 667
              · have : n = 666 := by omega
                subst this
                decide
              · have : n = 667 := by omega
                subst this
                decide
            · have : n = 668 := by omega
              subst this
              decide
        · by_cases h_mid : n < 672
          · by_cases h_mid : n < 671
            · by_cases h_mid : n < 670
              · have : n = 669 := by omega
                subst this
                decide
              · have : n = 670 := by omega
                subst this
                decide
            · have : n = 671 := by omega
              subst this
              decide
          · by_cases h_mid : n < 674
            · by_cases h_mid : n < 673
              · have : n = 672 := by omega
                subst this
                decide
              · have : n = 673 := by omega
                subst this
                decide
            · have : n = 674 := by omega
              subst this
              decide
    · by_cases h_mid : n < 688
      · by_cases h_mid : n < 682
        · by_cases h_mid : n < 679
          · by_cases h_mid : n < 677
            · by_cases h_mid : n < 676
              · have : n = 675 := by omega
                subst this
                decide
              · have : n = 676 := by omega
                subst this
                decide
            · by_cases h_mid : n < 678
              · have : n = 677 := by omega
                subst this
                decide
              · have : n = 678 := by omega
                subst this
                decide
          · by_cases h_mid : n < 681
            · by_cases h_mid : n < 680
              · have : n = 679 := by omega
                subst this
                decide
              · have : n = 680 := by omega
                subst this
                decide
            · have : n = 681 := by omega
              subst this
              decide
        · by_cases h_mid : n < 685
          · by_cases h_mid : n < 684
            · by_cases h_mid : n < 683
              · have : n = 682 := by omega
                subst this
                decide
              · have : n = 683 := by omega
                subst this
                decide
            · have : n = 684 := by omega
              subst this
              decide
          · by_cases h_mid : n < 687
            · by_cases h_mid : n < 686
              · have : n = 685 := by omega
                subst this
                decide
              · have : n = 686 := by omega
                subst this
                decide
            · have : n = 687 := by omega
              subst this
              decide
      · by_cases h_mid : n < 694
        · by_cases h_mid : n < 691
          · by_cases h_mid : n < 690
            · by_cases h_mid : n < 689
              · have : n = 688 := by omega
                subst this
                decide
              · have : n = 689 := by omega
                subst this
                decide
            · have : n = 690 := by omega
              subst this
              decide
          · by_cases h_mid : n < 693
            · by_cases h_mid : n < 692
              · have : n = 691 := by omega
                subst this
                decide
              · have : n = 692 := by omega
                subst this
                decide
            · have : n = 693 := by omega
              subst this
              decide
        · by_cases h_mid : n < 697
          · by_cases h_mid : n < 696
            · by_cases h_mid : n < 695
              · have : n = 694 := by omega
                subst this
                decide
              · have : n = 695 := by omega
                subst this
                decide
            · have : n = 696 := by omega
              subst this
              decide
          · by_cases h_mid : n < 699
            · by_cases h_mid : n < 698
              · have : n = 697 := by omega
                subst this
                decide
              · have : n = 698 := by omega
                subst this
                decide
            · have : n = 699 := by omega
              subst this
              decide

lemma witness_pos_and_mod_7 (n : ℕ) (h1 : 700 ≤ n) (h2 : n < 800) : witness n > 0 ∧ (witness n - 1) % Nat.totient (witness n) = n := by
  by_cases h_mid : n < 750
  · by_cases h_mid : n < 725
    · by_cases h_mid : n < 713
      · by_cases h_mid : n < 707
        · by_cases h_mid : n < 704
          · by_cases h_mid : n < 702
            · by_cases h_mid : n < 701
              · have : n = 700 := by omega
                subst this
                decide
              · have : n = 701 := by omega
                subst this
                decide
            · by_cases h_mid : n < 703
              · have : n = 702 := by omega
                subst this
                decide
              · have : n = 703 := by omega
                subst this
                decide
          · by_cases h_mid : n < 706
            · by_cases h_mid : n < 705
              · have : n = 704 := by omega
                subst this
                decide
              · have : n = 705 := by omega
                subst this
                decide
            · have : n = 706 := by omega
              subst this
              decide
        · by_cases h_mid : n < 710
          · by_cases h_mid : n < 709
            · by_cases h_mid : n < 708
              · have : n = 707 := by omega
                subst this
                decide
              · have : n = 708 := by omega
                subst this
                decide
            · have : n = 709 := by omega
              subst this
              decide
          · by_cases h_mid : n < 712
            · by_cases h_mid : n < 711
              · have : n = 710 := by omega
                subst this
                decide
              · have : n = 711 := by omega
                subst this
                decide
            · have : n = 712 := by omega
              subst this
              decide
      · by_cases h_mid : n < 719
        · by_cases h_mid : n < 716
          · by_cases h_mid : n < 715
            · by_cases h_mid : n < 714
              · have : n = 713 := by omega
                subst this
                decide
              · have : n = 714 := by omega
                subst this
                decide
            · have : n = 715 := by omega
              subst this
              decide
          · by_cases h_mid : n < 718
            · by_cases h_mid : n < 717
              · have : n = 716 := by omega
                subst this
                decide
              · have : n = 717 := by omega
                subst this
                decide
            · have : n = 718 := by omega
              subst this
              decide
        · by_cases h_mid : n < 722
          · by_cases h_mid : n < 721
            · by_cases h_mid : n < 720
              · have : n = 719 := by omega
                subst this
                decide
              · have : n = 720 := by omega
                subst this
                decide
            · have : n = 721 := by omega
              subst this
              decide
          · by_cases h_mid : n < 724
            · by_cases h_mid : n < 723
              · have : n = 722 := by omega
                subst this
                decide
              · have : n = 723 := by omega
                subst this
                decide
            · have : n = 724 := by omega
              subst this
              decide
    · by_cases h_mid : n < 738
      · by_cases h_mid : n < 732
        · by_cases h_mid : n < 729
          · by_cases h_mid : n < 727
            · by_cases h_mid : n < 726
              · have : n = 725 := by omega
                subst this
                decide
              · have : n = 726 := by omega
                subst this
                decide
            · by_cases h_mid : n < 728
              · have : n = 727 := by omega
                subst this
                decide
              · have : n = 728 := by omega
                subst this
                decide
          · by_cases h_mid : n < 731
            · by_cases h_mid : n < 730
              · have : n = 729 := by omega
                subst this
                decide
              · have : n = 730 := by omega
                subst this
                decide
            · have : n = 731 := by omega
              subst this
              decide
        · by_cases h_mid : n < 735
          · by_cases h_mid : n < 734
            · by_cases h_mid : n < 733
              · have : n = 732 := by omega
                subst this
                decide
              · have : n = 733 := by omega
                subst this
                decide
            · have : n = 734 := by omega
              subst this
              decide
          · by_cases h_mid : n < 737
            · by_cases h_mid : n < 736
              · have : n = 735 := by omega
                subst this
                decide
              · have : n = 736 := by omega
                subst this
                decide
            · have : n = 737 := by omega
              subst this
              decide
      · by_cases h_mid : n < 744
        · by_cases h_mid : n < 741
          · by_cases h_mid : n < 740
            · by_cases h_mid : n < 739
              · have : n = 738 := by omega
                subst this
                decide
              · have : n = 739 := by omega
                subst this
                decide
            · have : n = 740 := by omega
              subst this
              decide
          · by_cases h_mid : n < 743
            · by_cases h_mid : n < 742
              · have : n = 741 := by omega
                subst this
                decide
              · have : n = 742 := by omega
                subst this
                decide
            · have : n = 743 := by omega
              subst this
              decide
        · by_cases h_mid : n < 747
          · by_cases h_mid : n < 746
            · by_cases h_mid : n < 745
              · have : n = 744 := by omega
                subst this
                decide
              · have : n = 745 := by omega
                subst this
                decide
            · have : n = 746 := by omega
              subst this
              decide
          · by_cases h_mid : n < 749
            · by_cases h_mid : n < 748
              · have : n = 747 := by omega
                subst this
                decide
              · have : n = 748 := by omega
                subst this
                decide
            · have : n = 749 := by omega
              subst this
              decide
  · by_cases h_mid : n < 775
    · by_cases h_mid : n < 763
      · by_cases h_mid : n < 757
        · by_cases h_mid : n < 754
          · by_cases h_mid : n < 752
            · by_cases h_mid : n < 751
              · have : n = 750 := by omega
                subst this
                decide
              · have : n = 751 := by omega
                subst this
                decide
            · by_cases h_mid : n < 753
              · have : n = 752 := by omega
                subst this
                decide
              · have : n = 753 := by omega
                subst this
                decide
          · by_cases h_mid : n < 756
            · by_cases h_mid : n < 755
              · have : n = 754 := by omega
                subst this
                decide
              · have : n = 755 := by omega
                subst this
                decide
            · have : n = 756 := by omega
              subst this
              decide
        · by_cases h_mid : n < 760
          · by_cases h_mid : n < 759
            · by_cases h_mid : n < 758
              · have : n = 757 := by omega
                subst this
                decide
              · have : n = 758 := by omega
                subst this
                decide
            · have : n = 759 := by omega
              subst this
              decide
          · by_cases h_mid : n < 762
            · by_cases h_mid : n < 761
              · have : n = 760 := by omega
                subst this
                decide
              · have : n = 761 := by omega
                subst this
                decide
            · have : n = 762 := by omega
              subst this
              decide
      · by_cases h_mid : n < 769
        · by_cases h_mid : n < 766
          · by_cases h_mid : n < 765
            · by_cases h_mid : n < 764
              · have : n = 763 := by omega
                subst this
                decide
              · have : n = 764 := by omega
                subst this
                decide
            · have : n = 765 := by omega
              subst this
              decide
          · by_cases h_mid : n < 768
            · by_cases h_mid : n < 767
              · have : n = 766 := by omega
                subst this
                decide
              · have : n = 767 := by omega
                subst this
                decide
            · have : n = 768 := by omega
              subst this
              decide
        · by_cases h_mid : n < 772
          · by_cases h_mid : n < 771
            · by_cases h_mid : n < 770
              · have : n = 769 := by omega
                subst this
                decide
              · have : n = 770 := by omega
                subst this
                decide
            · have : n = 771 := by omega
              subst this
              decide
          · by_cases h_mid : n < 774
            · by_cases h_mid : n < 773
              · have : n = 772 := by omega
                subst this
                decide
              · have : n = 773 := by omega
                subst this
                decide
            · have : n = 774 := by omega
              subst this
              decide
    · by_cases h_mid : n < 788
      · by_cases h_mid : n < 782
        · by_cases h_mid : n < 779
          · by_cases h_mid : n < 777
            · by_cases h_mid : n < 776
              · have : n = 775 := by omega
                subst this
                decide
              · have : n = 776 := by omega
                subst this
                decide
            · by_cases h_mid : n < 778
              · have : n = 777 := by omega
                subst this
                decide
              · have : n = 778 := by omega
                subst this
                decide
          · by_cases h_mid : n < 781
            · by_cases h_mid : n < 780
              · have : n = 779 := by omega
                subst this
                decide
              · have : n = 780 := by omega
                subst this
                decide
            · have : n = 781 := by omega
              subst this
              decide
        · by_cases h_mid : n < 785
          · by_cases h_mid : n < 784
            · by_cases h_mid : n < 783
              · have : n = 782 := by omega
                subst this
                decide
              · have : n = 783 := by omega
                subst this
                decide
            · have : n = 784 := by omega
              subst this
              decide
          · by_cases h_mid : n < 787
            · by_cases h_mid : n < 786
              · have : n = 785 := by omega
                subst this
                decide
              · have : n = 786 := by omega
                subst this
                decide
            · have : n = 787 := by omega
              subst this
              decide
      · by_cases h_mid : n < 794
        · by_cases h_mid : n < 791
          · by_cases h_mid : n < 790
            · by_cases h_mid : n < 789
              · have : n = 788 := by omega
                subst this
                decide
              · have : n = 789 := by omega
                subst this
                decide
            · have : n = 790 := by omega
              subst this
              decide
          · by_cases h_mid : n < 793
            · by_cases h_mid : n < 792
              · have : n = 791 := by omega
                subst this
                decide
              · have : n = 792 := by omega
                subst this
                decide
            · have : n = 793 := by omega
              subst this
              decide
        · by_cases h_mid : n < 797
          · by_cases h_mid : n < 796
            · by_cases h_mid : n < 795
              · have : n = 794 := by omega
                subst this
                decide
              · have : n = 795 := by omega
                subst this
                decide
            · have : n = 796 := by omega
              subst this
              decide
          · by_cases h_mid : n < 799
            · by_cases h_mid : n < 798
              · have : n = 797 := by omega
                subst this
                decide
              · have : n = 798 := by omega
                subst this
                decide
            · have : n = 799 := by omega
              subst this
              decide

lemma witness_pos_and_mod_8 (n : ℕ) (h1 : 800 ≤ n) (h2 : n < 900) : witness n > 0 ∧ (witness n - 1) % Nat.totient (witness n) = n := by
  by_cases h_mid : n < 850
  · by_cases h_mid : n < 825
    · by_cases h_mid : n < 813
      · by_cases h_mid : n < 807
        · by_cases h_mid : n < 804
          · by_cases h_mid : n < 802
            · by_cases h_mid : n < 801
              · have : n = 800 := by omega
                subst this
                decide
              · have : n = 801 := by omega
                subst this
                decide
            · by_cases h_mid : n < 803
              · have : n = 802 := by omega
                subst this
                decide
              · have : n = 803 := by omega
                subst this
                decide
          · by_cases h_mid : n < 806
            · by_cases h_mid : n < 805
              · have : n = 804 := by omega
                subst this
                decide
              · have : n = 805 := by omega
                subst this
                decide
            · have : n = 806 := by omega
              subst this
              decide
        · by_cases h_mid : n < 810
          · by_cases h_mid : n < 809
            · by_cases h_mid : n < 808
              · have : n = 807 := by omega
                subst this
                decide
              · have : n = 808 := by omega
                subst this
                decide
            · have : n = 809 := by omega
              subst this
              decide
          · by_cases h_mid : n < 812
            · by_cases h_mid : n < 811
              · have : n = 810 := by omega
                subst this
                decide
              · have : n = 811 := by omega
                subst this
                decide
            · have : n = 812 := by omega
              subst this
              decide
      · by_cases h_mid : n < 819
        · by_cases h_mid : n < 816
          · by_cases h_mid : n < 815
            · by_cases h_mid : n < 814
              · have : n = 813 := by omega
                subst this
                decide
              · have : n = 814 := by omega
                subst this
                decide
            · have : n = 815 := by omega
              subst this
              decide
          · by_cases h_mid : n < 818
            · by_cases h_mid : n < 817
              · have : n = 816 := by omega
                subst this
                decide
              · have : n = 817 := by omega
                subst this
                decide
            · have : n = 818 := by omega
              subst this
              decide
        · by_cases h_mid : n < 822
          · by_cases h_mid : n < 821
            · by_cases h_mid : n < 820
              · have : n = 819 := by omega
                subst this
                decide
              · have : n = 820 := by omega
                subst this
                decide
            · have : n = 821 := by omega
              subst this
              decide
          · by_cases h_mid : n < 824
            · by_cases h_mid : n < 823
              · have : n = 822 := by omega
                subst this
                decide
              · have : n = 823 := by omega
                subst this
                decide
            · have : n = 824 := by omega
              subst this
              decide
    · by_cases h_mid : n < 838
      · by_cases h_mid : n < 832
        · by_cases h_mid : n < 829
          · by_cases h_mid : n < 827
            · by_cases h_mid : n < 826
              · have : n = 825 := by omega
                subst this
                decide
              · have : n = 826 := by omega
                subst this
                decide
            · by_cases h_mid : n < 828
              · have : n = 827 := by omega
                subst this
                decide
              · have : n = 828 := by omega
                subst this
                decide
          · by_cases h_mid : n < 831
            · by_cases h_mid : n < 830
              · have : n = 829 := by omega
                subst this
                decide
              · have : n = 830 := by omega
                subst this
                decide
            · have : n = 831 := by omega
              subst this
              decide
        · by_cases h_mid : n < 835
          · by_cases h_mid : n < 834
            · by_cases h_mid : n < 833
              · have : n = 832 := by omega
                subst this
                decide
              · have : n = 833 := by omega
                subst this
                decide
            · have : n = 834 := by omega
              subst this
              decide
          · by_cases h_mid : n < 837
            · by_cases h_mid : n < 836
              · have : n = 835 := by omega
                subst this
                decide
              · have : n = 836 := by omega
                subst this
                decide
            · have : n = 837 := by omega
              subst this
              decide
      · by_cases h_mid : n < 844
        · by_cases h_mid : n < 841
          · by_cases h_mid : n < 840
            · by_cases h_mid : n < 839
              · have : n = 838 := by omega
                subst this
                decide
              · have : n = 839 := by omega
                subst this
                decide
            · have : n = 840 := by omega
              subst this
              decide
          · by_cases h_mid : n < 843
            · by_cases h_mid : n < 842
              · have : n = 841 := by omega
                subst this
                decide
              · have : n = 842 := by omega
                subst this
                decide
            · have : n = 843 := by omega
              subst this
              decide
        · by_cases h_mid : n < 847
          · by_cases h_mid : n < 846
            · by_cases h_mid : n < 845
              · have : n = 844 := by omega
                subst this
                decide
              · have : n = 845 := by omega
                subst this
                decide
            · have : n = 846 := by omega
              subst this
              decide
          · by_cases h_mid : n < 849
            · by_cases h_mid : n < 848
              · have : n = 847 := by omega
                subst this
                decide
              · have : n = 848 := by omega
                subst this
                decide
            · have : n = 849 := by omega
              subst this
              decide
  · by_cases h_mid : n < 875
    · by_cases h_mid : n < 863
      · by_cases h_mid : n < 857
        · by_cases h_mid : n < 854
          · by_cases h_mid : n < 852
            · by_cases h_mid : n < 851
              · have : n = 850 := by omega
                subst this
                decide
              · have : n = 851 := by omega
                subst this
                decide
            · by_cases h_mid : n < 853
              · have : n = 852 := by omega
                subst this
                decide
              · have : n = 853 := by omega
                subst this
                decide
          · by_cases h_mid : n < 856
            · by_cases h_mid : n < 855
              · have : n = 854 := by omega
                subst this
                decide
              · have : n = 855 := by omega
                subst this
                decide
            · have : n = 856 := by omega
              subst this
              decide
        · by_cases h_mid : n < 860
          · by_cases h_mid : n < 859
            · by_cases h_mid : n < 858
              · have : n = 857 := by omega
                subst this
                decide
              · have : n = 858 := by omega
                subst this
                decide
            · have : n = 859 := by omega
              subst this
              decide
          · by_cases h_mid : n < 862
            · by_cases h_mid : n < 861
              · have : n = 860 := by omega
                subst this
                decide
              · have : n = 861 := by omega
                subst this
                decide
            · have : n = 862 := by omega
              subst this
              decide
      · by_cases h_mid : n < 869
        · by_cases h_mid : n < 866
          · by_cases h_mid : n < 865
            · by_cases h_mid : n < 864
              · have : n = 863 := by omega
                subst this
                decide
              · have : n = 864 := by omega
                subst this
                decide
            · have : n = 865 := by omega
              subst this
              decide
          · by_cases h_mid : n < 868
            · by_cases h_mid : n < 867
              · have : n = 866 := by omega
                subst this
                decide
              · have : n = 867 := by omega
                subst this
                decide
            · have : n = 868 := by omega
              subst this
              decide
        · by_cases h_mid : n < 872
          · by_cases h_mid : n < 871
            · by_cases h_mid : n < 870
              · have : n = 869 := by omega
                subst this
                decide
              · have : n = 870 := by omega
                subst this
                decide
            · have : n = 871 := by omega
              subst this
              decide
          · by_cases h_mid : n < 874
            · by_cases h_mid : n < 873
              · have : n = 872 := by omega
                subst this
                decide
              · have : n = 873 := by omega
                subst this
                decide
            · have : n = 874 := by omega
              subst this
              decide
    · by_cases h_mid : n < 888
      · by_cases h_mid : n < 882
        · by_cases h_mid : n < 879
          · by_cases h_mid : n < 877
            · by_cases h_mid : n < 876
              · have : n = 875 := by omega
                subst this
                decide
              · have : n = 876 := by omega
                subst this
                decide
            · by_cases h_mid : n < 878
              · have : n = 877 := by omega
                subst this
                decide
              · have : n = 878 := by omega
                subst this
                decide
          · by_cases h_mid : n < 881
            · by_cases h_mid : n < 880
              · have : n = 879 := by omega
                subst this
                decide
              · have : n = 880 := by omega
                subst this
                decide
            · have : n = 881 := by omega
              subst this
              decide
        · by_cases h_mid : n < 885
          · by_cases h_mid : n < 884
            · by_cases h_mid : n < 883
              · have : n = 882 := by omega
                subst this
                decide
              · have : n = 883 := by omega
                subst this
                decide
            · have : n = 884 := by omega
              subst this
              decide
          · by_cases h_mid : n < 887
            · by_cases h_mid : n < 886
              · have : n = 885 := by omega
                subst this
                decide
              · have : n = 886 := by omega
                subst this
                decide
            · have : n = 887 := by omega
              subst this
              decide
      · by_cases h_mid : n < 894
        · by_cases h_mid : n < 891
          · by_cases h_mid : n < 890
            · by_cases h_mid : n < 889
              · have : n = 888 := by omega
                subst this
                decide
              · have : n = 889 := by omega
                subst this
                decide
            · have : n = 890 := by omega
              subst this
              decide
          · by_cases h_mid : n < 893
            · by_cases h_mid : n < 892
              · have : n = 891 := by omega
                subst this
                decide
              · have : n = 892 := by omega
                subst this
                decide
            · have : n = 893 := by omega
              subst this
              decide
        · by_cases h_mid : n < 897
          · by_cases h_mid : n < 896
            · by_cases h_mid : n < 895
              · have : n = 894 := by omega
                subst this
                decide
              · have : n = 895 := by omega
                subst this
                decide
            · have : n = 896 := by omega
              subst this
              decide
          · by_cases h_mid : n < 899
            · by_cases h_mid : n < 898
              · have : n = 897 := by omega
                subst this
                decide
              · have : n = 898 := by omega
                subst this
                decide
            · have : n = 899 := by omega
              subst this
              decide

lemma witness_pos_and_mod_9 (n : ℕ) (h1 : 900 ≤ n) (h2 : n < 1000) : witness n > 0 ∧ (witness n - 1) % Nat.totient (witness n) = n := by
  by_cases h_mid : n < 950
  · by_cases h_mid : n < 925
    · by_cases h_mid : n < 913
      · by_cases h_mid : n < 907
        · by_cases h_mid : n < 904
          · by_cases h_mid : n < 902
            · by_cases h_mid : n < 901
              · have : n = 900 := by omega
                subst this
                decide
              · have : n = 901 := by omega
                subst this
                decide
            · by_cases h_mid : n < 903
              · have : n = 902 := by omega
                subst this
                decide
              · have : n = 903 := by omega
                subst this
                decide
          · by_cases h_mid : n < 906
            · by_cases h_mid : n < 905
              · have : n = 904 := by omega
                subst this
                decide
              · have : n = 905 := by omega
                subst this
                decide
            · have : n = 906 := by omega
              subst this
              decide
        · by_cases h_mid : n < 910
          · by_cases h_mid : n < 909
            · by_cases h_mid : n < 908
              · have : n = 907 := by omega
                subst this
                decide
              · have : n = 908 := by omega
                subst this
                decide
            · have : n = 909 := by omega
              subst this
              decide
          · by_cases h_mid : n < 912
            · by_cases h_mid : n < 911
              · have : n = 910 := by omega
                subst this
                decide
              · have : n = 911 := by omega
                subst this
                decide
            · have : n = 912 := by omega
              subst this
              decide
      · by_cases h_mid : n < 919
        · by_cases h_mid : n < 916
          · by_cases h_mid : n < 915
            · by_cases h_mid : n < 914
              · have : n = 913 := by omega
                subst this
                decide
              · have : n = 914 := by omega
                subst this
                decide
            · have : n = 915 := by omega
              subst this
              decide
          · by_cases h_mid : n < 918
            · by_cases h_mid : n < 917
              · have : n = 916 := by omega
                subst this
                decide
              · have : n = 917 := by omega
                subst this
                decide
            · have : n = 918 := by omega
              subst this
              decide
        · by_cases h_mid : n < 922
          · by_cases h_mid : n < 921
            · by_cases h_mid : n < 920
              · have : n = 919 := by omega
                subst this
                decide
              · have : n = 920 := by omega
                subst this
                decide
            · have : n = 921 := by omega
              subst this
              decide
          · by_cases h_mid : n < 924
            · by_cases h_mid : n < 923
              · have : n = 922 := by omega
                subst this
                decide
              · have : n = 923 := by omega
                subst this
                decide
            · have : n = 924 := by omega
              subst this
              decide
    · by_cases h_mid : n < 938
      · by_cases h_mid : n < 932
        · by_cases h_mid : n < 929
          · by_cases h_mid : n < 927
            · by_cases h_mid : n < 926
              · have : n = 925 := by omega
                subst this
                decide
              · have : n = 926 := by omega
                subst this
                decide
            · by_cases h_mid : n < 928
              · have : n = 927 := by omega
                subst this
                decide
              · have : n = 928 := by omega
                subst this
                decide
          · by_cases h_mid : n < 931
            · by_cases h_mid : n < 930
              · have : n = 929 := by omega
                subst this
                decide
              · have : n = 930 := by omega
                subst this
                decide
            · have : n = 931 := by omega
              subst this
              decide
        · by_cases h_mid : n < 935
          · by_cases h_mid : n < 934
            · by_cases h_mid : n < 933
              · have : n = 932 := by omega
                subst this
                decide
              · have : n = 933 := by omega
                subst this
                decide
            · have : n = 934 := by omega
              subst this
              decide
          · by_cases h_mid : n < 937
            · by_cases h_mid : n < 936
              · have : n = 935 := by omega
                subst this
                decide
              · have : n = 936 := by omega
                subst this
                decide
            · have : n = 937 := by omega
              subst this
              decide
      · by_cases h_mid : n < 944
        · by_cases h_mid : n < 941
          · by_cases h_mid : n < 940
            · by_cases h_mid : n < 939
              · have : n = 938 := by omega
                subst this
                decide
              · have : n = 939 := by omega
                subst this
                decide
            · have : n = 940 := by omega
              subst this
              decide
          · by_cases h_mid : n < 943
            · by_cases h_mid : n < 942
              · have : n = 941 := by omega
                subst this
                decide
              · have : n = 942 := by omega
                subst this
                decide
            · have : n = 943 := by omega
              subst this
              decide
        · by_cases h_mid : n < 947
          · by_cases h_mid : n < 946
            · by_cases h_mid : n < 945
              · have : n = 944 := by omega
                subst this
                decide
              · have : n = 945 := by omega
                subst this
                decide
            · have : n = 946 := by omega
              subst this
              decide
          · by_cases h_mid : n < 949
            · by_cases h_mid : n < 948
              · have : n = 947 := by omega
                subst this
                decide
              · have : n = 948 := by omega
                subst this
                decide
            · have : n = 949 := by omega
              subst this
              decide
  · by_cases h_mid : n < 975
    · by_cases h_mid : n < 963
      · by_cases h_mid : n < 957
        · by_cases h_mid : n < 954
          · by_cases h_mid : n < 952
            · by_cases h_mid : n < 951
              · have : n = 950 := by omega
                subst this
                decide
              · have : n = 951 := by omega
                subst this
                decide
            · by_cases h_mid : n < 953
              · have : n = 952 := by omega
                subst this
                decide
              · have : n = 953 := by omega
                subst this
                decide
          · by_cases h_mid : n < 956
            · by_cases h_mid : n < 955
              · have : n = 954 := by omega
                subst this
                decide
              · have : n = 955 := by omega
                subst this
                decide
            · have : n = 956 := by omega
              subst this
              decide
        · by_cases h_mid : n < 960
          · by_cases h_mid : n < 959
            · by_cases h_mid : n < 958
              · have : n = 957 := by omega
                subst this
                decide
              · have : n = 958 := by omega
                subst this
                decide
            · have : n = 959 := by omega
              subst this
              decide
          · by_cases h_mid : n < 962
            · by_cases h_mid : n < 961
              · have : n = 960 := by omega
                subst this
                decide
              · have : n = 961 := by omega
                subst this
                decide
            · have : n = 962 := by omega
              subst this
              decide
      · by_cases h_mid : n < 969
        · by_cases h_mid : n < 966
          · by_cases h_mid : n < 965
            · by_cases h_mid : n < 964
              · have : n = 963 := by omega
                subst this
                decide
              · have : n = 964 := by omega
                subst this
                decide
            · have : n = 965 := by omega
              subst this
              decide
          · by_cases h_mid : n < 968
            · by_cases h_mid : n < 967
              · have : n = 966 := by omega
                subst this
                decide
              · have : n = 967 := by omega
                subst this
                decide
            · have : n = 968 := by omega
              subst this
              decide
        · by_cases h_mid : n < 972
          · by_cases h_mid : n < 971
            · by_cases h_mid : n < 970
              · have : n = 969 := by omega
                subst this
                decide
              · have : n = 970 := by omega
                subst this
                decide
            · have : n = 971 := by omega
              subst this
              decide
          · by_cases h_mid : n < 974
            · by_cases h_mid : n < 973
              · have : n = 972 := by omega
                subst this
                decide
              · have : n = 973 := by omega
                subst this
                decide
            · have : n = 974 := by omega
              subst this
              decide
    · by_cases h_mid : n < 988
      · by_cases h_mid : n < 982
        · by_cases h_mid : n < 979
          · by_cases h_mid : n < 977
            · by_cases h_mid : n < 976
              · have : n = 975 := by omega
                subst this
                decide
              · have : n = 976 := by omega
                subst this
                decide
            · by_cases h_mid : n < 978
              · have : n = 977 := by omega
                subst this
                decide
              · have : n = 978 := by omega
                subst this
                decide
          · by_cases h_mid : n < 981
            · by_cases h_mid : n < 980
              · have : n = 979 := by omega
                subst this
                decide
              · have : n = 980 := by omega
                subst this
                decide
            · have : n = 981 := by omega
              subst this
              decide
        · by_cases h_mid : n < 985
          · by_cases h_mid : n < 984
            · by_cases h_mid : n < 983
              · have : n = 982 := by omega
                subst this
                decide
              · have : n = 983 := by omega
                subst this
                decide
            · have : n = 984 := by omega
              subst this
              decide
          · by_cases h_mid : n < 987
            · by_cases h_mid : n < 986
              · have : n = 985 := by omega
                subst this
                decide
              · have : n = 986 := by omega
                subst this
                decide
            · have : n = 987 := by omega
              subst this
              decide
      · by_cases h_mid : n < 994
        · by_cases h_mid : n < 991
          · by_cases h_mid : n < 990
            · by_cases h_mid : n < 989
              · have : n = 988 := by omega
                subst this
                decide
              · have : n = 989 := by omega
                subst this
                decide
            · have : n = 990 := by omega
              subst this
              decide
          · by_cases h_mid : n < 993
            · by_cases h_mid : n < 992
              · have : n = 991 := by omega
                subst this
                decide
              · have : n = 992 := by omega
                subst this
                decide
            · have : n = 993 := by omega
              subst this
              decide
        · by_cases h_mid : n < 997
          · by_cases h_mid : n < 996
            · by_cases h_mid : n < 995
              · have : n = 994 := by omega
                subst this
                decide
              · have : n = 995 := by omega
                subst this
                decide
            · have : n = 996 := by omega
              subst this
              decide
          · by_cases h_mid : n < 999
            · by_cases h_mid : n < 998
              · have : n = 997 := by omega
                subst this
                decide
              · have : n = 998 := by omega
                subst this
                decide
            · have : n = 999 := by omega
              subst this
              decide

lemma witness_pos_and_mod (n : ℕ) (hn : n < 1000) : witness n > 0 ∧ (witness n - 1) % Nat.totient (witness n) = n := by
  by_cases h_mid : n < 500
  · by_cases h_mid : n < 300
    · by_cases h_mid : n < 200
      · by_cases h_mid : n < 100
        · exact witness_pos_and_mod_0 n hn
        · have h_low : 100 ≤ n := by omega
          have h_high : n < 200 := by omega
          exact witness_pos_and_mod_1 n h_low h_high
      · have h_low : 200 ≤ n := by omega
        have h_high : n < 300 := by omega
        exact witness_pos_and_mod_2 n h_low h_high
    · by_cases h_mid : n < 400
      · have h_low : 300 ≤ n := by omega
        have h_high : n < 400 := by omega
        exact witness_pos_and_mod_3 n h_low h_high
      · have h_low : 400 ≤ n := by omega
        have h_high : n < 500 := by omega
        exact witness_pos_and_mod_4 n h_low h_high
  · by_cases h_mid : n < 800
    · by_cases h_mid : n < 700
      · by_cases h_mid : n < 600
        · have h_low : 500 ≤ n := by omega
          have h_high : n < 600 := by omega
          exact witness_pos_and_mod_5 n h_low h_high
        · have h_low : 600 ≤ n := by omega
          have h_high : n < 700 := by omega
          exact witness_pos_and_mod_6 n h_low h_high
      · have h_low : 700 ≤ n := by omega
        have h_high : n < 800 := by omega
        exact witness_pos_and_mod_7 n h_low h_high
    · by_cases h_mid : n < 900
      · have h_low : 800 ≤ n := by omega
        have h_high : n < 900 := by omega
        exact witness_pos_and_mod_8 n h_low h_high
      · have h_low : 900 ≤ n := by omega
        exact witness_pos_and_mod_9 n h_low hn
