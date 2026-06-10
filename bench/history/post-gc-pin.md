# Bench run: post-gc-pin

- **Timestamp**: 2026-06-10T11:25:24Z
- **Nix**: 2.31.4
- **System**: x86_64-linux
- **Runs per workload**: 5

| Workload                                            |     values |     thunks |   cpu ms |  wall ms |
|-----------------------------------------------------|-----------:|-----------:|---------:|---------:|
| effects.buildSim.diamond5                           |     670765 |     228522 |      413 |      345 |
| effects.buildSim.fail_early                         |     667835 |     225689 |      405 |      393 |
| effects.buildSim.fail_late                          |     667835 |     225689 |      411 |      410 |
| effects.buildSim.fail_mid                           |     667835 |     225689 |      413 |      405 |
| effects.buildSim.linear100                          |     687614 |     244670 |      429 |      377 |
| effects.buildSim.linear50                           |     677714 |     235170 |      401 |      385 |
| effects.buildSim.mixed_small                        |     696493 |     253079 |      409 |      389 |
| effects.buildSim.tree5                              |     679541 |     236988 |      443 |      409 |
| effects.buildSim.wide100                            |     685529 |     242480 |      396 |      401 |
| effects.buildSim.wide50                             |     676779 |     234180 |      419 |      391 |
| effects.interp.countdown1000                        |     936178 |     484025 |      515 |      488 |
| effects.interp.fib10                                |     725941 |     281763 |      447 |      408 |
| effects.interp.fib15                                |    1315029 |     850197 |      642 |      566 |
| effects.interp.lets100                              |     684345 |     241702 |      408 |      333 |
| effects.interp.lets500                              |     750345 |     305702 |      586 |      531 |
| effects.interp.sum100                               |     703983 |     260530 |      431 |      384 |
| effects.interp.sum1000                              |    1026183 |     571030 |      507 |      501 |
| effects.stateChain.s10k                             |    1358126 |     865918 |      624 |      585 |
| effects.stateChain.s1k                              |     737126 |     289918 |      456 |      429 |
| effects.stress.bindHeavy.s10k                       |     956344 |     474200 |      466 |      445 |
| effects.stress.deepChains.s10k                      |     737722 |     255600 |      418 |      393 |
| effects.stress.effectHeavy.s10k                     |     927829 |     475684 |      543 |      498 |
| effects.stress.mixed.s10k                           |    1207830 |     735685 |      617 |      577 |
| effects.stress.nestedHandlers.d3_i1k                |     724882 |     277730 |      491 |      447 |
| effects.stress.rawGC.s10k                           |      50174 |      50050 |       43 |       59 |
| experimental.descInterp.stateChain.s1k              |   23883615 |   21632689 |     8030 |     6243 |
| experimental.descInterp.stateChain.s1kShort         |    2382554 |    1845140 |      988 |      818 |
| tc.bindP.desc-con-trampoline-blame-5000             |    2514875 |    1987250 |      999 |      854 |
| tc.bindP.slow-path-chain-5000                       |    1068661 |     601321 |      489 |      504 |
| tc.bindP.universal-blame-chain                      |    1068661 |     601321 |      475 |      446 |
| tc.check.list-chain-5000                            |    1934629 |    1413474 |      878 |      783 |
| tc.check.macro-field                                |     824880 |     367465 |      507 |      487 |
| tc.check.nat-chain-5000                             |    1612824 |    1122366 |      677 |      621 |
| tc.checkD.mixed-chain-5000                          |    1249769 |     779712 |      623 |      575 |
| tc.conv.alpha-equivalent                            |     749003 |     298632 |      493 |      465 |
| tc.conv.beta-distinct                               |     757723 |     302940 |      498 |      482 |
| tc.conv.identical-deep                              |    1612827 |    1122369 |      701 |      659 |
| tc.conv.identical-shallow                           |     681582 |     236174 |      449 |      421 |
| tc.conv.mu-heavy                                    |     717385 |     268092 |      520 |      504 |
| tc.conv.plus-heavy                                  |     700253 |     253884 |      483 |      464 |
| tc.decidable.leDiag50                               |   40956571 |   35163803 |     9182 |     8049 |
| tc.diag.error-chain-backmap-5000                    |     762581 |     300788 |      431 |      409 |
| tc.diag.hint-resolve-5000                           |     796847 |     339053 |      644 |      486 |
| tc.diag.pretty-multi-line-5000                      |     810744 |     338392 |      631 |      535 |
| tc.diag.pretty-one-line-5000                        |     771691 |     309343 |      581 |      468 |
| tc.e2e.datatype-macro-big                           |     824887 |     367472 |      528 |      489 |
| tc.e2e.datatypeI-fin-deep                           |     874344 |     415559 |      497 |      486 |
| tc.e2e.let-chain-100                                |    1194576 |     720569 |      524 |      527 |
| tc.e2e.tc-test-suite-full                           |  332306666 |  303782279 |    96189 |    77570 |
| tc.e2e.tc-test-suite-per-module.check               |   18355341 |   16176524 |     5711 |     4415 |
| tc.e2e.tc-test-suite-per-module.conv                |   76779318 |   68672898 |    25228 |    19327 |
| tc.e2e.tc-test-suite-per-module.elaborate           |    9482240 |    8229625 |     3148 |     2498 |
| tc.e2e.tc-test-suite-per-module.eval                |   22756843 |   19991413 |     6048 |     4755 |
| tc.e2e.tc-test-suite-per-module.hoas                |  174288967 |  160843160 |    64984 |    50583 |
| tc.e2e.tc-test-suite-per-module.quote               |    2969181 |    2191982 |     1032 |      997 |
| tc.e2e.tc-test-suite-per-module.term                |     763996 |     285552 |      513 |      510 |
| tc.e2e.tc-test-suite-per-module.value               |     989288 |     390126 |      587 |      591 |
| tc.e2e.tc-test-suite-per-module.verified            |   11821610 |   10386052 |     3915 |     3180 |
| tc.elaborate.flatten                                |     684889 |     233328 |      434 |      413 |
| tc.elaborate.recursive                              |     946629 |     485474 |      548 |      571 |
| tc.eval-depth-scaling.conv.n10                      |     684718 |     239165 |      482 |      502 |
| tc.eval-depth-scaling.conv.n100                     |     701458 |     255095 |      487 |      467 |
| tc.eval-depth-scaling.conv.n1000                    |     868858 |     414395 |      520 |      514 |
| tc.eval-depth-scaling.desc-ind.n10                  |    1908056 |    1289033 |      765 |      751 |
| tc.eval-depth-scaling.desc-ind.n100                 |    2713940 |    1952811 |     1003 |      932 |
| tc.eval-depth-scaling.desc-ind.n1000                |   10080330 |    8590330 |     2972 |     2288 |
| tc.eval-depth-scaling.vAppF.n10                     |     675761 |     231149 |      407 |      383 |
| tc.eval-depth-scaling.vAppF.n100                    |     684401 |     239519 |      473 |      422 |
| tc.eval-depth-scaling.vAppF.n1000                   |     851251 |     376544 |      507 |      484 |
| tc.generic.derive-deps                              |     736375 |     287839 |      473 |      461 |
| tc.generic.derive-descriptor                        |     671550 |     227875 |      441 |      423 |
| tc.generic.derive-schema                            |     671546 |     227871 |      467 |      467 |
| tc.generic.functional-builder-chain                 |    3116975 |    2523516 |     1216 |     1031 |
| tc.generic.metadata-normalize                       |     671388 |     227869 |      428 |      442 |
| tc.generic.synthetic-builder-chain                  |    2381377 |    1820918 |      936 |      865 |
| tc.generic.view-review                              |     742491 |     293528 |      533 |      528 |
| tc.infer.deep-app-100                               |    1263104 |     784282 |      670 |      670 |
| tc.meta.postpone-and-wake-100                       |     708217 |     251849 |      422 |      416 |
| tc.meta.solve-chain-100                             |     690279 |     245329 |      388 |      367 |
| tc.ornaments.alg-list-to-vec-check                  |    3824556 |    3184153 |     1568 |     1304 |
| tc.ornaments.functional-diagnostics-missing-builder |     671679 |     227953 |      472 |      474 |
| tc.ornaments.functional-liftProducer-check          |     724705 |     275938 |      493 |      472 |
| tc.ornaments.functional-synthesis-build             |    1087949 |     611646 |      582 |      555 |
| tc.ornaments.ornCompose-check                       |    1592492 |    1095102 |      783 |      744 |
| tc.ornaments.ornDesc-normalize                      |     670732 |     227173 |      451 |      431 |
| tc.ornaments.ornForget-check                        |    1078766 |     603208 |      588 |      591 |
| tc.ornaments.ornForget-elaborate                    |     671089 |     227514 |      407 |      403 |
| tc.quote.closed                                     |     714560 |     267490 |      498 |      490 |
| tc.quote.open                                       |     678442 |     233391 |      479 |      459 |
| tc.quote.stuck                                      |     691753 |     246735 |      456 |      443 |
| tc.surface.toy-elaborate-100                        |   29578526 |   26294897 |    10337 |     7398 |

