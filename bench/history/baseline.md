# Bench run: release-0.14.0

- **Timestamp**: 2026-06-23T10:25:14Z
- **Nix**: 2.31.4
- **System**: x86_64-linux
- **Runs per workload**: 5

| Workload                                            |     values |     thunks |   cpu ms |  wall ms |
|-----------------------------------------------------|-----------:|-----------:|---------:|---------:|
| effects.buildSim.diamond5                           |     670684 |     228390 |      425 |      414 |
| effects.buildSim.fail_early                         |     667896 |     225699 |      388 |      354 |
| effects.buildSim.fail_late                          |     667896 |     225699 |      431 |      408 |
| effects.buildSim.fail_mid                           |     667896 |     225699 |      408 |      368 |
| effects.buildSim.linear100                          |     687650 |     244655 |      437 |      417 |
| effects.buildSim.linear50                           |     677750 |     235155 |      413 |      371 |
| effects.buildSim.mixed_small                        |     695827 |     252362 |      456 |      423 |
| effects.buildSim.tree5                              |     679174 |     236570 |      421 |      425 |
| effects.buildSim.wide100                            |     684278 |     241178 |      437 |      423 |
| effects.buildSim.wide50                             |     676178 |     233528 |      437 |      427 |
| effects.interp.countdown1000                        |     910223 |     458019 |      518 |      508 |
| effects.interp.fib10                                |     720615 |     276386 |      449 |      430 |
| effects.interp.fib15                                |    1254925 |     790042 |      595 |      578 |
| effects.interp.lets100                              |     682816 |     240122 |      435 |      413 |
| effects.interp.lets500                              |     742416 |     297722 |      534 |      508 |
| effects.interp.sum100                               |     701128 |     257624 |      380 |      353 |
| effects.interp.sum1000                              |     997228 |     542024 |      538 |      531 |
| effects.stateChain.s10k                             |    1358181 |     865922 |      690 |      561 |
| effects.stateChain.s1k                              |     737181 |     289922 |      450 |      379 |
| effects.stress.bindHeavy.s10k                       |     956405 |     474210 |      499 |      398 |
| effects.stress.deepChains.s10k                      |     737783 |     255610 |      490 |      425 |
| effects.stress.effectHeavy.s10k                     |     897887 |     445691 |      540 |      452 |
| effects.stress.mixed.s10k                           |    1147888 |     675692 |      595 |      461 |
| effects.stress.nestedHandlers.d3_i1k                |     724940 |     277737 |      457 |      419 |
| effects.stress.rawGC.s10k                           |      50175 |      50051 |       45 |       65 |
| experimental.descInterp.stateChain.s1k              |    3793780 |    3183856 |     1470 |     1241 |
| experimental.descInterp.stateChain.s1kShort         |    1310470 |     840989 |      702 |      640 |
| tc.bindP.desc-con-trampoline-blame-5000             |    1314103 |     818305 |      628 |      653 |
| tc.bindP.slow-path-chain-5000                       |     908805 |     441410 |      483 |      425 |
| tc.bindP.universal-blame-chain                      |     908805 |     441410 |      520 |      470 |
| tc.check.list-chain-5000                            |    1312400 |     801671 |      651 |      617 |
| tc.check.macro-field                                |     724733 |     278724 |      479 |      448 |
| tc.check.nat-chain-5000                             |    1204246 |     713766 |      589 |      565 |
| tc.checkD.mixed-chain-5000                          |    1155608 |     688033 |      594 |      532 |
| tc.conv.alpha-equivalent                            |     701498 |     254997 |      479 |      436 |
| tc.conv.beta-distinct                               |     679474 |     234029 |      466 |      440 |
| tc.conv.identical-deep                              |    1204249 |     713769 |      623 |      547 |
| tc.conv.identical-shallow                           |     677595 |     232152 |      480 |      473 |
| tc.conv.mu-heavy                                    |     678844 |     232793 |      470 |      422 |
| tc.conv.plus-heavy                                  |     685427 |     239963 |      501 |      464 |
| tc.decidable.leDiag50                               |   14258310 |   12958918 |     4438 |     3537 |
| tc.diag.error-chain-backmap-5000                    |     762660 |     300812 |      444 |      428 |
| tc.diag.hint-resolve-5000                           |     796909 |     339064 |      684 |      510 |
| tc.diag.pretty-multi-line-5000                      |     811164 |     338723 |      689 |      523 |
| tc.diag.pretty-one-line-5000                        |     771757 |     309358 |      656 |      521 |
| tc.e2e.datatype-macro-big                           |     724740 |     278731 |      498 |      466 |
| tc.e2e.datatypeI-fin-deep                           |     759010 |     308977 |      520 |      483 |
| tc.e2e.let-chain-100                                |     860305 |     414563 |      545 |      538 |
| tc.e2e.tc-test-suite-full                           |  305851908 |  292270467 |    99905 |    76240 |
| tc.e2e.tc-test-suite-per-module.check               |   15560121 |   14220878 |     5088 |     3766 |
| tc.e2e.tc-test-suite-per-module.conv                |   25413999 |   23795575 |     8213 |     6088 |
| tc.e2e.tc-test-suite-per-module.elaborate           |    6794064 |    5569652 |     2192 |     1822 |
| tc.e2e.tc-test-suite-per-module.eval                |   31982047 |   28318930 |     6969 |     5466 |
| tc.e2e.tc-test-suite-per-module.hoas                |   78959423 |   75713797 |    31925 |    25353 |
| tc.e2e.tc-test-suite-per-module.quote               |    1667864 |    1110510 |      904 |      793 |
| tc.e2e.tc-test-suite-per-module.term                |     777161 |     293319 |      570 |      560 |
| tc.e2e.tc-test-suite-per-module.value               |    1162528 |     477966 |      640 |      538 |
| tc.e2e.tc-test-suite-per-module.verified            |    4759600 |    4165095 |     1929 |     1658 |
| tc.elaborate.flatten                                |     687483 |     234873 |      378 |      366 |
| tc.elaborate.recursive                              |     812400 |     353671 |      527 |      525 |
| tc.eval-depth-scaling.conv.n10                      |     680330 |     234755 |      481 |      439 |
| tc.eval-depth-scaling.conv.n100                     |     689780 |     243395 |      498 |      462 |
| tc.eval-depth-scaling.conv.n1000                    |     784280 |     329795 |      528 |      478 |
| tc.eval-depth-scaling.desc-ind.n10                  |    1117330 |     644136 |      662 |      529 |
| tc.eval-depth-scaling.desc-ind.n100                 |    1491299 |     957586 |      831 |      692 |
| tc.eval-depth-scaling.desc-ind.n1000                |    5600683 |    4657789 |     1882 |     1499 |
| tc.eval-depth-scaling.vAppF.n10                     |     676240 |     230817 |      482 |      437 |
| tc.eval-depth-scaling.vAppF.n100                    |     685240 |     239547 |      465 |      445 |
| tc.eval-depth-scaling.vAppF.n1000                   |     795837 |     335237 |      503 |      471 |
| tc.generic.derive-deps                              |     685751 |     239763 |      462 |      479 |
| tc.generic.derive-descriptor                        |     671661 |     227917 |      445 |      414 |
| tc.generic.derive-schema                            |     671657 |     227913 |      483 |      424 |
| tc.generic.functional-builder-chain                 |     796930 |     347040 |      511 |      471 |
| tc.generic.metadata-normalize                       |     671499 |     227911 |      483 |      459 |
| tc.generic.synthetic-builder-chain                  |     725786 |     278125 |      435 |      444 |
| tc.generic.view-review                              |     689321 |     243393 |      451 |      444 |
| tc.infer.deep-app-100                               |     889475 |     443045 |      545 |      516 |
| tc.meta.postpone-and-wake-100                       |     734613 |     275254 |      496 |      428 |
| tc.meta.solve-chain-100                             |     704831 |     258206 |      469 |      442 |
| tc.ornaments.alg-list-to-vec-check                  |    2089079 |    1588792 |      903 |      844 |
| tc.ornaments.functional-diagnostics-missing-builder |     671790 |     227995 |      459 |      440 |
| tc.ornaments.functional-liftProducer-check          |     690786 |     244457 |      508 |      508 |
| tc.ornaments.functional-synthesis-build             |     835926 |     383790 |      524 |      508 |
| tc.ornaments.ornCompose-check                       |    1134015 |     669768 |      620 |      624 |
| tc.ornaments.ornDesc-normalize                      |     670850 |     227218 |      474 |      426 |
| tc.ornaments.ornForget-check                        |     830065 |     378435 |      477 |      463 |
| tc.ornaments.ornForget-elaborate                    |     671207 |     227559 |      415 |      351 |
| tc.quote.closed                                     |     694523 |     247668 |      457 |      404 |
| tc.quote.open                                       |     677344 |     231717 |      477 |      426 |
| tc.quote.stuck                                      |     686561 |     241079 |      548 |      514 |
| tc.surface.toy-elaborate-100                        |   14736244 |   14051771 |     5311 |     4183 |

