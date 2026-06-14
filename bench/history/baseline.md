# Bench run: release-0.13.0

- **Timestamp**: 2026-06-14T09:12:59Z
- **Nix**: 2.31.4
- **System**: x86_64-linux
- **Runs per workload**: 5

| Workload                                            |     values |     thunks |   cpu ms |  wall ms |
|-----------------------------------------------------|-----------:|-----------:|---------:|---------:|
| effects.buildSim.diamond5                           |     670623 |     228380 |      398 |      362 |
| effects.buildSim.fail_early                         |     667835 |     225689 |      400 |      384 |
| effects.buildSim.fail_late                          |     667835 |     225689 |      405 |      359 |
| effects.buildSim.fail_mid                           |     667835 |     225689 |      336 |      331 |
| effects.buildSim.linear100                          |     687589 |     244645 |      305 |      276 |
| effects.buildSim.linear50                           |     677689 |     235145 |      378 |      353 |
| effects.buildSim.mixed_small                        |     695766 |     252352 |      409 |      398 |
| effects.buildSim.tree5                              |     679113 |     236560 |      442 |      396 |
| effects.buildSim.wide100                            |     684217 |     241168 |      392 |      391 |
| effects.buildSim.wide50                             |     676117 |     233518 |      418 |      430 |
| effects.interp.countdown1000                        |     910162 |     458009 |      501 |      522 |
| effects.interp.fib10                                |     720554 |     276376 |      423 |      399 |
| effects.interp.fib15                                |    1254864 |     790032 |      567 |      575 |
| effects.interp.lets100                              |     682755 |     240112 |      393 |      393 |
| effects.interp.lets500                              |     742355 |     297712 |      568 |      563 |
| effects.interp.sum100                               |     701067 |     257614 |      431 |      401 |
| effects.interp.sum1000                              |     997167 |     542014 |      501 |      505 |
| effects.stateChain.s10k                             |    1358120 |     865912 |      613 |      591 |
| effects.stateChain.s1k                              |     737120 |     289912 |      438 |      422 |
| effects.stress.bindHeavy.s10k                       |     956344 |     474200 |      456 |      447 |
| effects.stress.deepChains.s10k                      |     737722 |     255600 |      433 |      437 |
| effects.stress.effectHeavy.s10k                     |     897826 |     445681 |      464 |      430 |
| effects.stress.mixed.s10k                           |    1147827 |     675682 |      459 |      442 |
| effects.stress.nestedHandlers.d3_i1k                |     724879 |     277727 |      387 |      379 |
| effects.stress.rawGC.s10k                           |      50174 |      50050 |       28 |       41 |
| experimental.descInterp.stateChain.s1k              |    3846250 |    3236414 |     1219 |     1128 |
| experimental.descInterp.stateChain.s1kShort         |    1309075 |     839691 |      607 |      624 |
| tc.bindP.desc-con-trampoline-blame-5000             |    1303812 |     808103 |      577 |      572 |
| tc.bindP.slow-path-chain-5000                       |     908736 |     441396 |      460 |      475 |
| tc.bindP.universal-blame-chain                      |     908736 |     441396 |      426 |      419 |
| tc.check.list-chain-5000                            |    1302111 |     791471 |      615 |      598 |
| tc.check.macro-field                                |     724391 |     278471 |      450 |      451 |
| tc.check.nat-chain-5000                             |    1199054 |     708663 |      561 |      561 |
| tc.checkD.mixed-chain-5000                          |    1155486 |     687992 |      569 |      586 |
| tc.conv.alpha-equivalent                            |     704886 |     258357 |      498 |      460 |
| tc.conv.beta-distinct                               |     679279 |     233923 |      512 |      478 |
| tc.conv.identical-deep                              |    1199057 |     708666 |      620 |      578 |
| tc.conv.identical-shallow                           |     677417 |     232063 |      453 |      467 |
| tc.conv.mu-heavy                                    |     678666 |     232704 |      509 |      472 |
| tc.conv.plus-heavy                                  |     685229 |     239854 |      456 |      441 |
| tc.decidable.leDiag50                               |   14269022 |   12969939 |     3529 |     3411 |
| tc.diag.error-chain-backmap-5000                    |     762591 |     300798 |      449 |      425 |
| tc.diag.hint-resolve-5000                           |     796847 |     339053 |      634 |      491 |
| tc.diag.pretty-multi-line-5000                      |     810744 |     338392 |      672 |      531 |
| tc.diag.pretty-one-line-5000                        |     771691 |     309343 |      672 |      565 |
| tc.e2e.datatype-macro-big                           |     724398 |     278478 |      500 |      473 |
| tc.e2e.datatypeI-fin-deep                           |     763820 |     313514 |      500 |      487 |
| tc.e2e.let-chain-100                                |     859527 |     413874 |      571 |      565 |
| tc.e2e.tc-test-suite-full                           |  162114833 |  153159786 |    57157 |    46449 |
| tc.e2e.tc-test-suite-per-module.check               |   15347837 |   14042265 |     5527 |     3995 |
| tc.e2e.tc-test-suite-per-module.conv                |   30610967 |   28863019 |    10901 |     8282 |
| tc.e2e.tc-test-suite-per-module.elaborate           |    5781966 |    4736782 |     1996 |     1677 |
| tc.e2e.tc-test-suite-per-module.eval                |   23977518 |   20978242 |     6369 |     4848 |
| tc.e2e.tc-test-suite-per-module.hoas                |   78909069 |   75608253 |    35101 |    28764 |
| tc.e2e.tc-test-suite-per-module.quote               |    1655493 |    1102351 |      804 |      808 |
| tc.e2e.tc-test-suite-per-module.term                |     765088 |     285456 |      511 |      516 |
| tc.e2e.tc-test-suite-per-module.value               |     990380 |     390030 |      546 |      551 |
| tc.e2e.tc-test-suite-per-module.verified            |    5155285 |    4550982 |     1946 |     1740 |
| tc.elaborate.flatten                                |     684895 |     233334 |      509 |      464 |
| tc.elaborate.recursive                              |     810111 |     351471 |      530 |      518 |
| tc.eval-depth-scaling.conv.n10                      |     680128 |     234642 |      418 |      407 |
| tc.eval-depth-scaling.conv.n100                     |     689488 |     243192 |      513 |      483 |
| tc.eval-depth-scaling.conv.n1000                    |     783088 |     328692 |      476 |      455 |
| tc.eval-depth-scaling.desc-ind.n10                  |    1116932 |     643847 |      593 |      568 |
| tc.eval-depth-scaling.desc-ind.n100                 |    1492076 |     958472 |      570 |      542 |
| tc.eval-depth-scaling.desc-ind.n1000                |    5615065 |    4672280 |     1570 |     1322 |
| tc.eval-depth-scaling.vAppF.n10                     |     676034 |     230706 |      410 |      409 |
| tc.eval-depth-scaling.vAppF.n100                    |     684674 |     239076 |      434 |      429 |
| tc.eval-depth-scaling.vAppF.n1000                   |     791671 |     331166 |      507 |      500 |
| tc.generic.derive-deps                              |     685388 |     239493 |      503 |      507 |
| tc.generic.derive-descriptor                        |     671556 |     227881 |      388 |      385 |
| tc.generic.derive-schema                            |     671552 |     227877 |      498 |      483 |
| tc.generic.functional-builder-chain                 |     796196 |     346395 |      446 |      470 |
| tc.generic.metadata-normalize                       |     671394 |     227875 |      442 |      413 |
| tc.generic.synthetic-builder-chain                  |     725368 |     277796 |      409 |      399 |
| tc.generic.view-review                              |     688942 |     243109 |      447 |      431 |
| tc.infer.deep-app-100                               |     883449 |     437108 |      458 |      475 |
| tc.meta.postpone-and-wake-100                       |     708261 |     251891 |      436 |      402 |
| tc.meta.solve-chain-100                             |     690323 |     245371 |      449 |      448 |
| tc.ornaments.alg-list-to-vec-check                  |    2136496 |    1634701 |      883 |      853 |
| tc.ornaments.functional-diagnostics-missing-builder |     671685 |     227959 |      471 |      442 |
| tc.ornaments.functional-liftProducer-check          |     690504 |     244264 |      497 |      457 |
| tc.ornaments.functional-synthesis-build             |     837144 |     385049 |      524 |      495 |
| tc.ornaments.ornCompose-check                       |    1137090 |     672797 |      572 |      583 |
| tc.ornaments.ornDesc-normalize                      |     670738 |     227179 |      438 |      404 |
| tc.ornaments.ornForget-check                        |     831304 |     379715 |      417 |      415 |
| tc.ornaments.ornForget-elaborate                    |     671095 |     227520 |      444 |      377 |
| tc.quote.closed                                     |     700805 |     253740 |      475 |      420 |
| tc.quote.open                                       |     677177 |     231639 |      470 |      443 |
| tc.quote.stuck                                      |     686265 |     240872 |      428 |      407 |
| tc.surface.toy-elaborate-100                        |   14696886 |   14007910 |     5640 |     4044 |

