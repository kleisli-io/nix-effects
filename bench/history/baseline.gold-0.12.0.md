# Bench run: baseline

- **Timestamp**: 2026-05-20T18:39:54Z
- **Nix**: 2.31.4
- **System**: x86_64-linux
- **Runs per workload**: 5

| Workload                                            |     values |     thunks |   cpu ms |  wall ms |
|-----------------------------------------------------|-----------:|-----------:|---------:|---------:|
| effects.buildSim.diamond5                           |     670781 |     228542 |      211 |      273 |
| effects.buildSim.fail_early                         |     667851 |     225709 |      198 |      260 |
| effects.buildSim.fail_late                          |     667851 |     225709 |      197 |      259 |
| effects.buildSim.fail_mid                           |     667851 |     225709 |      200 |      269 |
| effects.buildSim.linear100                          |     687630 |     244690 |      214 |      274 |
| effects.buildSim.linear50                           |     677730 |     235190 |      201 |      267 |
| effects.buildSim.mixed_small                        |     696509 |     253099 |      207 |      270 |
| effects.buildSim.tree5                              |     679557 |     237008 |      201 |      267 |
| effects.buildSim.wide100                            |     685545 |     242500 |      201 |      259 |
| effects.buildSim.wide50                             |     676795 |     234200 |      195 |      265 |
| effects.interp.countdown1000                        |     936193 |     484044 |      249 |      324 |
| effects.interp.fib10                                |     725956 |     281782 |      234 |      301 |
| effects.interp.fib15                                |    1315044 |     850216 |      310 |      377 |
| effects.interp.lets100                              |     684360 |     241721 |      196 |      258 |
| effects.interp.lets500                              |     750360 |     305721 |      280 |      344 |
| effects.interp.sum100                               |     703998 |     260549 |      211 |      276 |
| effects.interp.sum1000                              |    1026198 |     571049 |      267 |      341 |
| effects.stateChain.s10k                             |    1358297 |     866093 |      298 |      386 |
| effects.stateChain.s1k                              |     737297 |     290093 |      218 |      286 |
| effects.stress.bindHeavy.s10k                       |     956364 |     474224 |      242 |      310 |
| effects.stress.deepChains.s10k                      |     737776 |     255658 |      213 |      279 |
| effects.stress.effectHeavy.s10k                     |     927849 |     475708 |      242 |      317 |
| effects.stress.mixed.s10k                           |    1207850 |     735709 |      267 |      349 |
| effects.stress.nestedHandlers.d3_i1k                |     724902 |     277754 |      215 |      286 |
| effects.stress.rawGC.s10k                           |      50173 |      50049 |       28 |       44 |
| experimental.descInterp.stateChain.s1k              |    7496558 |    6914616 |     1304 |     1506 |
| experimental.descInterp.stateChain.s1kShort         |    1336651 |     867435 |      325 |      409 |
| tc.bindP.desc-con-trampoline-blame-5000             |    8663017 |    8073924 |     1415 |     1625 |
| tc.bindP.slow-path-chain-5000                       |     983962 |     526681 |      236 |      315 |
| tc.bindP.universal-blame-chain                      |     983962 |     526681 |      249 |      324 |
| tc.check.list-chain-5000                            |    1441118 |     906122 |      329 |      404 |
| tc.check.macro-field                                |     717057 |     271778 |      236 |      302 |
| tc.check.nat-chain-5000                             |    1258523 |     768833 |      300 |      377 |
| tc.checkD.mixed-chain-5000                          |     977030 |     499130 |      258 |      363 |
| tc.conv.alpha-equivalent                            |     706322 |     260874 |      241 |      308 |
| tc.conv.beta-distinct                               |     736876 |     290565 |      239 |      317 |
| tc.conv.identical-deep                              |    1258526 |     768836 |      306 |      383 |
| tc.conv.identical-shallow                           |     676811 |     232158 |      232 |      305 |
| tc.conv.mu-heavy                                    |     678060 |     232799 |      233 |      305 |
| tc.conv.plus-heavy                                  |     720231 |     274519 |      251 |      320 |
| tc.decidable.leDiag50                               |   11624257 |   10904362 |     1865 |     2022 |
| tc.diag.hint-resolve-5000                           |     796961 |     339171 |      234 |      341 |
| tc.diag.pretty-multi-line-5000                      |     810866 |     338518 |      225 |      347 |
| tc.diag.pretty-one-line-5000                        |     771813 |     309469 |      218 |      334 |
| tc.e2e.datatype-macro-big                           |     717064 |     271785 |      245 |      318 |
| tc.e2e.datatypeI-fin-deep                           |     770483 |     321080 |      257 |      331 |
| tc.e2e.let-chain-100                                |     809129 |     363577 |      262 |      332 |
| tc.e2e.tc-test-suite-full                           |  113049617 |  109375488 |    29115 |    23847 |
| tc.e2e.tc-test-suite-per-module.check               |    5847640 |    5086198 |     1344 |     1370 |
| tc.e2e.tc-test-suite-per-module.conv                |   10425351 |    9700906 |     1818 |     1835 |
| tc.e2e.tc-test-suite-per-module.elaborate           |    7052338 |    5867395 |     1039 |     1246 |
| tc.e2e.tc-test-suite-per-module.eval                |    2087356 |    1493334 |      455 |      559 |
| tc.e2e.tc-test-suite-per-module.hoas                |   77677916 |   75622965 |    23620 |    18362 |
| tc.e2e.tc-test-suite-per-module.quote               |    4371784 |    3850508 |      670 |      822 |
| tc.e2e.tc-test-suite-per-module.term                |     757679 |     281583 |      296 |      372 |
| tc.e2e.tc-test-suite-per-module.value               |     757579 |     281483 |      281 |      358 |
| tc.e2e.tc-test-suite-per-module.verified            |    3643652 |    3105107 |      739 |      871 |
| tc.elaborate.flatten                                |     685100 |     233545 |      234 |      304 |
| tc.elaborate.recursive                              |     837118 |     374122 |      261 |      339 |
| tc.generic.derive-deps                              |     703276 |     257675 |      255 |      319 |
| tc.generic.derive-descriptor                        |     671839 |     228168 |      230 |      302 |
| tc.generic.derive-schema                            |     671835 |     228164 |      236 |      302 |
| tc.generic.functional-builder-chain                 |    1291060 |     836067 |      336 |      425 |
| tc.generic.metadata-normalize                       |     671677 |     228162 |      222 |      286 |
| tc.generic.synthetic-builder-chain                  |    1127153 |     673709 |      329 |      417 |
| tc.generic.view-review                              |     705032 |     259445 |      249 |      325 |
| tc.infer.deep-app-100                               |     909508 |     458183 |      278 |      365 |
| tc.meta.postpone-and-wake-100                       |     707600 |     251304 |      221 |      302 |
| tc.meta.solve-chain-100                             |     689176 |     244298 |      214 |      278 |
| tc.ornaments.alg-list-to-vec-check                  |    1420230 |     961763 |      359 |      441 |
| tc.ornaments.functional-diagnostics-missing-builder |     671968 |     228246 |      229 |      304 |
| tc.ornaments.functional-liftProducer-check          |     694406 |     249173 |      248 |      319 |
| tc.ornaments.functional-synthesis-build             |     829336 |     380389 |      271 |      346 |
| tc.ornaments.ornCompose-check                       |     879603 |     431321 |      277 |      345 |
| tc.ornaments.ornDesc-normalize                      |     670943 |     227390 |      229 |      290 |
| tc.ornaments.ornForget-check                        |     825372 |     376527 |      262 |      324 |
| tc.ornaments.ornForget-elaborate                    |     671300 |     227731 |      223 |      284 |
| tc.quote.closed                                     |     703973 |     257779 |      264 |      335 |
| tc.quote.open                                       |     676088 |     231439 |      238 |      310 |
| tc.quote.stuck                                      |     678818 |     234547 |      235 |      309 |
| tc.surface.toy-elaborate-100                        |   15270467 |   14476761 |     2789 |     2821 |

