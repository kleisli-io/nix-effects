# Bench run: baseline

- **Timestamp**: 2026-04-22T10:22:38Z
- **Nix**: 2.31.4
- **System**: x86_64-linux
- **Runs per workload**: 5

| Workload                                  |     values |     thunks |   cpu ms |  wall ms |
|-------------------------------------------|-----------:|-----------:|---------:|---------:|
| effects.buildSim.diamond5                 |     670869 |     228479 |      206 |      262 |
| effects.buildSim.fail_early               |     667739 |     225617 |      196 |      255 |
| effects.buildSim.fail_late                |     667739 |     225617 |      197 |      260 |
| effects.buildSim.fail_mid                 |     667739 |     225617 |      204 |      266 |
| effects.buildSim.linear100                |     688738 |     244627 |      196 |      262 |
| effects.buildSim.linear50                 |     678238 |     235127 |      203 |      276 |
| effects.buildSim.mixed_small              |     698121 |     253036 |      213 |      271 |
| effects.buildSim.tree5                    |     680159 |     236945 |      214 |      289 |
| effects.buildSim.wide100                  |     686467 |     242437 |      201 |      268 |
| effects.buildSim.wide50                   |     677217 |     234137 |      191 |      258 |
| effects.interp.countdown1000              |     949115 |     483977 |      245 |      324 |
| effects.interp.fib10                      |     728787 |     281719 |      211 |      267 |
| effects.interp.fib15                      |    1347509 |     850153 |      287 |      382 |
| effects.interp.lets100                    |     684869 |     241654 |      200 |      263 |
| effects.interp.lets500                    |     753269 |     305654 |      273 |      339 |
| effects.interp.sum100                     |     705824 |     260486 |      208 |      272 |
| effects.interp.sum1000                    |    1045124 |     570986 |      264 |      337 |
| effects.stress.bindHeavy.s10k             |     976276 |     474157 |      243 |      319 |
| effects.stress.deepChains.s10k            |     737619 |     255521 |      210 |      282 |
| effects.stress.effectHeavy.s10k           |     937752 |     475631 |      241 |      304 |
| effects.stress.mixed.s10k                 |    1227753 |     735632 |      271 |      348 |
| effects.stress.nestedHandlers.d3_i1k      |     728815 |     277691 |      211 |      270 |
| effects.stress.rawGC.s10k                 |      50171 |      50047 |       35 |       53 |
| tc.check.list-chain-5000                  |    3796662 |    3243796 |      740 |      866 |
| tc.check.macro-field                      |     693141 |     250106 |      208 |      271 |
| tc.check.nat-chain-5000                   |    1140298 |     652572 |      249 |      317 |
| tc.conv.alpha-equivalent                  |     669578 |     226906 |      204 |      266 |
| tc.conv.beta-distinct                     |     671095 |     228292 |      210 |      270 |
| tc.conv.identical-deep                    |    1140301 |     652575 |      247 |      325 |
| tc.conv.identical-shallow                 |     670301 |     227514 |      199 |      263 |
| tc.conv.mu-heavy                          |     672571 |     229344 |      209 |      272 |
| tc.conv.plus-heavy                        |     672704 |     229915 |      202 |      264 |
| tc.e2e.datatype-macro-big                 |     693143 |     250108 |      216 |      283 |
| tc.e2e.datatypeI-fin-deep                 |     778408 |     331843 |      228 |      297 |
| tc.e2e.tc-test-suite-full                 |   16509670 |   14921929 |     3262 |     3349 |
| tc.e2e.tc-test-suite-per-module.check     |     976762 |     414931 |      255 |      327 |
| tc.e2e.tc-test-suite-per-module.conv      |     974217 |     413328 |      253 |      316 |
| tc.e2e.tc-test-suite-per-module.elaborate |   11871024 |   10912367 |     2576 |     2531 |
| tc.e2e.tc-test-suite-per-module.eval      |     833484 |     301526 |      233 |      297 |
| tc.e2e.tc-test-suite-per-module.hoas      |    3131944 |    2419813 |      576 |      685 |
| tc.e2e.tc-test-suite-per-module.quote     |    1063941 |     513022 |      256 |      327 |
| tc.e2e.tc-test-suite-per-module.term      |     712279 |     251604 |      223 |      292 |
| tc.e2e.tc-test-suite-per-module.value     |     712278 |     251603 |      225 |      292 |
| tc.e2e.tc-test-suite-per-module.verified  |    1941587 |    1457595 |      430 |      523 |
| tc.elaborate.flatten                      |     681730 |     231280 |      195 |      262 |
| tc.elaborate.recursive                    |     731063 |     276544 |      202 |      274 |
| tc.infer.deep-app-100                     |     762411 |     318123 |      230 |      294 |
| tc.quote.closed                           |     689180 |     244935 |      207 |      263 |
| tc.quote.open                             |     670439 |     227681 |      207 |      273 |
| tc.quote.stuck                            |     675816 |     232766 |      220 |      275 |

