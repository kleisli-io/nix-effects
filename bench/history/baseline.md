# Bench run: baseline

- **Timestamp**: 2026-05-13T13:34:22Z
- **Nix**: 2.31.4
- **System**: x86_64-linux
- **Runs per workload**: 50

| Workload                                  |     values |     thunks |   cpu ms |  wall ms |
|-------------------------------------------|-----------:|-----------:|---------:|---------:|
| effects.buildSim.diamond5                 |     670891 |     228493 |      197 |      253 |
| effects.buildSim.fail_early               |     667761 |     225631 |      193 |      247 |
| effects.buildSim.fail_late                |     667761 |     225631 |      195 |      253 |
| effects.buildSim.fail_mid                 |     667761 |     225631 |      196 |      256 |
| effects.buildSim.linear100                |     688760 |     244641 |      200 |      262 |
| effects.buildSim.linear50                 |     678260 |     235141 |      194 |      254 |
| effects.buildSim.mixed_small              |     698143 |     253050 |      204 |      266 |
| effects.buildSim.tree5                    |     680181 |     236959 |      201 |      259 |
| effects.buildSim.wide100                  |     686489 |     242451 |      216 |      286 |
| effects.buildSim.wide50                   |     677239 |     234151 |      224 |      294 |
| effects.interp.countdown1000              |     949137 |     483991 |      250 |      332 |
| effects.interp.fib10                      |     728809 |     281733 |      211 |      280 |
| effects.interp.fib15                      |    1347531 |     850167 |      303 |      379 |
| effects.interp.lets100                    |     684891 |     241668 |      207 |      272 |
| effects.interp.lets500                    |     753291 |     305668 |      274 |      346 |
| effects.interp.sum100                     |     705846 |     260500 |      210 |      278 |
| effects.interp.sum1000                    |    1045146 |     571000 |      272 |      358 |
| effects.stress.bindHeavy.s10k             |     976298 |     474171 |      244 |      316 |
| effects.stress.deepChains.s10k            |     737641 |     255535 |      213 |      288 |
| effects.stress.effectHeavy.s10k           |     937774 |     475645 |      234 |      300 |
| effects.stress.mixed.s10k                 |    1227775 |     735646 |      269 |      340 |
| effects.stress.nestedHandlers.d3_i1k      |     728837 |     277705 |      207 |      271 |
| effects.stress.rawGC.s10k                 |      50171 |      50047 |       29 |       47 |
| tc.bindP.slow-path-chain-5000             |     933379 |     476142 |      225 |      291 |
| tc.check.list-chain-5000                  |    3466566 |    2913243 |      651 |      768 |
| tc.check.macro-field                      |     696635 |     253246 |      216 |      280 |
| tc.check.nat-chain-5000                   |    1222926 |     734871 |      280 |      353 |
| tc.conv.alpha-equivalent                  |     680157 |     236981 |      210 |      274 |
| tc.conv.beta-distinct                     |     672727 |     229621 |      207 |      268 |
| tc.conv.identical-deep                    |    1222929 |     734874 |      295 |      372 |
| tc.conv.identical-shallow                 |     671757 |     228661 |      210 |      271 |
| tc.conv.mu-heavy                          |     672287 |     228797 |      211 |      276 |
| tc.conv.plus-heavy                        |     675035 |     231904 |      218 |      289 |
| tc.diag.hint-resolve-5000                 |     796396 |     338809 |      225 |      336 |
| tc.diag.pretty-multi-line-5000            |     800457 |     338235 |      225 |      334 |
| tc.diag.pretty-one-line-5000              |     771413 |     309195 |      216 |      324 |
| tc.e2e.datatype-macro-big                 |     696642 |     253253 |      213 |      275 |
| tc.e2e.datatypeI-fin-deep                 |     918976 |     470397 |      254 |      322 |
| tc.e2e.let-chain-100                      |     763184 |     319484 |      230 |      297 |
| tc.e2e.tc-test-suite-full                 |  104642139 |  102086143 |    16437 |    15912 |
| tc.e2e.tc-test-suite-per-module.check     |    6133177 |    5465096 |     1105 |     1260 |
| tc.e2e.tc-test-suite-per-module.conv      |   13859708 |   13172250 |     2489 |     2520 |
| tc.e2e.tc-test-suite-per-module.elaborate |   10749162 |    9756365 |     2256 |     2162 |
| tc.e2e.tc-test-suite-per-module.eval      |    1414275 |     852133 |      333 |      426 |
| tc.e2e.tc-test-suite-per-module.hoas      |   66367394 |   64956050 |    10096 |     9768 |
| tc.e2e.tc-test-suite-per-module.quote     |    3211654 |    2718750 |      520 |      636 |
| tc.e2e.tc-test-suite-per-module.term      |     711289 |     249697 |      233 |      299 |
| tc.e2e.tc-test-suite-per-module.value     |     711195 |     249603 |      232 |      300 |
| tc.e2e.tc-test-suite-per-module.verified  |    7225644 |    6702396 |     1237 |     1413 |
| tc.elaborate.flatten                      |     683188 |     232565 |      207 |      268 |
| tc.elaborate.recursive                    |     735552 |     280856 |      208 |      271 |
| tc.infer.deep-app-100                     |     780396 |     335799 |      229 |      294 |
| tc.quote.closed                           |     696960 |     252381 |      219 |      280 |
| tc.quote.open                             |     671411 |     228403 |      216 |      283 |
| tc.quote.stuck                            |     674750 |     231386 |      217 |      282 |

