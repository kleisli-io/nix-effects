# Bench run: calibrate-20260428-125547

- **Timestamp**: 2026-04-28T13:17:40Z
- **Nix**: 2.31.4
- **System**: x86_64-linux
- **Runs per workload**: 50

| Workload                                  |     values |     thunks |   cpu ms |  wall ms |
|-------------------------------------------|-----------:|-----------:|---------:|---------:|
| effects.buildSim.diamond5                 |     670890 |     228492 |      202 |      265 |
| effects.buildSim.fail_early               |     667760 |     225630 |      210 |      281 |
| effects.buildSim.fail_late                |     667760 |     225630 |      203 |      267 |
| effects.buildSim.fail_mid                 |     667760 |     225630 |      196 |      259 |
| effects.buildSim.linear100                |     688759 |     244640 |      205 |      266 |
| effects.buildSim.linear50                 |     678259 |     235140 |      205 |      266 |
| effects.buildSim.mixed_small              |     698142 |     253049 |      209 |      277 |
| effects.buildSim.tree5                    |     680180 |     236958 |      200 |      265 |
| effects.buildSim.wide100                  |     686488 |     242450 |      207 |      272 |
| effects.buildSim.wide50                   |     677238 |     234150 |      209 |      273 |
| effects.interp.countdown1000              |     949136 |     483990 |      256 |      337 |
| effects.interp.fib10                      |     728808 |     281732 |      214 |      280 |
| effects.interp.fib15                      |    1347530 |     850166 |      313 |      389 |
| effects.interp.lets100                    |     684890 |     241667 |      203 |      267 |
| effects.interp.lets500                    |     753290 |     305667 |      271 |      341 |
| effects.interp.sum100                     |     705845 |     260499 |      199 |      262 |
| effects.interp.sum1000                    |    1045145 |     570999 |      254 |      333 |
| effects.stress.bindHeavy.s10k             |     976297 |     474170 |      230 |      297 |
| effects.stress.deepChains.s10k            |     737640 |     255534 |      205 |      269 |
| effects.stress.effectHeavy.s10k           |     937773 |     475644 |      235 |      308 |
| effects.stress.mixed.s10k                 |    1227774 |     735645 |      284 |      363 |
| effects.stress.nestedHandlers.d3_i1k      |     728836 |     277704 |      209 |      276 |
| effects.stress.rawGC.s10k                 |      50171 |      50047 |       27 |       46 |
| tc.bindP.slow-path-chain-5000             |     933360 |     476123 |      232 |      303 |
| tc.check.list-chain-5000                  |    3827101 |    3274095 |      802 |      939 |
| tc.check.macro-field                      |     694476 |     251301 |      220 |      286 |
| tc.check.nat-chain-5000                   |    1140693 |     652829 |      260 |      329 |
| tc.conv.alpha-equivalent                  |     669957 |     227151 |      207 |      269 |
| tc.conv.beta-distinct                     |     671491 |     228550 |      214 |      280 |
| tc.conv.identical-deep                    |    1140696 |     652832 |      273 |      349 |
| tc.conv.identical-shallow                 |     670695 |     227770 |      205 |      269 |
| tc.conv.mu-heavy                          |     672947 |     229582 |      211 |      273 |
| tc.conv.plus-heavy                        |     673108 |     230181 |      209 |      266 |
| tc.diag.hint-resolve-5000                 |     796398 |     338809 |      216 |      321 |
| tc.diag.pretty-multi-line-5000            |     800459 |     338235 |      217 |      320 |
| tc.diag.pretty-one-line-5000              |     771415 |     309195 |      214 |      317 |
| tc.e2e.datatype-macro-big                 |     694483 |     251308 |      210 |      272 |
| tc.e2e.datatypeI-fin-deep                 |     778958 |     332255 |      225 |      291 |
| tc.e2e.let-chain-100                      |     745826 |     302297 |      225 |      290 |
| tc.e2e.tc-test-suite-full                 |   17223357 |   15591975 |     3754 |     3601 |
| tc.e2e.tc-test-suite-per-module.check     |    1258944 |     655630 |      388 |      537 |
| tc.e2e.tc-test-suite-per-module.conv      |     974433 |     412585 |      276 |      353 |
| tc.e2e.tc-test-suite-per-module.elaborate |   11960808 |   11001476 |     2796 |     2764 |
| tc.e2e.tc-test-suite-per-module.eval      |     832574 |     299714 |      248 |      318 |
| tc.e2e.tc-test-suite-per-module.hoas      |    3441544 |    2723965 |      681 |      801 |
| tc.e2e.tc-test-suite-per-module.quote     |    1062603 |     510838 |      289 |      367 |
| tc.e2e.tc-test-suite-per-module.term      |     710490 |     248837 |      242 |      312 |
| tc.e2e.tc-test-suite-per-module.value     |     710405 |     248752 |      253 |      328 |
| tc.e2e.tc-test-suite-per-module.verified  |    1966588 |    1481779 |      505 |      602 |
| tc.elaborate.flatten                      |     681925 |     231398 |      212 |      277 |
| tc.elaborate.recursive                    |     731258 |     276662 |      217 |      281 |
| tc.infer.deep-app-100                     |     763506 |     319080 |      230 |      293 |
| tc.quote.closed                           |     689596 |     245208 |      230 |      292 |
| tc.quote.open                             |     670841 |     227940 |      227 |      300 |
| tc.quote.stuck                            |     676130 |     232937 |      227 |      297 |
