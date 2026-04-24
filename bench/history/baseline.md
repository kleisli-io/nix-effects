# Bench run: baseline

- **Timestamp**: 2026-04-24T09:40:16Z
- **Nix**: 2.31.4
- **System**: x86_64-linux
- **Runs per workload**: 50

| Workload                                  |     values |     thunks |   cpu ms |  wall ms |
|-------------------------------------------|-----------:|-----------:|---------:|---------:|
| effects.buildSim.diamond5                 |     670882 |     228488 |      193 |      250 |
| effects.buildSim.fail_early               |     667752 |     225626 |      196 |      251 |
| effects.buildSim.fail_late                |     667752 |     225626 |      197 |      256 |
| effects.buildSim.fail_mid                 |     667752 |     225626 |      199 |      262 |
| effects.buildSim.linear100                |     688751 |     244636 |      198 |      261 |
| effects.buildSim.linear50                 |     678251 |     235136 |      197 |      258 |
| effects.buildSim.mixed_small              |     698134 |     253045 |      202 |      266 |
| effects.buildSim.tree5                    |     680172 |     236954 |      195 |      255 |
| effects.buildSim.wide100                  |     686480 |     242446 |      196 |      258 |
| effects.buildSim.wide50                   |     677230 |     234146 |      193 |      256 |
| effects.interp.countdown1000              |     949128 |     483986 |      238 |      310 |
| effects.interp.fib10                      |     728800 |     281728 |      203 |      266 |
| effects.interp.fib15                      |    1347522 |     850162 |      293 |      366 |
| effects.interp.lets100                    |     684882 |     241663 |      197 |      259 |
| effects.interp.lets500                    |     753282 |     305663 |      265 |      332 |
| effects.interp.sum100                     |     705837 |     260495 |      200 |      261 |
| effects.interp.sum1000                    |    1045137 |     570995 |      254 |      327 |
| effects.stress.bindHeavy.s10k             |     976289 |     474166 |      229 |      296 |
| effects.stress.deepChains.s10k            |     737632 |     255530 |      199 |      265 |
| effects.stress.effectHeavy.s10k           |     937765 |     475640 |      229 |      296 |
| effects.stress.mixed.s10k                 |    1227766 |     735641 |      264 |      338 |
| effects.stress.nestedHandlers.d3_i1k      |     728828 |     277700 |      198 |      265 |
| effects.stress.rawGC.s10k                 |      50171 |      50047 |       27 |       45 |
| tc.bindP.slow-path-chain-5000             |     933333 |     476102 |      220 |      289 |
| tc.check.list-chain-5000                  |    3836865 |    3283951 |      756 |      876 |
| tc.check.macro-field                      |     693689 |     250606 |      212 |      275 |
| tc.check.nat-chain-5000                   |    1140491 |     652717 |      253 |      325 |
| tc.conv.alpha-equivalent                  |     669763 |     227043 |      204 |      268 |
| tc.conv.beta-distinct                     |     671308 |     228457 |      207 |      270 |
| tc.conv.identical-deep                    |    1140494 |     652720 |      253 |      324 |
| tc.conv.identical-shallow                 |     670494 |     227659 |      203 |      268 |
| tc.conv.mu-heavy                          |     672816 |     229541 |      206 |      266 |
| tc.conv.plus-heavy                        |     672975 |     230138 |      205 |      265 |
| tc.diag.hint-resolve-5000                 |     795380 |     338190 |      221 |      324 |
| tc.diag.pretty-multi-line-5000            |     800416 |     338218 |      218 |      327 |
| tc.diag.pretty-one-line-5000              |     771372 |     309178 |      215 |      321 |
| tc.e2e.datatype-macro-big                 |     693692 |     250609 |      214 |      272 |
| tc.e2e.datatypeI-fin-deep                 |     778670 |     332057 |      221 |      286 |
| tc.e2e.let-chain-100                      |     746721 |     303282 |      223 |      285 |
| tc.e2e.tc-test-suite-full                 |   16915425 |   15290544 |     3512 |     3341 |
| tc.e2e.tc-test-suite-per-module.check     |    1245824 |     645574 |      363 |      509 |
| tc.e2e.tc-test-suite-per-module.conv      |     966888 |     407873 |      254 |      324 |
| tc.e2e.tc-test-suite-per-module.elaborate |   11983665 |   11027045 |     2698 |     2640 |
| tc.e2e.tc-test-suite-per-module.eval      |     826163 |     296061 |      245 |      311 |
| tc.e2e.tc-test-suite-per-module.hoas      |    3133169 |    2422881 |      580 |      694 |
| tc.e2e.tc-test-suite-per-module.quote     |    1056586 |     507553 |      264 |      338 |
| tc.e2e.tc-test-suite-per-module.term      |     705116 |     246175 |      220 |      285 |
| tc.e2e.tc-test-suite-per-module.value     |     705084 |     246143 |      227 |      296 |
| tc.e2e.tc-test-suite-per-module.verified  |    1943139 |    1461092 |      441 |      530 |
| tc.elaborate.flatten                      |     681816 |     231343 |      204 |      269 |
| tc.elaborate.recursive                    |     731149 |     276607 |      203 |      265 |
| tc.infer.deep-app-100                     |     764414 |     320078 |      228 |      291 |
| tc.quote.closed                           |     689392 |     245094 |      208 |      272 |
| tc.quote.open                             |     670660 |     227849 |      206 |      268 |
| tc.quote.stuck                            |     676198 |     233095 |      207 |      272 |

