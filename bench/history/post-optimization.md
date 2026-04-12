# Benchmark: post-optimization

- **Timestamp**: 2026-04-12T16:46:05+02:00
- **Nix**: nix (Nix) 2.31.3
- **System**: Linux 6.12.66 x86_64

## Test Suite
| Benchmark            |     ms |
|----------------------|-------:|
| tests                |  23352 |

## Interpreter
| Benchmark            |     ms |
|----------------------|-------:|
| fib10                |    160 |
| fib15                |    232 |
| fib20                |   1835 |
| lets100              |    157 |
| lets500              |    205 |
| sum100               |    153 |
| sum1000              |    207 |
| countdown1000        |    191 |

## Build Simulator
| Benchmark            |     ms |
|----------------------|-------:|
| linear50             |    161 |
| linear100            |    169 |
| linear200            |    178 |
| wide50               |    153 |
| wide100              |    161 |
| wide200              |    164 |
| diamond5             |    161 |
| diamond8             |    154 |
| tree5                |    162 |
| tree8                |    186 |
| mixed_small          |    154 |
| mixed_medium         |    203 |

## Stress Tests
| Benchmark            |    10k |   100k |
|----------------------|-------:|-------:|
| effectHeavy          |    174 |    412 |
| bindHeavy            |    187 |    567 |
| mixed                |    528 |    703 |
| rawGC                |     28 |     99 |
