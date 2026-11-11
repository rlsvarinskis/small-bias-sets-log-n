# Lean 4 formalization

Machine-checked proof that explicit small-bias sets of size O(log n / ε³) exist in ℤ/nℤ. It follows
`../proof.md` step by step and uses the notation of `../proof.md` and the slideshow `../tutorial.html`.

Built with Lean `v4.36.0-rc2` and Mathlib `v4.36.0-rc2`, which are pinned in `lean-toolchain` and `lakefile.toml`.

```
lake exe cache get   # prebuilt Mathlib
lake build
```

The build has no errors, and Lean reports no warnings. Lake only notes that the files import Mathlib modules
without being written as modules themselves. `#print axioms` on every main theorem reports only `propext`,
`Classical.choice`, `Quot.sound`, and there is no `sorry`.

## Main statement (`Smallbias/Main.lean`, `SmallBias.explicitList_spec`)

For `n ≥ 2` and `0 < ε ≤ 1`, the explicitly defined list `ks = explicitList n ε` satisfies:

* every `k ∈ ks` is in `[0, n)`;
* `length ks ≤ 235 · (log n + 2) / ε³`, and exactly `|P| · s` (`main_size_exact`);
* for every `0 < l < n`: `‖ (1/|ks|) · Σ_{k ∈ ks} exp(2πi·k·l/n) ‖ ≤ ε`.

The statement uses only Mathlib notions (`Complex.exp`, `List`, `Real.log`).

## Files

| file | content |
|---|---|
| `Core.lean` | Lemma 1 (`avgAt_hand`: the hands split into groups), Lemma 2 (`dvd_of_angle_small`: a bad group's prime divides ℓ*; `card_bad_le`: at most `log_{R+1}(n/2)` of them), `core_bias_bound` |
| `Greedy.lean` | Lemma 3 (`greedy_mult_bound`): the greedy multipliers (`greedyList`, least minimiser of the potential `Φ`) with `D` compass directions, the direction-rounding lemma `exists_dir_ge` |
| `Main.lean` | Lemma 4 (`card_candidates_ge`, via Mathlib's Chebyshev bound), the parameters, `main_bias`, `main_size_exact`, `main_size`, `explicitList_spec` |

## Notation

| tutorial / proof.md | Lean |
|---|---|
| Ŝ(ℓ), the average of the hands at time ℓ | `avgAt T k ℓ` |
| hand c·q⁻¹ of group q | `hand C (q, i)` |
| base hand's angle ℓ·q⁻¹/n, signed, in turns | `angle (ℓ * q⁻¹)`, where `angle y = y.valMinAbs / n` |
| group average at base angle a, (1/s) Σ e(c·a) | `groupAvg C a` |
| compass direction u, ω_u = e(−u/D) | `dir D u` |
| reach X_{a,u}(c) at grid angle a = j/M | `reach D M j u c` |
| potential Φ | `Φ` |

## Parameters

| symbol | Lean | value |
|---|---|---|
| `R` | `Rpar` | `⌈4 log n / ε⌉ + 16` |
| `K` | | `Nat.log (R+1) (n/2)` |
| `\|P\|` | `numPrimes` | `⌊3K/ε⌋ + 1` |
| `P` | `primes` | the `\|P\|` smallest primes in `(R, R²]` not dividing `n` |
| `P_max` | `Pmax` | `max P` |
| `δ` | | `1/(2 P_max)` |
| `N` | `Npar` | `⌈300 P_max/ε⌉` |
| `M` | `Mpar` | `⌈1000N/ε⌉` |
| `D` | | `16` |
| `t` | | `5ε/8` |
| `s` | `spar` | `⌈2 log(16(M+1)) / t²⌉` |
| `C` | `multList` | the greedy multipliers |

**What "deterministic" means here.** The construction is a fully determined definition. Each greedy step takes the *least*
`c < N` minimising the potential. It is `noncomputable` in Lean because it compares real numbers.
Running time is not formalized.

**The Python code.** `../smallbias.py` has two entry points.
- `formal_parameters` computes this file's exact parameters and size `|P| · s`.
- `build` uses the same outer structure (`R`, `K`, the primes) but a much smaller multiplier search: `N = 16 P_max`, a grid of about `4N`, and 8 directions.

The set `build` outputs is not formally linked to this proof. It is checked by its own certificate instead.
