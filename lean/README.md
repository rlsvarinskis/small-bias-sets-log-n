# Lean 4 formalization

Machine-checked proof that explicit small-bias sets of size O(log n / ε³) exist in ℤ/nℤ. It follows
`../proof.md` step by step.

Built with Lean `v4.36.0-rc2` and Mathlib `v4.36.0-rc2`, which are pinned in `lean-toolchain` and `lakefile.toml`.

```
lake exe cache get   # prebuilt Mathlib
lake build
```

The build has no errors and no warnings. `#print axioms` on every main theorem reports only `propext`,
`Classical.choice`, `Quot.sound`, and there is no `sorry`.

## Main statement (`Smallbias/Main.lean`, `SmallBias.explicitList_spec`)

For `n ≥ 2` and `0 < ε ≤ 1`, the explicitly defined list `ks = explicitList n ε` satisfies:

* every `k ∈ ks` is in `[0, n)`;
* `length ks ≤ 235 · (log n + 2) / ε³`, and exactly `k · s` (`main_size_exact`);
* for every `0 < l < n`: `‖ (1/|ks|) · Σ_{k ∈ ks} exp(2πi·k·l/n) ‖ ≤ ε`.

The statement uses only Mathlib notions (`Complex.exp`, `List`, `Real.log`).

## Files

| file | content |
|---|---|
| `Core.lean` | Lemma 1 (product structure), Lemma 2 (a bad prime divides ℓ; at most `log_{R+1}(n/2)` of them), `core_bias_bound` |
| `Greedy.lean` | Lemma 3: the greedy search (`greedyList`, least minimiser of the potential) with `D` directions, the direction-rounding lemma `exists_rot_ge`, and `greedy_inner_bound` |
| `Main.lean` | Lemma 4 (`card_candidates_ge`, via Mathlib's Chebyshev bound), the parameters, `main_bias`, `main_size_exact`, `main_size`, `explicitList_spec` |

## Parameters

| symbol | value |
|---|---|
| `R` | `⌈4 log n / ε⌉ + 16` |
| `K` | `Nat.log (R+1) (n/2)` |
| `k` | `⌊3K/ε⌋ + 1` |
| `P` | the `k` smallest primes in `(R, R²]` not dividing `n` |
| `Q` | `max P` |
| `δ` | `1/(2Q)` |
| `N` | `⌈300Q/ε⌉` |
| `M` | `⌈1000N/ε⌉` |
| `D` | `16` |
| `t` | `5ε/8` |
| `s` | `⌈2 log(16(M+1)) / t²⌉` |

**What "deterministic" means here.** The construction is a fully determined definition. Each greedy step takes the *least*
`c < N` minimising the potential. It is `noncomputable` in Lean because it compares real numbers.
Running time is not formalized.

**The Python code.** `../smallbias.py` has two entry points.
- `formal_parameters` computes this file's exact parameters and size `k · s`.
- `build` uses the same outer structure (`R`, `K`, the primes) but a much smaller inner search: `N = 16Q`, a grid of about `4N`, and 8 directions.

The set `build` outputs is not formally linked to this proof. It is checked by its own certificate instead.
