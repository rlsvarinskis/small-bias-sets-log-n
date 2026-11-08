# Lean 4 formalization

Machine-checked proof that explicit small-bias sets of size O(log n / ε³) exist in ℤ/nℤ, following
`../proof.md` with slightly different parameters (listed below).

Built with Lean `v4.36.0-rc2` and Mathlib `v4.36.0-rc2`, which are pinned in `lean-toolchain` and `lakefile.toml`.

```
lake exe cache get   # prebuilt Mathlib
lake build
```

`#print axioms` on every main theorem reports only `propext`, `Classical.choice`, `Quot.sound`.
There is no `sorry`.

## Main statement (`Smallbias/Main.lean`, `SmallBias.explicitList_spec`)

For `n ≥ 2` and `0 < ε ≤ 1`, the explicitly defined list `ks = explicitList n ε` satisfies:

* every `k ∈ ks` is in `[0, n)`;
* `length ks ≤ 1625 · (20 · log n / ε + 32769) / ε²`;
* for every `0 < l < n`: `‖ (1/|ks|) · Σ_{k ∈ ks} exp(2πi·k·l/n) ‖ ≤ ε`.

The statement uses only Mathlib notions (`Complex.exp`, `List`, `Real.log`).

## Files

| file | content |
|---|---|
| `Core.lean` | Lemma 1 (product structure), Lemma 2 (a bad prime divides ℓ; at most `log_{m+1}(n/2)` of them), `core_bias_bound` |
| `Greedy.lean` | Lemma 3: the greedy inner-set search as a Lean definition (`greedyList`, least minimiser of the potential), Hoeffding-type step via convexity of `exp`, grid and Lipschitz argument, `greedy_inner_bound` |
| `Main.lean` | parameters, prime counting (Mathlib's Chebyshev bounds), `main_bias`, `main_size`, `explicitList_spec` |

## Relation to `../proof.md`

`proof.md` follows this formalization step by step. Both use primes in `(⌊√Q⌋, Q]`, the same parameters,
and a 4-direction greedy search.

* **The Python code differs.** `smallbias.py` uses an earlier variant (primes in `(Q/2, Q]`, `N = 16Q`). It is not
  formally linked to this proof; each set it outputs is checked by its own certificate instead.
* **What "deterministic" means here:** the construction is a fully determined definition. Each greedy step takes
  the *least* `c < N` minimising the potential. It is `noncomputable` in Lean because it compares real numbers.
* **Running time is not formalized.**
