# Even bases with exactly one four-digit Kaprekar cycle

Write an input `0 ≤ x < B⁴` with four base-`B` digits, padding with zeros on the left.
A Kaprekar step subtracts the ascending arrangement from the descending arrangement.
A cycle is the forward orbit of a periodic input whose four digits are not all equal.
Cyclic shifts describe the same orbit, and fixed points count as cycles of least period one.

For even `B ≥ 2`, the bases with exactly one cycle are the following.

| Base | Range | Least period |
| --- | --- | --- |
| `3 · 2^(2k+1)` | `k ≥ 0` | `6(k+1)` |
| `5 · 2^(2k+1)` | `k ≥ 0` | `1` |
| `7 · 2^n` | `n ≥ 1` and `3 ∤ n` | `3` |

Base ten lies in the second family, and its fixed point is `6174`.

The two declarations selected in [Challenge.lean](Challenge.lean) state Corollary 2 of
Rustem Galyavin's [*Cycles of the four-digit Kaprekar map in even bases*](https://doi.org/10.5281/zenodo.24358739).
They settle the pattern recorded in Remark 28 of Chen, Ono, Schwartz and Thakur's
[*Four-digit Kaprekar dynamics in odd bases*](https://arxiv.org/abs/2606.20439).
The cycle classification behind the corollary concerns the dependence of periodic orbits
on the base's odd factor and power of two.

[Solution.lean](Solution.lean) proves the compared declarations by conjugating the map
in the Challenge to the positional digit map of `KaprekarBoundary.every_even_base` in
[TheoremC.lean](TheoremC.lean). The underlying development is a module-system port of the
paper's [released Lean source](https://github.com/galyavin/kaprekar-dynamics/tree/9a2b7e90c8fdd39dc654b383f07c678e8cd8da45/cycles-even-bases/ancillary/lean).
The two proof obligations in Challenge are intentional. Comparator checks the corresponding
proofs in Solution against their exact types and the definitions those types use.

## Build

With elan on your path, run these commands from the repository root.
The pinned toolchain is Lean 4.35.0-rc2. The development uses only Lean core and Std.

```sh
lake build
lake env lean Solution.lean
```

The Solution prints the axiom dependencies of both compared declarations.
The [Palomar preflight workflow](.github/workflows/palomar-preflight.yml) runs the pinned
full reusable verification workflow on the commit selected by the responsible author or maintainer.

The repository is MIT-licensed. Author and maintainer information, sources, and AI assistance
are recorded in [formalization.yaml](formalization.yaml).
