# Radial Clipping Verification

Lean 4/mathlib verification of the numbered mathematical results 2.1–5.2 in
the radial-clipping article. The repository includes the complete proof sources,
not just references to files on the author's computer.

## Find a result

Each file in [`Numbered`](Numbered) corresponds to one numbered statement.
It provides a kernel-checked alias of the proved declaration and prints its
axiom dependencies. The detailed proof steps and shared lemmas are in [`H099`](H099).

| Article result | Topic | Numbered file | Main proof source |
| --- | --- | --- | --- |
| 2.1 | Deterministic sharp envelope | [2.1.lean](Numbered/2.1.lean) | [`Deterministic.lean`](H099/Deterministic.lean) |
| 2.2 | Endpoint `p = 1` | [2.2.lean](Numbered/2.2.lean) | [`DeterministicP1.lean`](H099/DeterministicP1.lean) |
| 3.1 | Stochastic envelope | [3.1.lean](Numbered/3.1.lean) | [`Stochastic.lean`](H099/Stochastic.lean), [`StochasticConditionalP1.lean`](H099/StochasticConditionalP1.lean) |
| 3.2 | Sharpness | [3.2.lean](Numbered/3.2.lean) | [`Sharpness.lean`](H099/Sharpness.lean), [`StochasticSharpP1.lean`](H099/StochasticSharpP1.lean) |
| 3.3 | Conditional envelope | [3.3.lean](Numbered/3.3.lean) | [`ConditionalExtended.lean`](H099/ConditionalExtended.lean), [`StochasticConditionalP1.lean`](H099/StochasticConditionalP1.lean) |
| 4.1 | Exact attainable set | [4.1.lean](Numbered/4.1.lean) | [`Article41.lean`](H099/Article41.lean) |
| 4.2 | Pointwise arc lemma | [4.2.lean](Numbered/4.2.lean) | [`PointwiseArc.lean`](H099/PointwiseArc.lean) |
| 4.3 | Signed support function | [4.3.lean](Numbered/4.3.lean) | [`SignedSupport.lean`](H099/SignedSupport.lean), [`SignedSupportP1.lean`](H099/SignedSupportP1.lean) |
| 4.4 | Two-atom realization | [4.4.lean](Numbered/4.4.lean) | [`TwoAtom.lean`](H099/TwoAtom.lean) |
| 4.5 | All-threshold 3D realization | [4.5.lean](Numbered/4.5.lean) | [`AllThresholdsFinalPrep.lean`](H099/AllThresholdsFinalPrep.lean) and its imported modules |
| 5.1 | Reinsurance application | [5.1.lean](Numbered/5.1.lean) | [`ApplicationReinsuranceFull.lean`](H099/ApplicationReinsuranceFull.lean) |
| 5.2 | Trading application | [5.2.lean](Numbered/5.2.lean) | [`ApplicationTrading.lean`](H099/ApplicationTrading.lean) |

Some results require more than one source module because the endpoint `p = 1`
is proved separately, or because substantial common lemmas are shared. The
numbered files are entry points, **not independent one-file reproofs**.

## Verify

The versions of Lean and mathlib are pinned by `lean-toolchain` and
`lake-manifest.json`. With Lean/Elan and Lake installed, from this directory:

```sh
lake update
lake build H099
for proof_file in Numbered/*.lean; do
  lake env lean "$proof_file" || exit 1
done
```

The build and all numbered files passed locally on 2026-09-30. Their axiom
reports contained only `propext`, `Classical.choice`, and `Quot.sound`; no
`sorry`, `admit`, or additional axioms are used. For scope and assumptions,
see [`FORMALIZATION_STATUS.md`](FORMALIZATION_STATUS.md) and the included
[`THEOREM_CONTRACT.md`](docs/THEOREM_CONTRACT.md).
