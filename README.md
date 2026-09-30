# Sharp Radial Clipping

Lean 4/mathlib verification of numbered results 2.1–5.2 in Danila Litvinov's
manuscript *A Sharp Joint Bias–Energy Envelope for Radial Clipping*
(*Точная совместная огибающая смещения и энергии радиального клиппинга*).
The repository includes the complete proof sources, not just references to
files on the author's computer. The manuscript itself is not included here.

## Find a result

Each file in [`Numbered`](Numbered) corresponds to one numbered statement.
It prints the formal statement (`#check`) and axiom dependencies (`#print axioms`)
of a kernel-checked alias of the proved declaration. The detailed proof steps
and shared lemmas are in [`SharpRadialClipping`](SharpRadialClipping).

| Article result | Topic | Numbered file | Main proof source |
| --- | --- | --- | --- |
| 2.1 | Deterministic sharp envelope | [2.1.lean](Numbered/2.1.lean) | [`Deterministic.lean`](SharpRadialClipping/Deterministic.lean) |
| 2.2 | Endpoint `p = 1` | [2.2.lean](Numbered/2.2.lean) | [`DeterministicP1.lean`](SharpRadialClipping/DeterministicP1.lean) |
| 3.1 | Stochastic envelope | [3.1.lean](Numbered/3.1.lean) | [`Stochastic.lean`](SharpRadialClipping/Stochastic.lean), [`StochasticConditionalP1.lean`](SharpRadialClipping/StochasticConditionalP1.lean) |
| 3.2 | Sharpness | [3.2.lean](Numbered/3.2.lean) | [`Sharpness.lean`](SharpRadialClipping/Sharpness.lean), [`StochasticSharpP1.lean`](SharpRadialClipping/StochasticSharpP1.lean) |
| 3.3 | Conditional envelope | [3.3.lean](Numbered/3.3.lean) | [`ConditionalExtended.lean`](SharpRadialClipping/ConditionalExtended.lean), [`StochasticConditionalP1.lean`](SharpRadialClipping/StochasticConditionalP1.lean) |
| 4.1 | Exact attainable set | [4.1.lean](Numbered/4.1.lean) | [`Article41.lean`](SharpRadialClipping/Article41.lean) |
| 4.2 | Pointwise arc lemma | [4.2.lean](Numbered/4.2.lean) | [`PointwiseArc.lean`](SharpRadialClipping/PointwiseArc.lean) |
| 4.3 | Signed support function | [4.3.lean](Numbered/4.3.lean) | [`SignedSupport.lean`](SharpRadialClipping/SignedSupport.lean), [`SignedSupportP1.lean`](SharpRadialClipping/SignedSupportP1.lean) |
| 4.4 | Two-atom realization | [4.4.lean](Numbered/4.4.lean) | [`TwoAtom.lean`](SharpRadialClipping/TwoAtom.lean) |
| 4.5 | All-threshold 3D realization | [4.5.lean](Numbered/4.5.lean) | [`AllThresholdsFinalPrep.lean`](SharpRadialClipping/AllThresholdsFinalPrep.lean) and its imported modules |
| 5.1 | Reinsurance application | [5.1.lean](Numbered/5.1.lean) | [`ApplicationReinsuranceFull.lean`](SharpRadialClipping/ApplicationReinsuranceFull.lean) |
| 5.2 | Trading application | [5.2.lean](Numbered/5.2.lean) | [`ApplicationTrading.lean`](SharpRadialClipping/ApplicationTrading.lean) |

Some results require more than one source module because the endpoint `p = 1`
is proved separately, or because substantial common lemmas are shared. The
numbered files are entry points, **not independent one-file reproofs**.
For Proposition 3.2 with `1 < p ≤ 2`, the bound for every admissible law and
the matching supremum already on centered two-point laws together prove the
claimed global sharp constant; both facts are exposed in `Numbered/3.2.lean`.
For Corollary 5.2, Lean numbers periods from `0` to `T-1`, whereas the article
uses `1` to `T`; this is only an index shift.

## Verify

The versions of Lean and mathlib are pinned by `lean-toolchain` and
`lake-manifest.json`. With Lean/Elan and Lake installed, from this directory:

```sh
lake build SharpRadialClipping
for proof_file in Numbered/*.lean; do
  lake env lean "$proof_file" || exit 1
done
```

Run a numbered file to see its exact Lean statement and axiom report; follow
its import and the `Full proof` comment to inspect the proof. Do not run a bare
`lake update` for verification: that command may upgrade pinned dependencies.

The build and all numbered files passed locally on 2026-09-30. Their axiom
reports contained only `propext`, `Classical.choice`, and `Quot.sound`; no
`sorry`, `admit`, or additional axioms are used. For scope and assumptions,
see [`FORMALIZATION_STATUS.md`](FORMALIZATION_STATUS.md). To compare these
formal statements with the article's wording, use the manuscript named above;
an authoritative public manuscript link has not yet been added.
