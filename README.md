# Kakeya multiplicativity over ℤ/N — kernel-checked Lean proofs

Machine-checked (Lean 4 kernel, no `native_decide`, no `sorry`, no extra
axioms) exact values and multiplicativity laws for minimum Kakeya set
sizes over the rings (ℤ/N)ⁿ.

A **Kakeya set** in (ℤ/N)ⁿ is a set containing a full line
`{a + t·b : t ∈ ℤ/N}` in every direction `b`. `minKakeyaSize N n` is
the least cardinality of such a set. Headline theorems, all closing
over only the standard classical trio
`[propext, Classical.choice, Quot.sound]`:

| Theorem | Statement |
|---|---|
| `minKakeyaSize_three_three` | `minKakeyaSize 3 3 = 13` |
| `minKakeyaSize_six_three` | `minKakeyaSize 6 3 = 65` |
| `minKakeyaSize_six_three_eq_product` | `minKakeyaSize 6 3 = minKakeyaSize 2 3 * minKakeyaSize 3 3` |
| `minKakeyaSize_squarefree_dim_two` | for squarefree `N`: `minKakeyaSize N 2 = ∏ p ∈ N.primeFactors, minKakeyaSize p 2` |
| `minKakeyaSize_four_two` | `minKakeyaSize 4 2 = 10` (proper prime power, plane) |
| `minKakeyaSize_twelve_two` | `minKakeyaSize 12 2 = 70` |
| `minKakeyaSize_two_four'` | `minKakeyaSize 2 4 = 6` |
| `minKakeyaSize_two_mul_dim_four` | `minKakeyaSize (2M) 4 = 6 * minKakeyaSize M 4` for `M` coprime to 2 |

All theorem statements live in ordinary `Finset`/`ZMod` vocabulary; see
the files for precise hypotheses.

## Toolchain

- **Lean**: `leanprover/lean4:v4.32.0-rc1` (pinned in `lean-toolchain`)
- **Mathlib**: rev `360da6fa66c1273b76b6b2d8c5666fd5ac2e3b56` (pinned in
  `lakefile.toml`)

The tree was verified end-to-end with exactly this pin.

## How to run

```sh
lake exe cache get   # download prebuilt Mathlib (recommended)
lake build           # builds the whole tree; fails on any axiom deviation
```

Building `Kakeya` (the default target) builds the full verification
tree — every proof-authority file at the repository root (`artifact/`
is human-readable reference and is not imported). The axiom audit is a
checked assertion, not a report: each headline theorem's `#print
axioms` output is pinned with `#guard_msgs` to exactly
`[propext, Classical.choice, Quot.sound]`, and the build FAILS on any
deviation.

**Resource guidance.** The proofs contain large kernel-checked
enumerations (`decide +kernel`). Each file needs roughly **2–7 GB RAM**;
the whole tree is ~3 CPU-hours. Lake builds files in parallel, so cap
jobs to your RAM: with 16 GB, use `lake build -j2`; with 64 GB or more,
`-j8`+ finishes in well under an hour. Nothing here needs a big
machine — one file at a time works on a laptop.

## Layout

- `P01Base.lean` — carriers, encodings, Theorem 1 machinery (the
  index-world `Fin 27`/`Fin 16` encodings and their kernel bridges).
- `N00Core.lean`, `N27.lean`, `N16A.lean`, `N16B.lean` — the bitmask
  layer: windows are `Nat` bitmasks (membership = `Nat.testBit`), with
  structural bridge lemmas (`card_filter_eq_countP`,
  `testBit_maskOfList`, pointwise carrier equivalences) transporting
  every bitmask computation back to the original `Finset` statements.
  This representation is why the tree is cheap: the same enumerations
  stated over `Finset (Fin n)` cost 100+ GB in kernel memory (quotient
  term overhead); over `Nat` numerals they cost ~3 GB.
- `P02Cov.lean`, `P03E1.lean` … `P10E8.lean`, `N27A12R0..9.lean` — the
  𝔽₃³ coverage and endgame enumerations (Theorem 2's counting core).
- `P11Tail.lean` — Theorem 2 assembly: `minKakeyaSize_three_three`,
  `minKakeyaSize_six_three`, multiplicativity.
- `P12Schema.lean` — Theorem 3: the squarefree plane schema.
- `P13ABase.lean`, `P14AK00..P29AK15`, `P31AFc.lean` — the ℤ₄² cell:
  a 2¹⁶-mask certificate sweep in sixteen range slices plus a
  combiner, yielding `minKakeyaSize_four_two` and
  `minKakeyaSize_twelve_two`.
- `P32BBase.lean`, `P33BK00..P48BK15`, `P50BFc.lean` — the 𝔽₂⁴ cell,
  same shape, yielding `minKakeyaSize_two_four'` and the ×6 dimension-4
  law.
- `NFcExact.lean` — both-sides exactness of the small mod-2
  fractional-cost values (`FC(2,3,4)`, `¬FC(2,2,4)`, `¬FC(2,4,7)`
  joining the three halves already in the main development).
- `Kakeya.lean` — root target + build-failing axiom assertions
  (`#guard_msgs`-pinned `#print axioms` for every headline theorem).
- `artifact/` — the original single-file development
  (`KakeyaMultiplicativity.lean` plus the Theorem 3/4 bodies) from
  which the tree was cut. Same theorems, human-readable order; do not
  compile it as one file unless you have hundreds of GB of RAM — that
  is exactly the problem the split tree and the bitmask layer solve.
- `scripts/` — independent Python re-verifications of every
  enumeration the kernel checks (run with `python3 scripts/<name>.py`);
  these are sanity mirrors, not proof authority.

## License

[CC BY-NC-SA 4.0](https://creativecommons.org/licenses/by-nc-sa/4.0/)
(Attribution-NonCommercial-ShareAlike) — see `LICENSE`.

## Method note

Every combinatorial fact is proved by kernel-checked enumeration
(`decide +kernel`) over an explicitly encoded finite world, then
transported to the mathematical statement through small structural
lemmas. The kernel is the only checker in the trust chain: no compiled
native evaluator (`native_decide`) is used anywhere, and the axiom
audit at the end of the build enforces this mechanically.
