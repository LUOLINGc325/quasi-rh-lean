# quasi-rh-lean

A Lean 4 formalization of the main results of the manuscript
**"The Quasi-Riemann Hypothesis"** (OpenAI Math Release preprint, author: OpenAI, October 5, 2026),
relying only on the standard axioms (`propext`, `Classical.choice`, `Quot.sound`).

[![build](https://github.com/LUOLINGc325/quasi-rh-lean/actions/workflows/build.yml/badge.svg)](https://github.com/LUOLINGc325/quasi-rh-lean/actions/workflows/build.yml)
Reproduce: see [`.github/workflows/build.yml`](.github/workflows/build.yml).

> **Attribution.** The mathematics (theorem and proof) is the work of the manuscript's author, OpenAI:
> [PDF](https://github.com/openai/math/blob/main/preprints/The-Quasi-Riemann-Hypothesis-October-5-2026/paper2.pdf),
> TeX source in [`source-material/`](source-material/preprints). This repository is an *independent* Lean 4
> formalization of that manuscript's main results, carried out by the repository owner (LUOLINGc325) with
> AI coding agents. It is not an official OpenAI artifact and is not affiliated with or endorsed by OpenAI.

## What is formalized

The manuscript proves that every finite-order Hecke L-function over K = Q(sqrt(-3)), and hence every Dirichlet
L-function including the Riemann zeta function, has no zeros in the half-plane Re s > 11/12, and derives a
prime number theorem in arithmetic progressions with error O(x^(11/12) log x).

| Lean name | Statement | Manuscript |
|---|---|---|
| `QRHShort.Manuscript.main` | `QRHShort.MainStatement` | Theorem `thm:main` |
| `QRHShort.Manuscript.primes_ap` | `QRHShort.PrimeAPStatement` | Corollary `cor:primes-ap` |

The statements are in [`stage3/QRHShort/MainStatements.lean`](stage3/QRHShort/MainStatements.lean); the proofs are
assembled in [`stage3/QRHShort/Manuscript.lean`](stage3/QRHShort/Manuscript.lean) (proof root `QRHShort.Manuscript`).
Abridged:

```lean
def HeckeZeroFreeStatement : Prop :=
  ∀ (χ : HeckeCharacter) (s : ℂ), (11 : ℝ) / 12 < s.re →
    (s ≠ 1 ∨ χ.residue ≠ 1) → HeckeL χ s ≠ 0

def DirichletZeroFreeStatement : Prop :=
  ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N) (s : ℂ),
    (11 : ℝ) / 12 < s.re → (s ≠ 1 ∨ χ ≠ 1) → DirichletCharacter.LFunction χ s ≠ 0

def MainStatement : Prop := HeckeZeroFreeStatement ∧ DirichletZeroFreeStatement

def PrimeAPStatement : Prop :=
  ∃ C : ℕ, ∀ (x : ℝ) (q a : ℕ), 2 ≤ x → 1 ≤ q → (q : ℝ) ≤ x → Nat.Coprime a q →
    |(primeAPCount x q a : ℝ) - (Nat.totient q : ℝ)⁻¹ * ∫ t in (2 : ℝ)..x, (Real.log t)⁻¹|
      ≤ (C : ℝ) * x ^ ((11 : ℝ) / 12) * Real.log x
```

Reading notes (the Lean kernel certifies that the proofs prove *these* statements; whether the definitions
match the manuscript is for the reader to judge):
- `HeckeCharacter` (`stage3/QRHShort/Arithmetic.lean`) is a ray character of `K = CyclotomicField 3 ℚ`
  modulo a nonzero ideal, trivial on units; imprimitive characters are allowed.
- `HeckeL χ` (`stage3/QRHShort/External.lean`) is a *chosen* function satisfying `HeckeContinuationSpec χ`
  (agrees with the ideal Dirichlet series for Re s > 1 and is analytic away from the possible pole at s = 1).
  By the identity theorem such a function is unique on that set, but uniqueness is not part of the stated theorem.
- Dirichlet L-functions are Mathlib's `DirichletCharacter.LFunction`, for every modulus and every character.
- The file name `External.lean` is historical: earlier iterations assumed three literature results (Hecke's
  analytic continuation, a Landau-type dyadic prime-ideal bound, a Goldmakher-Louvel quadratic-sieve bound) as
  axioms. In this release all three are proved and the project declares no axioms of its own; the comments
  in some files that still speak of "external inputs" are outdated.

**Not formalized.** (i) The manuscript's claim that the implied constants are effectively computable:
`PrimeAPStatement` only asserts that a constant `C` exists. (ii) The further consequences discussed in the
manuscript's introduction (least quadratic nonresidue, Miller's test, class-number bounds, idoneal numbers).

## Verification

Results of a final acceptance run (GitHub Actions, run 40679418949 in a private CI repository; its harness is not
shipped here) on commit `7b408ba34991db117776ad32bedbc745d4b8e430` of the development repository. This repository
contains that tree, minus the machine-specific build files of `stage3/` and plus `README.md`, `LICENSE`, `NOTICE`,
`build/`, `.github/` and `upstream/OAI/LICENSE`. Toolchain `leanprover/lean4:v4.34.1`, Mathlib
`d13f23b723b8a846827a245b89c10fc7d3f11612`. All acceptance criteria passed, except that the frozen-statement
checker flagged one difference: `hecke_continuation` changed from an axiom to a theorem with an identical type, which
is the intended removal of an external axiom.

| Check | Result |
|---|---|
| Clean `lake build` of all project modules | PASS: exit 0, no module without `.olean`, 0 `sorry` warnings (about 52 min on a hosted runner, Mathlib cache) |
| Axioms of the main theorems | PASS: `main` and `primes_ap` depend only on `propext`, `Classical.choice`, `Quot.sound`. Audit of the 646 proof-closure modules (27,182 theorems): 0 `sorry`, 0 axioms declared in the project |
| Kernel replay of the proof closure | PASS: 646 modules, 0 failures (20 re-checked in this run; 626 reused from an earlier run of the same harness: same toolchain and Mathlib, source and import closure unchanged) |
| Frozen statement file | `MainStatements.lean` byte-identical to the baseline |
| Frozen statement cone (26 constants) | One difference, as above: `QRHShort.hecke_continuation`, `axiom` to `theorem`, identical type (the checker flags any change of declaration kind) |
| Source text scan | PASS: 0 blocking hits |
| Dependency lock / vendored sources | PASS (2 warnings: the two adapted third-party copies below, covered by the kernel audit and replay) |

To reproduce the axiom check (after building, from `build/`; expected: exactly the three standard axioms for each
theorem), run `lake env lean PrintAxioms.lean`. The workflow `.github/workflows/build.yml` does this on every push:
it builds `QRHShort.Manuscript`, fails on any `declaration uses 'sorry'` in the build log, and fails unless the
`#print axioms` output of `main`, `primes_ap` and `hecke_continuation` lists only the three standard axioms.

## Building

Needs [elan](https://github.com/leanprover/elan), `git`, `curl` and a C compiler. Lake and Lean v4.34.1 are
fetched automatically; Mathlib is fetched from its pinned revision. `build/` is the single build entry.

```
git clone https://github.com/LUOLINGc325/quasi-rh-lean && cd quasi-rh-lean/build
lake exe cache get                 # prebuilt Mathlib artifacts
lake build QRHShort.Manuscript     # builds the whole proof closure
lake env lean PrintAxioms.lean     # axiom audit of the main theorems
```

`build/` is a small Lake package that exposes the source directories of this repository as libraries (`QRH`,
`QRHShort`, `QRHLean3`, `OAI`, `RellichKondrachov`, `PrimeNumberTheoremAnd`), laid out like the acceptance harness.
Do not run `lake build` there without a target: the three third-party libraries have no root module file.

## Layout

| Path | Contents |
|---|---|
| `stage3/QRHShort/` | Main development (about 290 files): statements, estimates, assembly; proof root `Manuscript.lean` |
| `stage3/QRHLean3/`, `QRH/` | Smaller supporting libraries imported by the main development (`stage3/CheckAxioms.lean` is a development-time audit script, not used by the build) |
| `upstream/OAI/` | Part of the Lean library of OpenAI's [openai/math](https://github.com/openai/math) release (327 files, unmodified) plus one project-written file, `NumberTheory/DirichletL/PrimeCounting/LandauAnnularBridge.lean`. The release's own main theorems (e.g. the 7/8 results) are not used |
| `upstream/RellichKondrachov/` | Adapted copy of [abenenson/rellich-kondrachov](https://github.com/abenenson/rellich-kondrachov) @ `70f85d4c` (15 files, 11 adapted) |
| `upstream/PrimeNumberTheoremAnd/` | Adapted subset of [PrimeNumberTheoremAnd](https://github.com/AlexKontorovich/PrimeNumberTheoremAnd) @ `c39a751` (6 files; blueprint attributes removed; four unused declarations, two of them `sorry` upstream, removed from `Wiener.lean`) |
| `source-material/preprints/` | TeX sources of the OpenAI manuscripts (Oct 5, 2026: 11/12; Sep 30, 2026: 7/8) |
| `build/` | Lake package for building, and `PrintAxioms.lean` (above) |
| `.github/workflows/build.yml` | CI: build, no-`sorry` check, axiom audit |

## Licenses

Apache License 2.0 (see `LICENSE`); third-party components keep their own Apache-2.0 licenses and notices, see
`NOTICE` (including the list of modified files). The Lean code was produced with substantial AI assistance; treat
the kernel-checked statements above, not the commentary in source files, as the authoritative content.
