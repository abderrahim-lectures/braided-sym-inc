# Braided-Symmetric Derivations of Incidence Algebras

Author: Abderrahim Adrabi, Mohammed V University in Rabat.  
Current version: **v2**.

## The idea of the paper

Let A be the incidence algebra of a finite partially ordered set X (a poset) over a commutative ring K in which 2 is invertible. Let be an order automorphism of X with ^2 = id, and let be the automorphism of A that induces. We twist the Jordan product of A by , and we call a linear map that satisfies the Leibniz rule for this product a braided-symmetric derivation. We prove that a braided-symmetric derivation that commutes with is a derivation. For = id this is the known theorem that Jordan derivations of incidence algebras are derivations. We show that the hypothesis on 2 is needed, and we list computed dimensions for small posets.

### Contents

1. Introduction
2. Preliminaries
3. Proof of the theorem
4. Examples and sharpness

## Repository layout

| Path | Content |
|---|---|
| `paper/braided-sym-inc.tex` | LaTeX source (class files in `cls/`) |
| `pdf/` | the PDF of the latest release |
| `lean/Research/BraidedSymInc/` | Lean 4 files that check computations and lemmas of the paper (mathlib only) |

Build the paper with `cd paper && latexmk -pdf braided-sym-inc.tex`. Build the Lean files with `cd lean && lake build`.

## Change log

One entry per released version, newest first. Each version is also a tag of this repository.

- **v2** (2026-10-16): Xiao Theorem 3.3 is stated before use. No claim changes.
- **v1** (2026-10-14): initial draft from the proof found for lead #813.

## References

Citations of the works the paper uses. The works themselves are not part of this repository.

1. A. Adrabi, Braided-symmetric derivations of algebras, preprint, Mohammed V University in Rabat, 2026.
2. É. Z. Fornaroli and M. Khrypchenko, Skew derivations of incidence algebras, Collect. Math. (2023), doi:10.1007/s13348-023-00423-7.
3. H. Jia and Z. Xiao, Jordan skew derivations of incidence algebras, Bull. Malays. Math. Sci. Soc. (2025), doi:10.1007/s40840-025-01960-z.
4. Z. Xiao, Jordan derivations of incidence algebras, Rocky Mountain J. Math. 45 (2015), no. 4, 1357–1368.
5. Y. Yang, Nonlinear Jordan derivations of incidence algebras, Comm. Algebra (2021), doi:10.1080/00927872.2021.1890106.
6. L. Yang, Jordan *-derivations of incidence algebras, arXiv:2507.13751 (2025).
7. X. Zhang and M. Khrypchenko, Lie derivations of incidence algebras, Linear Algebra Appl. 513 (2017), 69–83.

## About this repository

The repository is updated after every release of the paper. The research workspace that produced it is private; the final source, PDF and Lean code are published here.
