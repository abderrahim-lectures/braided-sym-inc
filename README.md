# A Note on Twisted Jordan Derivations of Incidence Algebras

Author: Abderrahim Adrabi, Mohammed V University in Rabat.  
Current version: **v5**.

## The idea of the paper

Let A be the incidence algebra of a finite partially ordered set X (a poset) over a commutative ring K in which 2 is invertible. Let be an order automorphism of X with ^2 = id, and let be the automorphism of A that induces. We twist the Jordan product of A by , and we call a linear map that satisfies the Leibniz rule for this product a braided-symmetric derivation. We prove that the braided-symmetric derivations are exactly the derivations that commute with . The commuting condition is not an assumption, because every braided-symmetric derivation satisfies it. For = id this is the known theorem that Jordan derivations of incidence algebras are derivations. We show that the hypothesis on 2 is needed, and we list computed dimensions for small posets.

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

- **v5** (2026-10-17): referee report (pasted by the owner) observed that the commuting condition of Theorem 1.1 is redundant; checked by hand and in Lean (Criterion.lean: bs_map_one, bs_comm; Theorem.lean: braided_iff_derivation_comm). Every braided-symmetric derivation kills the unit and commutes with alpha, so BSDer(A,alpha) = Der(A)^alpha. New claims: Lemma lem:commute and the stronger Theorem 1.1.
- **v4** (2026-10-17): the paper is presented as a short note with the title "A Note on Twisted Jordan Derivations of Incidence Algebras" (the earlier title was "Braided-Symmetric Derivations of Incidence Algebras"), after a novelty check showed the result is a twisted analogue of Xiao 2015 Theorem 3.3, with the extra hypotheses that D commutes with alpha and 2 is invertible; the Step 1 heading of the proof is removed. No claim changes.
- **v3** (2026-10-16): Xiao's Theorem 3.3 is stated as the source gives it, with its standing hypothesis on X before it, and the incidence algebra is credited to Xiao. No result changes; two attributions are added.
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
