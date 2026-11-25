# Paper 8: Signed Weyl Resolvent Banks for Discrete Fourier Matrices: Small-Order Exactness and Linear Complexity

## Files
- `main.tex` — Submission-ready `amsart` LaTeX manuscript.
- `references.bib` — Clean BibTeX bibliography.
- `verify_weyl_resolvent_banks.py` — Standalone Python 3 (stdlib only) exact algebraic verifier checking: (1) the all-field order-3 4-bank construction (literally inverting all 12 branch matrices over $\mathbb{Q}(\zeta_3)$, $\mathbb{F}_4$, and $\mathbb{F}_7$); (2) the exact order-5 lower-bound elimination residues and 5-bank realization (literally inverting all 25 branch matrices over $\mathbb{Q}(\zeta_5)$); (3) the order-7 good-reduction B\'ezout certificate $U\overline{R}+V\overline{E}=1$ in $\mathbb{F}_{29}[Y]$ and the literal 8-bank cubic-algebra trace synthesis (verifying all 28 cubic-algebra $7\times 7$ branch inverses representing all 56 physical resolvents and all 49 entries of $F_7$); (4) the order-9 lower-bound certificate modulo $\Phi_9$ and the $\Theta(N)$ Fourier Hankel rank across odd $3\le N\le 19$; and (5) the first-order variable-coefficient envelope operator $L_x$ and deterministic reverse-GCD cubic coefficient generator over $\mathbb{F}_{47}$ ($N=23,d=4$), $\mathbb{F}_{71}$ ($N=35,d=6$), and characteristic-two $\mathbb{F}_{64}$ ($N=63,d=10$).
- `WeylResolventFourierBanks.lean` — Zero-dependency Lean 4 formal verifier (core `Init` only, verified in Lean 4.36.0 with zero `sorry`, zero custom axioms, and zero `native_decide`) symbolically proving the four-orientation exclusive-point and square-coverage lemmas for all odd $N\ge 3$, the $\Theta(N)$ Hankel bank-count bound, all range/margin inequalities for the $N\ge 6d-2$ ($5N/3 + O(1)$) theorem (including $H < (N+1)^2/2$), and the $2v-1$ telescoping trial bound for reverse GCD descent; plus pure-kernel verification of the exact $\mathbb{Z}[\zeta_5]$ lower/upper certificates, the $\mathbb{F}_{29}[Y]$ order-7 B\'ezout certificate, the $\mathbb{Z}[\zeta_9]$ order-9 lower-bound certificate, and the literal $\mathbb{F}_7$ 4-bank $3\times 3$ matrix synthesis of $F_3$.

## How to Compile PDF
1. Upload `main.tex` and `references.bib` to Overleaf (or compile locally with `latexmk -pdf main.tex`).

## Suggested Submission Metadata
- **arXiv primary / secondary:** `math.RA` (Rings and Algebras) / `cs.SC` (Symbolic Computation), `math.NT` (Number Theory)
- **MSC 2020:** Primary `15A23`, `15B05`; Secondary `65T50`, `11T06`, `13P15`
- **Target journals (zero-fee):** *Linear Algebra and its Applications*, *Journal of Symbolic Computation*, *Linear and Multilinear Algebra*.

## Verify Computations and Lean Proofs
```bash
python3 verify_weyl_resolvent_banks.py
lean WeylResolventFourierBanks.lean
```
