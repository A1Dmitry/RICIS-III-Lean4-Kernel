# RICIS-III Formal Kernel (v10.2.0)

MIT | Lean 4 | DOI 10.5281/zenodo.18116204
https://doi.org/10.5281/zenodo.18116204
https://doi.org/10.5281/zenodo.21701242

**Identity = SemanticType + Normalize(Expr)** · no classical limits

## From Ricis.Core (C#)

| C# | Lean |
|----|------|
| ExpressionSimplifierVisitor | `algSimplify` |
| AlgebraicReductionVisitor | `sp2_reduce` + nested cancel |
| ShouldCommute | `normalizeExpr` sorted ADD/MUL |
| StandardOperations inf | `ricis_add` / `ricis_sub` (A7) |
| 0_F x inf_G | `ricis_mul` (A6) |
| inf/inf = F/G | `singular_div` (A5) |

## Axioms

- A4: 0_F/0_G = 1 iff same Identity, else F/G
- A5: same for inf
- A6: 0_F × ∞_G = F·G
- A7: ∞_F ± ∞_G = ∞_{F±G}

## Theorem

`zero_div_same_identity` — singular_div (lazy_zero idx) (lazy_zero idx) = const 1

## Author

Dmitry Aleynikov · ORCID 0009-0004-3226-7700
