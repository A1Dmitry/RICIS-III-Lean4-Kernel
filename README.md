# RICIS-III Formal Kernel (v10.0.13)

MIT License | Lean 4 | DOI: 10.5281/zenodo.18116204

## OVERVIEW

Machine-verified formal kernel of RICIS-III
(Recursive Indexed Calculus of Identity and Singularity) in Lean 4.

**Identity = SemanticType + Normalize(Expr)**

## CORE (v10.0.13)

| Component | Description |
|-----------|-------------|
| Expr | AST (const, var, add, mul, sub, div) |
| SemanticType | arithmetic \| field \| geometry \| topology \| singularity |
| Identity | hash + canonical (normalizeExpr) |
| InstanceCounter / RICISState | instance IDs |
| Index | identity, instanceId, expr, name, semanticType |
| Monolith | const, expr, expr_idx, value_idx, value_expr_idx, lazy_zero, lazy_inf, unresolved |
| ricis_div / ricis_mul | classical_div + singular_div |
| evalAll | Classical \| RICIS modes |

## KEY PROPERTY

Same semantic identity (hash) can have different instanceIds:

```lean
#reduce idx1.identity.hash = idx2.identity.hash  -- true
#reduce idx1.instanceId = idx2.instanceId        -- false
```

## TESTS

```lean
#reduce ricis_div (const 5) (const 0)
#reduce ricis_div (lazy_zero ...) (lazy_zero ...)  -- → const 1
```

## Build

```bash
git clone https://github.com/A1Dmitry/RICIS-III-Lean4-Kernel.git
cd RICIS-III-Lean4-Kernel
lean --make Ricis3.Release.lean
```

## Author

Dmitry Aleynikov  
ORCID: 0009-0004-3226-7700  
DOI: 10.5281/zenodo.18116204  
License: MIT
