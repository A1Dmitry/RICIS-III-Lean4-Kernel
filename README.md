# RICIS-III Formal Kernel (v10.1.0)

MIT License | Lean 4 | DOI: 10.5281/zenodo.18116204

## Theory-faithful kernel (v7.7)

**Identity = SemanticType + Normalize(Expr)**

### Safety Protocols

| SP | Rule | In code |
|----|------|---------|
| SP2 | Clean first | `sp2_reduce` |
| SP3 | 0_F/0_G = F/G | identity check |
| SP4 | Index by expression | `Index.expr` |

### Axioms

- **A4**: `0_F/0_G = 1` iff same Identity, else `F/G`
- **A5**: same for ∞
- **A6**: `0_F × ∞_G = F·G`

### Theorem

```lean
theorem zero_div_same_identity (idx : Index) :
  singular_div (lazy_zero idx) (lazy_zero idx) = const 1
```

### Not any two zeros → 1

```lean
#reduce singular_div (lazy_zero z_{x-2}) (lazy_zero z_{x+2})
-- → expr (div (x-2) (x+2))
```

### Author

Dmitry Aleynikov · ORCID 0009-0004-3226-7700
