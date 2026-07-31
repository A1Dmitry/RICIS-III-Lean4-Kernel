# RICIS-III Formal Kernel (v10.2.0)

**MIT** · **Lean 4** · **DOI 10.5281/zenodo.18116204**

[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.18116204.svg)](https://doi.org/10.5281/zenodo.18116204)
[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.21701242.svg)](https://doi.org/10.5281/zenodo.21701242)

---

# RICIS-III Formal Kernel

Formalization of the **Recursive Indexed Calculus of Identity and Singularity (RICIS-III)** in **Lean 4**.

The project provides a machine-checked implementation of the RICIS axiomatic system together with formally verified theorems derived from those axioms.

Unlike classical analysis, RICIS evaluates singular expressions symbolically using semantic identities instead of limit computations.

---

# Key Features

• Identity = SemanticType + Normalize(Expression)

• No classical limits

• Machine-checked proofs in Lean 4

• Formal implementation of RICIS axioms:

  • A4 — 0_F / 0_G

  • A5 — ∞_F / ∞_G

  • A6 — 0_F × ∞_G

  • A7 — ∞_F ± ∞_G

• SP1–SP4 Safety Protocols

• TypeConsistencyProtocol

• Recursive Fractal Law

• Constant-time symbolic evaluation of singular forms

---

# Safety Protocols

### SP1 — No Total Amnesia

Information contained in singularities is preserved.

### SP2 — Algebraic Reduction First

Expressions are simplified before singularity evaluation.

### SP3 — Index Law

0_F / 0_G = F / G

unless both semantic identities are identical.

### SP4 — Semantic Identity

Identity depends on

SemanticType + Normalize(Expression)

instead of numerical value.

---

# RICIS Axioms

### A4 — Zero Division

0_F / 0_G =

• 1  if Identity(F) = Identity(G)

• F / G otherwise

---

### A5 — Infinity Division

∞_F / ∞_G =

• 1  if Identity(F) = Identity(G)

• F / G otherwise

---

### A6 — Zero–Infinity Multiplication

0_F × ∞_G = F · G

---

### A7 — Infinity Arithmetic

∞_F ± ∞_G = ∞_(F ± G)

---

# Recursive Fractal Law

R(Q) =

{
    Q,
    T(Q),
    ∞_Q,
    0_Q,
    R(∞_Q),
    R(0_Q)
}

Recursive closure of semantic objects under singularity generation.

---

# Architecture

```
           Parser
              │
              ▼
      Expression Tree
              │
              ▼
     Algebraic Reduction
          (SP2)
              │
              ▼
   Semantic Normalization
              │
              ▼
     Identity Construction
              │
              ▼
      SP1 • SP3 • SP4
              │
              ▼
      RICIS Axioms
      (A4–A7)
              │
              ▼
      Lean Proof Kernel
```

---

# Mapping from Ricis.Core (C#)

| Ricis.Core | Lean 4 |
|------------|---------|
| ExpressionSimplifierVisitor | `algSimplify` |
| AlgebraicReductionVisitor | `sp2_reduce` |
| ShouldCommute | `normalizeExpr` |
| StandardOperations (∞ ± ∞) | `ricis_add` / `ricis_sub` |
| 0_F × ∞_G | `ricis_mul` |
| ∞_F / ∞_G | `singular_div` |

---

# Example Verified Theorem

```lean
theorem zero_div_same_identity :
  singular_div (lazy_zero idx) (lazy_zero idx) = const 1
```

This theorem is mechanically verified by the Lean 4 proof kernel.

---

# Build

```bash
lake update
lake build
```

---

# Project Information

**Language**

Lean 4

**License**

MIT

**Author**

Dmitry Aleynikov

**ORCID**

https://orcid.org/0009-0004-3226-7700

**Primary DOI**

https://doi.org/10.5281/zenodo.18116204

**Formal Kernel DOI**

https://doi.org/10.5281/zenodo.21701242

---

# Keywords

RICIS

Formal Verification

Lean 4

Theorem Proving

Calculus

Singularity

Semantic Identity

Formal Kernel

Type Theory

Recursive Calculus

Indexed Zero

Indexed Infinity

Machine-Checked Mathematics

---

# Related Resources

• Zenodo DOI

https://doi.org/10.5281/zenodo.18116204

• Formal Kernel DOI

https://doi.org/10.5281/zenodo.21701242

• ORCID

https://orcid.org/0009-0004-3226-7700

• GitHub Repository

https://github.com/A1Dmitry/RICIS-III-Lean4-Kernel

---

# Status

Current release: **v10.2.0**

The implementation is intended to formalize the RICIS-III axiomatic system in Lean 4 and to provide machine-checked proofs derived from those axioms.

---

© 2026 Dmitry Aleynikov

Released under the MIT License.
