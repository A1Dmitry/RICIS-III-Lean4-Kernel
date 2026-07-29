RICIS-III Formal Kernel (v10.0.1)
==================================

MIT License | Lean 4 | DOI: 10.5281/zenodo.18116204


OVERVIEW
════════

This repository contains the machine-verified formal kernel of RICIS-III
(Recursive Indexed Calculus of Identity and Singularity), implemented in Lean 4.

RICIS-III provides an alternative constructive mathematical framework using
indexed infinities (∞_F) and typed zeros (0_F), replacing classical limits
with structural monolith matching at O(1).


CORE ARCHITECTURE
═════════════════

COMPONENT              DESCRIPTION
─────────────────────  ──────────────────────────────────────────────────
L0, L1                 Absolute Continuity & Identity (X = X)
SP1–SP4                Safety Protocols preventing logical paradoxes
A1–A10                 Core axioms for typed zeros and infinities
Expr                   AST (const, var, add, mul, sub, div)
Index                  Semantic context {expr, name}
Monolith               Unified type: const | expr e | lazy_zero idx | lazy_inf idx
sp2_reduce             Structural cancellation before evaluation
sp4_index              Semantic indexing at point
ricis_mul              A6: 0_F × ∞_G = F·G
ricis_div              A4/A5: 0_F/0_G = F/G, ∞_F/∞_G = F/G
ricis_sub              A7: ∞_F - ∞_G = ∞_{F-G}


VERIFIED THEOREM
════════════════

theorem ricis_zero_div_self_identity (idx : Index) : 
  ricis_div (lazy_zero idx) (lazy_zero idx) = const 1 := by
  unfold ricis_div; unfold sp2_reduce; simp

Meaning: 0_F / 0_F = 1 — proven structurally, without limits,
without L'Hôpital, without series.


GETTING STARTED
═══════════════

Prerequisites: Install Lean 4 via elan

  curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh

Build & Verify:

  git clone https://github.com/A1Dmitry/RICIS-III-Lean4-Kernel.git
  cd RICIS-III-Lean4-Kernel
  lean --make Ricis3.Release.lean

All 7 tests pass. Theorem compiles successfully.


REPOSITORY STRUCTURE
════════════════════

  RICIS-III-Lean4-Kernel/
  ├── Ricis3.Release.lean                    (278 lines, full kernel v10.0.1)
  ├── ricis_zero_div_self_identity.lean      (standalone theorem)
  ├── README.md
  └── LICENSE


REFERENCES
══════════

  RICIS-III Kernel (this repo)    10.5281/zenodo.18116204
  RICIS-III Theory                10.5281/zenodo.21517353
  RICIS Software                  10.5281/zenodo.21529989

  Author:  Dmitry Aleynikov
  ORCID:   0009-0004-3226-7700
  Online:  https://remix-ricis-iii-501343051156.europe-west2.run.app


LICENSE
═══════

MIT License. See LICENSE file for details.
