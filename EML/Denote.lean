/-
Copyright (c) 2026 Loren Abdulezer / Evolving Technologies Corporation.
All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Loren Abdulezer
-/

-- SPEC.md §1.3 — Denotation `⟦·⟧ : EMLTree n → (Fin n → ℂ) → ℂ` built on the
-- operator `eml(x, y) = Complex.exp x - Complex.log y`.
import Mathlib
import EML.Syntax

/-- The EML operator on complex numbers: `eml(x, y) = exp(x) - log(y)`,
using Mathlib's principal-branch `Complex.log` (which totalizes `log 0 = 0`).
This is the operator that Lemmas 1–3 in Phase 2 will reason about. It is
`noncomputable` because `Complex.log` is. -/
noncomputable def eml (x y : ℂ) : ℂ :=
  Complex.exp x - Complex.log y

/-- Denotation of an EML tree under a variable assignment. Per SPEC §1.3:
`⟦1⟧ = 1`, `⟦xᵢ⟧ = env i`, `⟦eml(l, r)⟧ = eml ⟦l⟧ ⟦r⟧`. -/
noncomputable def denote {n : ℕ} (env : Fin n → ℂ) : EMLTree n → ℂ
  | EMLTree.one => 1
  | EMLTree.var i => env i
  | EMLTree.node l r => eml (denote env l) (denote env r)

@[simp] theorem denote_one {n : ℕ} (env : Fin n → ℂ) :
    denote env (EMLTree.one : EMLTree n) = 1 := rfl

@[simp] theorem denote_var {n : ℕ} (env : Fin n → ℂ) (i : Fin n) :
    denote env (EMLTree.var i) = env i := rfl

@[simp] theorem denote_node {n : ℕ} (env : Fin n → ℂ) (l r : EMLTree n) :
    denote env (EMLTree.node l r) = eml (denote env l) (denote env r) := rfl
