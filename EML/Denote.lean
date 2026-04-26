/-
Copyright (c) 2026 Loren Abdulezer / Evolving Technologies Corporation.
All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Loren Abdulezer
-/

-- SPEC.md §1.3 — Denotation `⟦·⟧ : EMLTree n → (Fin n → ℂ) → ℂ` built on the
-- operator `eml(x, y) = Complex.exp x - Complex.log y`.
-- Phase 1 will define the denotation function here.
import Mathlib
