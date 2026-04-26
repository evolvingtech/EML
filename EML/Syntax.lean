/-
Copyright (c) 2026 Loren Abdulezer / Evolving Technologies Corporation.
All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Loren Abdulezer
-/

-- SPEC.md §1.2 — EMLTree grammar (full binary trees with leaves `1` and `xᵢ`).
import Mathlib

/-- Abstract syntax of EML expressions over `n` variable slots.

`EMLTree n` is a full binary tree whose leaves are either the constant `1` or
one of the variables `x₀, …, x_{n-1}` (encoded by `Fin n`), and whose internal
nodes are the binary EML operator. This is pure syntax — semantic content
(the `eml` operator and the denotation `⟦·⟧`) lives in `EML.Denote`. -/
inductive EMLTree (n : ℕ) : Type where
  /-- The constant terminal `1`. -/
  | one : EMLTree n
  /-- The `i`-th variable slot (with `i : Fin n`). -/
  | var : Fin n → EMLTree n
  /-- Binary application: `eml(l, r)`. -/
  | node : EMLTree n → EMLTree n → EMLTree n
  deriving DecidableEq
