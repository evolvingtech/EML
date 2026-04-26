/-
Copyright (c) 2026 Loren Abdulezer / Evolving Technologies Corporation.
All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Loren Abdulezer
-/

-- SPEC.md §2, Lemma 2 — Reconstructed logarithm on the real axis.
-- Define `L(x) := eml(1, exp(eml(1, x)))` and prove:
--   (a) on `x > 0`, `L x = Real.log x`;
--   (b) on `x < 0`, `L x = Complex.log x - 2π i`;
--   (c) universal property: `Complex.exp (L x) = x` for real `x ≠ 0`.
-- Proof lands in Phase 2.
import Mathlib
