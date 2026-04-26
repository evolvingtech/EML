/-
Copyright (c) 2026 Loren Abdulezer / Evolving Technologies Corporation.
All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Loren Abdulezer
-/

-- SPEC.md §1.3 — Basic auxiliary lemmas. Two of these patch small gaps in
-- Mathlib's principal-branch API surface (see `docs/MATHLIB_RECON.md`); the
-- third is a sanity check on the EML operator.
import Mathlib
import EML.Denote

/-- For `r > 0` real, `log` of the negative-real coercion `((-r : ℝ) : ℂ)`
equals `Real.log r + π * I`. The two-step proof uses `Complex.log_ofReal_mul`
to peel off the positive-real factor, leaving `Complex.log (-1) = π * I`.
Required for Lemma 2(b). -/
theorem Complex.log_ofReal_neg_of_pos {r : ℝ} (hr : 0 < r) :
    Complex.log ((-r : ℝ) : ℂ) = (Real.log r : ℂ) + Real.pi * Complex.I := by
  have step : ((-r : ℝ) : ℂ) = ((r : ℝ) : ℂ) * (-1 : ℂ) := by push_cast; ring
  rw [step,
      Complex.log_ofReal_mul hr (by norm_num : (-1 : ℂ) ≠ 0),
      Complex.log_neg_one]

/-- For real `x`, `Complex.log (Complex.exp ((x : ℝ) : ℂ)) = ((x : ℝ) : ℂ)`.
The principal-strip hypotheses of `Complex.log_exp` discharge automatically
because the imaginary part of a real coercion is zero. Required for
Lemma 2(a). -/
theorem Complex.log_exp_real (x : ℝ) :
    Complex.log (Complex.exp ((x : ℝ) : ℂ)) = ((x : ℝ) : ℂ) :=
  Complex.log_exp
    (by simp; linarith [Real.pi_pos])
    (by simp; linarith [Real.pi_pos])

/-- `eml(1, 1) = e`. Sanity check on the operator's behavior on the
simplest non-trivial inputs; also the SI's "step 1" witness for `e`. -/
theorem eml_one_one : eml 1 1 = Complex.exp 1 := by
  unfold eml
  simp [Complex.log_one]
