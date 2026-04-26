# Mathlib v4.28.0 API Reconnaissance

**Phase:** 0 (scaffolding + reconnaissance — no proofs).
**Toolchain:** `leanprover/lean4:v4.28.0`, Mathlib pinned to `v4.28.0`
(`8f9d9cff6bd728b17a24e163c9402775d9e6a365`). Manifest revs match the
user's reference project (`lunar-interop`) byte-for-byte.

All `#check` outputs below were captured by running
`lake env lean EML/_scratch.lean` against the built scaffold. The scratch
file is gitignored and is deleted at the end of Phase 0.

In the captured signatures, Mathlib pretty-prints `Complex.exp` as `cexp`
and uses `↑` for the `Real → ℂ` coercion; everything is inside
`namespace Complex`, so unqualified `log` / `arg` / `I` mean the complex
versions.

---

## Group A — Phase 1 (denotation infrastructure)

### Item 1: `Complex.exp`

- **Name found:** `Complex.exp`
- **Statement:** `cexp : ℂ → ℂ`
- **Location:** `Mathlib/Analysis/SpecialFunctions/Complex/Circle.lean`
  (and the canonical entry point in `Mathlib/Data/Complex/Exponential.lean`)
- **Notes:** Total. No preconditions. The pretty-printer uses `cexp`.
- **Status:** ✓ Available.

### Item 2: `Complex.log` (+ totalization, arg range)

- **Name found:** `Complex.log`, `Complex.log_zero`, `Complex.arg_mem_Ioc`
- **Statements:**
  ```
  log : ℂ → ℂ
  log_zero : log 0 = 0
  arg_mem_Ioc : ∀ (z : ℂ), z.arg ∈ Set.Ioc (-Real.pi) Real.pi
  ```
- **Location:** `Mathlib/Analysis/SpecialFunctions/Complex/Log.lean`,
  `Mathlib/Analysis/SpecialFunctions/Complex/Arg.lean`
- **Notes:** Totalization at 0 matches our convention. The principal-branch
  interval `(-π, π]` matches SPEC §1.1 exactly (upper-edge convention).
- **Status:** ✓ Available, signature matches expectation.

### Item 3: `Complex.log_one`

- **Name found:** `Complex.log_one`
- **Statement:** `log_one : log 1 = 0`
- **Location:** `Mathlib/Analysis/SpecialFunctions/Complex/Log.lean:106`
- **Status:** ✓.

### Item 4: `Complex.exp_zero`

- **Name found:** `Complex.exp_zero`
- **Statement:** `exp_zero : cexp 0 = 1`
- **Location:** `Mathlib/Data/Complex/Exponential.lean`
- **Status:** ✓.

---

## Group B — Phase 2 (Lemmas 1–3)

### Item 5: `Complex.log_neg_one`

- **Name found:** `Complex.log_neg_one`
- **Statement:** `log_neg_one : log (-1) = ↑Real.pi * I`
- **Location:** `Mathlib/Analysis/SpecialFunctions/Complex/Log.lean:111`
- **Notes:** Matches SI convention. The coercion `↑Real.pi` is `(Real.pi : ℂ)`.
- **Status:** ✓.

### Item 6: `Complex.exp_log` (`exp ∘ log = id`)

- **Name found:** `Complex.exp_log`
- **Statement:** `@exp_log : ∀ {x : ℂ}, x ≠ 0 → cexp (log x) = x`
- **Location:** `Mathlib/Analysis/SpecialFunctions/Complex/Log.lean`
- **Notes:** Single precondition `x ≠ 0`. This is the form we want for
  Lemma 2(c) (universal property `exp(L x) = x` for real `x ≠ 0`).
- **Status:** ✓.

### Item 7: `Complex.log_exp` (`log ∘ exp = id` on the principal strip)

- **Name found:** `Complex.log_exp`
- **Statement:** `@log_exp : ∀ {x : ℂ}, -Real.pi < x.im → x.im ≤ Real.pi → log (cexp x) = x`
- **Location:** `Mathlib/Analysis/SpecialFunctions/Complex/Log.lean:54`
- **Notes:** ⚠ **Two separate hypotheses**, not a single conjunction nor
  `Set.Ioc`. Lemma 2 proofs will need to discharge `-π < x.im` and
  `x.im ≤ π` independently (trivial for real arguments since `im = 0`,
  and confirmed in Item 15 below via `linarith [Real.pi_pos]`).
- **Status:** ✓.

### Item 8: `Complex.exp_sub`

- **Name found:** `Complex.exp_sub`
- **Statement:** `exp_sub : ∀ (x y : ℂ), cexp (x - y) = cexp x / cexp y`
- **Status:** ✓.

### Item 9: `Complex.exp_add`

- **Name found:** `Complex.exp_add`
- **Statement:** `exp_add : ∀ (x y : ℂ), cexp (x + y) = cexp x * cexp y`
- **Status:** ✓.

### Item 10: `exp(2πi) = 1` family

- **Names found:** `Complex.exp_two_pi_mul_I`, `Complex.exp_int_mul_two_pi_mul_I`
- **Statements:**
  ```
  exp_two_pi_mul_I : cexp (2 * ↑Real.pi * I) = 1
  exp_int_mul_two_pi_mul_I : ∀ (n : ℤ), cexp (↑n * (2 * ↑Real.pi * I)) = 1
  ```
- **Location:** `Mathlib/Analysis/SpecialFunctions/Complex/Circle.lean`
  (and adjacent files)
- **Notes:** The integer-multiple form (`n = -1`) gives `exp(-2πi) = 1`
  directly, which is what we need for Lemma 2(b) (subtracting `2π i` to
  put `Log x` back on the principal branch on negative reals).
- **Status:** ✓ — both forms available.

### Item 11: ℝ → ℂ coercion lemmas

- **Names found:** `Complex.ofReal_neg`, `Complex.ofReal_log`,
  `Complex.log_re`, `Complex.log_im`, `Complex.log_ofReal_re`,
  `Complex.log_ofReal_mul`
- **Statements:**
  ```
  ofReal_neg       : ∀ (r : ℝ), ↑(-r) = -↑r
  @ofReal_log      : ∀ {x : ℝ}, 0 ≤ x → ↑(Real.log x) = log ↑x
  log_re           : ∀ (x : ℂ), (log x).re = Real.log ‖x‖
  log_im           : ∀ (x : ℂ), (log x).im = x.arg
  log_ofReal_re    : ∀ (x : ℝ), (log ↑x).re = Real.log x
  @log_ofReal_mul  : ∀ {r : ℝ}, 0 < r → ∀ {x : ℂ}, x ≠ 0 →
                       log (↑r * x) = ↑(Real.log r) + log x
  ```
- **Location:** `Mathlib/Analysis/SpecialFunctions/Complex/Log.lean`
- **Notes — gotchas worth flagging now:**
  1. `ofReal_log` is stated in the **`ofReal → log`** direction
     (`↑(Real.log x) = log ↑x`). For Lemma 2(a) we usually want the
     other direction; just use `.symm` or write the equation reversed.
  2. The precondition is `0 ≤ x`, not `0 < x`. (At `x = 0` both sides
     evaluate to 0.) On the strict-positive subset of Lemma 2(a) this is
     fine.
  3. **There is no single-step Mathlib lemma for
     `log (((-r : ℝ)) : ℂ) = Real.log r + π * I`** for arbitrary `r > 0`.
     Mathlib provides only the special case `log_neg_one`. The clean
     two-rewrite chain is `log_ofReal_mul` (with `x = -1`) followed by
     `log_neg_one` — verified working in Item 16 below. For Phase 2
     Lemma 2(b) we may want to wrap this as a small auxiliary lemma
     `Complex.log_ofReal_neg_of_pos` in `EML/Basic.lean` rather than
     inlining the chain at every use site. **Not a blocker.**
- **Status:** ✓ (all individual lemmas present; the composite identity
  for Lemma 2(b) is derivable in one tactic block).

---

## Group C — Phase 3 (Corollary 4 identities)

### Item 12: `Complex.exp_neg`

- **Name found:** `Complex.exp_neg`
- **Statement:** `exp_neg : ∀ (x : ℂ), cexp (-x) = (cexp x)⁻¹`
- **Status:** ✓.

### Item 13: `cpow` definition

- **Names found:** `Complex.cpow`, `Complex.cpow_def`, `Complex.cpow_def_of_ne_zero`
- **Statements:**
  ```
  cpow : ℂ → ℂ → ℂ
  cpow_def : ∀ (x y : ℂ),
    x ^ y = if x = 0 then if y = 0 then 1 else 0 else cexp (log x * y)
  @cpow_def_of_ne_zero : ∀ {x : ℂ}, x ≠ 0 → ∀ (y : ℂ), x ^ y = cexp (log x * y)
  ```
- **Notes:** For Corollary 4 / C12 (`x^y` reconstruction), prefer
  `cpow_def_of_ne_zero` once nonzeroness has been established — avoids the
  if-then-else of the totalized `cpow_def`. The `^` notation here is the
  `HPow ℂ ℂ ℂ` instance backed by `Complex.cpow`.
- **Status:** ✓ — both forms available.

### Item 14: complex square root

- **Name found:** `Complex.sqrt`
- **Definition:** `noncomputable def Complex.sqrt (a : ℂ) : ℂ := a ^ (2⁻¹ : ℂ)`
- **API printed:** `sqrt : ℂ → ℂ`, plus `sqrt_zero : sqrt 0 = 0`,
  `sqrt_one : sqrt 1 = 1`, and a `sqrt_eq_real_add_ite` describing the
  imaginary-part case split.
- **Location:** `Mathlib/Analysis/RCLike/Sqrt.lean` (note: under
  `RCLike/`, not `Complex/`; transitively reached by `import Mathlib`).
- **Notes:** Mathlib **does** provide a dedicated `Complex.sqrt` symbol —
  we should use it for C9 (`π` via `√(-L(-1)²)`) and C11 (`√x`) rather
  than rolling our own `cpow x (1/2)`. The definition is literally
  `a ^ (2⁻¹ : ℂ)`, so it's interchangeable with `cpow` in proofs but
  named distinctly for readability.
- **Status:** ✓.

---

## Group D — sanity checks

### Item 15: `log (exp 1) = 1`

- **Verified.** The following compiles cleanly in `EML/_scratch.lean`:
  ```lean
  example : Complex.log (Complex.exp (1 : ℂ)) = 1 :=
    Complex.log_exp
      (by simp; linarith [Real.pi_pos])
      (by simp; linarith [Real.pi_pos])
  ```
- **Recipe for Phase 2:** for any real argument `x : ℝ` we have
  `((x : ℂ).im = 0)`, so the two hypotheses of `log_exp` reduce to
  `-π < 0` and `0 ≤ π`, both discharged by `linarith [Real.pi_pos]`.
- **Status:** ✓.

### Item 16: `log((-2 : ℝ) : ℂ) = Real.log 2 + π i`

- **Verified.** The following compiles cleanly:
  ```lean
  example :
      Complex.log ((-2 : ℝ) : ℂ) = (Real.log 2 : ℂ) + Real.pi * Complex.I := by
    have step : ((-2 : ℝ) : ℂ) = ((2 : ℝ) : ℂ) * (-1 : ℂ) := by push_cast; ring
    rw [step,
        Complex.log_ofReal_mul
          (by norm_num : (0 : ℝ) < 2) (by norm_num : (-1 : ℂ) ≠ 0),
        Complex.log_neg_one]
  ```
- **Recipe for Phase 2 Lemma 2(b):** `log_ofReal_mul` peels off the
  positive-real factor, leaving `log (-1)` which evaluates to `π i`.
  Generalizing to `r > 0`:
  ```
  log (((-r : ℝ)) : ℂ) = Real.log r + π * I    -- for r > 0
  ```
  is a one-line consequence. We will likely encapsulate this as
  `EML/Basic.lean : Complex.log_ofReal_neg_of_pos`.
- **Status:** ✓.

### Bonus probes captured during recon

These are not in the brief but are useful enough to record now:

```
log_im          : ∀ (x : ℂ), (log x).im = x.arg
arg_ofReal_of_neg     : ∀ {x : ℝ}, x < 0 → (↑x).arg = Real.pi
arg_ofReal_of_nonneg  : ∀ {x : ℝ}, 0 ≤ x → (↑x).arg = 0
```

The `arg_ofReal_of_neg` lemma is an alternative route to Item 16 via
`log_re` + `log_im`, but the `log_ofReal_mul` chain shown above is shorter.

---

## Phase 0 Summary

1. **Did `lake build` succeed cleanly?** Yes — 8033 jobs, exit 0, zero
   errors, zero warnings. Mathlib `.olean`s came from the precompiled
   cache; no rebuild from scratch occurred.

2. **Are all Group A items confirmed available?** Yes (Items 1–4 ✓).
   Phase 1 is unblocked.

3. **Are all Group B items confirmed available?** Yes (Items 5–11 ✓ —
   every individual lemma we expected to use is present with the
   expected signature). Phase 2 is unblocked. The one wrinkle worth
   pre-flagging is the absence of a single-step lemma for log of a
   negative real coercion (see Item 11, note 3); this is a one-line
   derivation via `log_ofReal_mul` + `log_neg_one` and is best wrapped as
   an auxiliary in `EML/Basic.lean` during Phase 1.

4. **⚠ items.** None blocking. Two items deserve a heads-up at the start
   of Phase 1/2 but neither is a workaround:
   - **Item 7 (`Complex.log_exp`)** takes two hypotheses, not a `Set.Ioc`
     conjunction. Recipe in Item 15 above.
   - **Item 11 / Lemma 2(b) ingredient.** No direct
     `log((-r : ℝ) : ℂ) = log r + π i` lemma; derive once and reuse.
     Recipe in Item 16 above.

5. **Recommendation: ready to proceed to Phase 1.** Every Mathlib
   declaration we expect to use through Phase 3 is present and behaves
   as documented. The two minor stylistic notes above are absorbed by
   one small auxiliary lemma in Phase 1's `EML/Basic.lean`. Phases 2 and
   3 should not surprise us with missing API.

   **Out-of-scope for Phase 0** but worth recording for later phases:
   the SPEC §8 open issues (negation witness, multiplication domain,
   sinh's alternative witness) are mathematical-design questions
   independent of Mathlib API completeness, and remain open.

---

*Generated at the end of Phase 0; the underlying probes live in
`EML/_scratch.lean` while that file exists, and were re-run at the end
of Phase 0 cleanup to confirm reproducibility.*
