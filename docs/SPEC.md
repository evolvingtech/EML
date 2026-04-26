# EML Formalization Specification

**Source paper:** Andrzej Odrzywołek, *"All elementary functions from a single operator,"* arXiv:2603.21852v2 (March 2026), with full technical details in the Supplementary Information PDF.

**Purpose of this document:** This is the canonical specification that the Lean 4 / Mathlib formalization targets. Every theorem, lemma, identity, and domain condition in the formal development should correspond to a numbered item in this document. When the paper and this document disagree, the paper wins — file an issue and update the SPEC.

This document is the *interface* between the mathematical content of the paper and the Lean code. Phase plans, prompts to Claude Code, and Lean files all reference SPEC sections by number.

---

## 1. The EML operator and its grammar

### 1.1 The operator

Define the binary operator on $\mathbb{C}$:
$$
\mathrm{eml}(x, y) \;:=\; \exp(x) - \mathrm{Log}(y)
$$
where:

- $\exp$ is the complex exponential, entire on $\mathbb{C}$.
- $\mathrm{Log}$ is the **principal branch** of the complex logarithm, analytic on $\mathbb{C} \setminus (-\infty, 0]$, with $\mathrm{Arg}(z) \in (-\pi, \pi]$. On the negative real axis, $\mathrm{Log}$ takes the upper-edge limit: $\mathrm{Log}(-r) = \log r + i\pi$ for $r > 0$. In particular $\mathrm{Log}(-1) = i\pi$.

**Mathlib correspondence:** Mathlib's `Complex.log` uses exactly this branch convention. In particular, `Complex.log_neg_one : Complex.log (-1) = π * I`. No convention translation is needed.

The operator is partial (in $y$): $\mathrm{eml}(x, 0)$ is undefined. Mathlib's `Complex.log 0 = 0` totalization should be acknowledged but not relied on for any theorem statement; theorems with $L$ in them carry an explicit $x \neq 0$ hypothesis.

### 1.2 The grammar

For a finite set of variables $X = \{x_1, \ldots, x_n\}$, define $T_{\mathrm{EML}}(X)$ inductively:
$$
T \;::=\; 1 \;\mid\; x_1 \;\mid\; \cdots \;\mid\; x_n \;\mid\; \mathrm{eml}(T, T)
$$

Every term determines a partial complex-valued map; its domain is the set of points where every subexpression is defined.

**Lean encoding (target):**
```lean
inductive EMLTree (n : Nat) where
  | one  : EMLTree n
  | var  : Fin n → EMLTree n
  | node : EMLTree n → EMLTree n → EMLTree n
```
The closed-form (variable-free) case `EMLTree 0` is the substrate for constants like $e, -1, \pi, i$.

### 1.3 Denotation

Given an environment $\sigma : \mathrm{Fin}\,n \to \mathbb{C}$, the denotation $\llbracket T \rrbracket_\sigma$ is defined recursively:
$$
\llbracket 1 \rrbracket_\sigma = 1, \qquad
\llbracket x_i \rrbracket_\sigma = \sigma(i), \qquad
\llbracket \mathrm{eml}(a,b) \rrbracket_\sigma = \exp(\llbracket a \rrbracket_\sigma) - \mathrm{Log}(\llbracket b \rrbracket_\sigma).
$$

In Lean this is `noncomputable` (because `Complex.log` is).

---

## 2. Core reconstructions (Lemmas 1–3 + Corollary 4)

This is the centerpiece of the formalization. Phases 2 and 3 of the plan cover this section.

### Lemma 1 (Exact exponential).

> For every $z \in \mathbb{C}$:
> $$\mathrm{eml}(z, 1) \;=\; e^z.$$

**Proof.** $\mathrm{eml}(z, 1) = \exp(z) - \mathrm{Log}(1) = \exp(z) - 0 = \exp(z)$.

**Lean target:**
```lean
theorem eml_exp (z : ℂ) : eml z 1 = Complex.exp z
```
**Mathlib levers:** `Complex.log_one` (`Complex.log 1 = 0`), `sub_zero`.

---

### Definition (Reconstructed log).

Define
$$
L(x) \;:=\; \mathrm{eml}\bigl(1,\, \exp(\mathrm{eml}(1, x))\bigr).
$$

Unfolded: $L(x) = e - \mathrm{Log}\bigl(\exp(e - \mathrm{Log}\,x)\bigr)$.

### Lemma 2 (Reconstructed logarithm on the real axis).

> Two parts:
>
> **(2a)** For real $x > 0$: $L(x) = \log x$ (real natural log).
>
> **(2b)** For real $x < 0$: $L(x) = \mathrm{Log}(x) - 2\pi i$.
>
> **(2c) Universal property:** For every real $x \neq 0$: $\exp(L(x)) = x$.

**Proof of (2a).** For $x > 0$: $\mathrm{Log}\,x = \log x$ is real, so $e - \mathrm{Log}\,x$ is real, so $\exp(e - \mathrm{Log}\,x) = e^e/x$ is positive real. The outer $\mathrm{Log}$ on a positive real is exact: $\mathrm{Log}(e^e/x) = e - \log x$. Hence $L(x) = e - (e - \log x) = \log x$.

**Proof of (2b).** Write $x = -u$, $u > 0$. Then $\mathrm{Log}(x) = \log u + i\pi$. So $e - \mathrm{Log}\,x = e - \log u - i\pi$, and $\exp(e - \mathrm{Log}\,x) = e^{e - \log u} \cdot e^{-i\pi} = -e^e/u$, which is *negative* real. So $\mathrm{Log}(-e^e/u) = e - \log u + i\pi$ (note: principal branch sends negative reals to upper edge). Hence
$$L(x) = e - (e - \log u + i\pi) = \log u - i\pi.$$
Compare to $\mathrm{Log}(x) = \log u + i\pi$: indeed $L(x) = \mathrm{Log}(x) - 2\pi i$.

**Proof of (2c).** From (2a), for $x > 0$: $\exp(L(x)) = \exp(\log x) = x$. From (2b), for $x < 0$: $\exp(L(x)) = \exp(\mathrm{Log}(x) - 2\pi i) = \exp(\mathrm{Log}(x)) \cdot e^{-2\pi i} = x \cdot 1 = x$.

**Lean targets:**
```lean
def L (x : ℂ) : ℂ := eml 1 (Complex.exp (eml 1 x))

theorem L_pos {x : ℝ} (hx : 0 < x) : L (x : ℂ) = (Real.log x : ℂ)

theorem L_neg {x : ℝ} (hx : x < 0) :
    L (x : ℂ) = Complex.log (x : ℂ) - 2 * Real.pi * Complex.I

theorem exp_L {x : ℝ} (hx : x ≠ 0) : Complex.exp (L (x : ℂ)) = (x : ℂ)
```

**Mathlib levers:**
- `Complex.exp_log` (when `z ≠ 0`)
- `Complex.log_exp` (when `z.im ∈ (-π, π]`)
- `Complex.log_ofReal` for real positive arguments
- `Complex.log_neg_eq_log_of_neg` or equivalent for the upper-edge case
- `Complex.exp_sub`, `Complex.exp_add`
- `Complex.exp_int_mul_two_pi_mul_I` (the $e^{-2\pi i} = 1$ fact; the right Mathlib name should be confirmed in Phase 0)

**Recommended proof strategy.** Prove (2a) and (2b) directly via case split on `sign x`. Then derive (2c) as a corollary of (2a) ∧ (2b). The universal property (2c) is the only one used downstream, so if (2a) or (2b) become tedious, (2c) can be proved more directly by case analysis without going through the explicit values — but proving them gives stronger documentation.

---

### Lemma 3 (Subtraction on the real plane).

> For real $x \neq 0$ and real $y$:
> $$\mathrm{eml}(L(x), \exp(y)) \;=\; x - y.$$

**Proof.** By Lemma 2(c), $\exp(L(x)) = x$. Since $e^y > 0$ for real $y$, $\mathrm{Log}(e^y) = y$. Therefore
$$\mathrm{eml}(L(x), \exp(y)) = \exp(L(x)) - \mathrm{Log}(e^y) = x - y.$$

**Extension to $x = 0$.** Adopting $L(0) = -\infty$, $\exp(-\infty) = 0$: $\mathrm{eml}(L(0), \exp(y)) = 0 - y = -y$, recovering negation.

**Lean target:**
```lean
theorem eml_L_exp_eq_sub {x y : ℝ} (hx : x ≠ 0) :
    eml (L (x : ℂ)) (Complex.exp (y : ℂ)) = ((x - y : ℝ) : ℂ)
```

**Note on $x = 0$ extension.** The SI's $L(0) = -\infty$, $\exp(-\infty) = 0$ extension is informal and does *not* Lean-verify under Mathlib's `Complex.log 0 = 0` totalization (which forces $L(0) = e - e = 0$, not $-\infty$). The substitution $-x = 0 - x$ via Lemma 3 also fails: it would require $0 \neq 0$.

**Recommended Phase 3 witness.** The SI itself provides a clean alternative in the "Note on use of extended reals" footnote at the end of §2.5: for $z \in \mathbb{R}$ (or, more generally, where each step is defined),
$$-z \;=\; 1 - (e - ((e - 1) - z)).$$
**Verification.** Let $a := (e-1) - z$; then $e - a = e - (e-1) + z = 1 + z$; then $1 - (1+z) = -z$. ✓

**Why this works for Lean.** Each of the three subtractions, applied via Lemma 3, has a *strictly positive* first argument: $e-1 > 0$ for the innermost, $e > 0$ for the middle, and $1 > 0$ for the outermost. Lemma 3 requires only $\text{(first arg)} \neq 0$, which is satisfied a fortiori. No appeal to $L(0)$ is needed, and on its first-argument inputs $L$ acts as $\log$ throughout (Lemma 2(a)), so the witness lives entirely on the "easy" branch.

**Status.** This is the recommended Phase 3 construction. Claude Code is not bound to it — a shorter witness may exist, and the search procedure may surface alternatives — but the formalization is no longer blocked on resolving the negation question. See §8, Open Issue 1.

---

### Corollary 4 (Core basis from EML).

The set $\{1, \mathrm{eml}\}$ yields witnesses for: $e, 0, -1, 2, i, \pi, \exp, \log, -, +, \times, /, \sqrt{\cdot}, x^2, x^y, \log_b x, \mathrm{hypot}(x,y), x/2, (x+y)/2$.

**Identity list (the seven "remark" identities + five "corollary" identities):**

| # | Function | Identity | Domain |
|---|---|---|---|
| C1 | $0$ | $0 = L(1)$ | always |
| C2 | $-x$ | $-x = $ (see Lemma 3 note above) | TBD in Phase 3 |
| C3 | $-1$ | $-1 = 0 - 1$ | always |
| C4 | $2$ | $2 = 1 - (-1)$ | always |
| C5 | $x + y$ | $x + y = x - (-y)$ | $x, y$ where each step defined |
| C6 | $1/x$ | $1/x = \exp(-L(x))$ | $x \neq 0$ |
| C7 | $x \cdot y$ | $x \cdot y = \exp(L(x) + L(y))$ | $x, y > 0$ initially; extension needed for general |
| C8 | $x / y$ | $x/y = x \cdot (1/y)$ | $y \neq 0$ |
| C9 | $\pi$ | $\pi = \sqrt{-L(-1)^2}$ | always (with principal $\sqrt{}$) |
| C10 | $i$ | $i = -L(-1)/\pi$ | always |
| C11 | $\sqrt{x}$ | $\sqrt{x} = \exp(L(x)/2)$ | $x > 0$ |
| C12 | $x^y$ | $x^y = \exp(y \cdot L(x))$ | $x > 0$ |

**Note on C7.** The SI gives $x \cdot y = \exp(L(x) + L(y))$ which only works for $x, y > 0$ (where $L = \log$). For general real $x, y$ (including negatives), the witness needs additional case work, OR multiplication is handled by a different EML witness (e.g., the search procedure may have found one). **Phase 3 task:** decide whether to formalize multiplication on positive reals only (clean, narrow) or on all of $\mathbb{R}$ (tedious, sign cases). Recommend positive-reals first; extend later if scope allows.

**Lean targets (Phase 3):** one theorem per identity, with the domain hypothesis baked in as a precondition. Each builds on the previous via `simp`/`rw` chains using Lemmas 1–3 as the foundation.

---

## 3. Remaining primitives (transcendentals)

This is **Phase 4** of the plan, optional/scope-dependent.

The SI's "Remaining primitives: standard identities" table:

| Primitive | Identity | Real domain |
|---|---|---|
| $\cosh(x)$ | $(e^x + e^{-x})/2$ | all $x$ |
| $\sinh(x)$ | $(e^x - e^{-x})/2$ | all $x$ |
| $\tanh(x)$ | $\sinh x / \cosh x$ | all $x$ |
| $\cos(x)$ | $\cosh(-ix)$ | all $x$ |
| $\sin(x)$ | $\cos(x - \pi/2)$ | all $x$ |
| $\tan(x)$ | $\sin x / \cos x$ | $\cos x \neq 0$ |
| $\mathrm{arsinh}(x)$ | $\mathrm{Log}(x + \sqrt{1 + x^2})$ | all $x$ |
| $\mathrm{arcosh}(x)$ | $\mathrm{Log}(x + \sqrt{x-1}\sqrt{x+1})$ | $x > 1$ |
| $\mathrm{artanh}(x)$ | $\frac{1}{2}(\mathrm{Log}(1+x) - \mathrm{Log}(1-x))$ | $\lvert x \rvert < 1$ |
| $\arcsin(x)$ | $-i \mathrm{Log}(ix + \sqrt{1-x^2})$ | $\lvert x \rvert < 1$ |
| $\arccos(x)$ | $\pi/2 - \arcsin(x)$ | $\lvert x \rvert < 1$ |
| $\arctan(x)$ | $\frac{i}{2}(\mathrm{Log}(1-ix) - \mathrm{Log}(1+ix))$ | all $x$ |

Each of these is a textbook principal-branch identity. Mathlib has all of these defined; the formalization work is: (a) verify the principal-branch identity holds at the Mathlib definition level (often already a Mathlib lemma); (b) compose the EML witness by recursive substitution; (c) discharge domain conditions.

**Practical observation.** Phase 4 is *less mathematically interesting* than Phases 2–3 because the principal-branch identities are well-trodden Mathlib territory. The interesting work is the EML composition and domain bookkeeping. CC will likely do well here once Phases 2–3 establish the patterns.

---

## 4. The discovery chain (Table S2)

For traceability with the paper. The 32-step witness chain that the paper's automated search produced. **This is informational** — the formalization does not need to follow the exact discovery order, but each row corresponds to a Lean target if Phase 4/5 is fully completed.

| Step | Primitive | $K$ | Witness expression |
|---|---|---|---|
| 1 | $e$ | 3 | $\mathrm{eml}(1, 1)$ |
| 2 | $\exp(x)$ | 3 | $\mathrm{eml}(x, 1)$ |
| 3 | $\ln(x)$ | 6 | $\mathrm{eml}(1, \exp(\mathrm{eml}(1, x)))$ |
| 4 | $x - y$ | 5 | $\mathrm{eml}(\ln x, \exp y)$ |
| 5 | $-1$ | 4 | $\ln(1) - 1$ |
| 6 | $2$ | 3 | $1 - (-1)$ |
| 7 | $-x$ | 4 | $\ln(1) - x$ |
| 8 | $x + y$ | 4 | $x - (-y)$ |
| 9 | $1/x$ | 4 | $\exp(-\ln x)$ |
| 10 | $x \times y$ | 6 | $\exp(\ln x + \ln y)$ |
| 11 | $x^2$ | 3 | $x \times x$ |
| 12 | $x/y$ | 4 | $x \times (1/y)$ |
| 13 | $x/2$ | 3 | $x/2$ |
| 14 | $\mathrm{avg}(x,y)$ | 4 | $\mathrm{half}(x+y)$ |
| 15 | $\sqrt{x}$ | 4 | $\exp(\mathrm{half}(\ln x))$ |
| 16 | $x^y$ | 5 | $\exp(y \times \ln x)$ |
| 17 | $\log_x y$ | 5 | $\ln y / \ln x$ |
| 18 | $\pi$ | 5 | $\sqrt{-(\ln(-1))^2}$ |
| 19 | $\mathrm{hypot}(x, y)$ | 6 | $\sqrt{x^2 + y^2}$ |
| 20 | $\sigma(x)$ | 6 | $1 / \mathrm{eml}(-x, \exp(-1))$ |
| 21 | $\cosh(x)$ | 6 | $\mathrm{avg}(\exp x, \exp(-x))$ |
| 22 | $\sinh(x)$ | 5 | $\mathrm{eml}(x, \exp(\cosh x))$ |
| 23 | $\tanh(x)$ | 5 | $\sinh x / \cosh x$ |
| 24 | $\cos(x)$ | 5 | $\cosh(\sqrt{-x^2})$ |
| 25 | $\sin(x)$ | 5 | $\cos(x - \pi/2)$ |
| 26 | $\tan(x)$ | 5 | $\sin x / \cos x$ |
| 27 | $\mathrm{arsinh}(x)$ | 6 | $\ln(x + \mathrm{hypot}(-1, x))$ |
| 28 | $\mathrm{arcosh}(x)$ | 5 | $\mathrm{arsinh}(\mathrm{hypot}(x, -1))$ |
| 29 | $\arccos(x)$ | 4 | $\mathrm{arcosh}(\cos(\mathrm{arcosh}(x)))$ |
| 30 | $\mathrm{artanh}(x)$ | 5 | $\mathrm{arsinh}(1/\tan(\arccos(x)))$ |
| 31 | $\arcsin(x)$ | 5 | $\pi/2 - \arccos(x)$ |
| 32 | $\arctan(x)$ | 4 | $\arcsin(\tanh(\mathrm{arsinh}(x)))$ |

Note: the witness at step 22 ($\sinh x = \mathrm{eml}(x, \exp(\cosh x))$) is striking and worth verifying numerically before formalizing — it is *not* the textbook $(e^x - e^{-x})/2$ but an alternative form.

---

## 5. Completeness theorem (Theorem 5)

This is **Phase 5**, optional.

> **Theorem 5 (Completeness for the Table-1 class).** Fix the principal branches above. For every expression $F \in F_{36}(X)$, there exists a finite EML term $W_F \in T_{\mathrm{EML}}(X)$ such that $W_F$ and $F$ agree at every real point where all recursively substituted witness identities are defined.

**Proof structure (from SI):** structural induction on $F$, witness substitution, domain pullback.

**Lean target:** define `F36` as an inductive type mirroring the 36-primitive class, define a witness function `witness : F36 X → EMLTree (vars X)`, and prove the agreement theorem by induction on `F36`.

**Honest note.** Theorem 5 in Lean is mostly bookkeeping once Phases 3 and 4 are done. The interesting mathematics is in Lemmas 1–3 and the principal-branch identities. Theorem 5 is the "big finish" that ties everything together but contributes no new mathematical content.

---

## 6. Out of scope

Explicitly **not** part of any phase:

- The Adam optimization / symbolic regression results (Section 3 of SI). These are empirical numerical claims, not theorems.
- Cross-backend IEEE 754 numerical agreement. Empirical.
- The "ternary variant" teased in the paper's conclusion.
- Any claim about the *minimality* or *optimality* of EML beyond the trivial counting argument.
- The Sheffer-completeness claim for the *full* Liouvillian class (the paper restricts to the 36-primitive Table 1 list).

---

## 7. Phase mapping

| Phase | SPEC sections covered | Status |
|---|---|---|
| 0 | §1 (Mathlib API recon) | Brief in `PHASE_0_BRIEF.md` |
| 1 | §1.2, §1.3 (grammar, denotation) | Pending |
| 2 | §2 Lemmas 1–3 | Pending |
| 3 | §2 Corollary 4 (C1–C12) | Pending |
| 4 | §3 (transcendentals) | Optional |
| 5 | §5 (Theorem 5) | Optional |

---

## 8. Open issues / TODOs

1. **Negation witness.** ~~Open.~~ **Resolved (recommended construction).** Use the SI's clean-math witness $-z = 1 - (e - ((e-1) - z))$, which expresses negation as three nested Lemma-3 subtractions whose first arguments are all strictly positive (and in particular nonzero), avoiding the $L(0)$ totalization issue entirely. See expanded note under Lemma 3. Phase 3 may adopt this directly or substitute a shorter witness if one is found.
2. **Multiplication domain.** SI's $x \cdot y = \exp(L(x) + L(y))$ requires $x, y > 0$. Phase 3 decision: positive-reals only, or extend to all reals via case work, or find an alternative witness.
3. **$\sinh$ alternative witness.** Step 22 of Table S2 uses $\sinh x = \mathrm{eml}(x, \exp(\cosh x))$. Verify this is correct (it claims $e^x - \cosh x = \sinh x$, which checks: $e^x - (e^x + e^{-x})/2 = (e^x - e^{-x})/2 = \sinh x$. ✓). Decide whether to formalize this witness or the textbook one.
4. **Phase 0 must verify** the exact Mathlib lemma names: `Complex.log_one`, `Complex.log_neg_one`, `Complex.exp_log`, `Complex.log_exp`, `Complex.exp_sub`, plus the $e^{2\pi i} = 1$ fact (most likely `Complex.exp_two_pi_mul_I`, with the $n = -1$ specialization derivable via `Complex.exp_neg` or `Complex.exp_int_mul_two_pi_mul_I`). Until these are confirmed, all Lean stubs use them as conjectural API references.
