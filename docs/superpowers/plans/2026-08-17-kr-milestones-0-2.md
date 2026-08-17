# Krohn–Rhodes Milestones 0–2 Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Stand up the Lean 4 project (lake + Mathlib + CI + blueprint) and build the first two theory layers: the `TransMon` structure with its basic API, and both division notions with their preorder lemmas.

**Architecture:** Standalone Lean 4 project over Mathlib. Core object is a bundled `TransMon` structure (finite state set, finite monoid, raw right action). Everything lives in the `KRTheory` namespace with scoped notation. Blueprint LaTeX chapters are written before the Lean they describe.

**Tech Stack:** Lean 4 (toolchain pinned to Mathlib's), lake, Mathlib (master, locked by manifest), GitHub Actions `lean-action`, plain LaTeX blueprint (plastex tooling deferred).

**Spec:** `docs/superpowers/specs/2026-08-17-krohn-rhodes-formalization-design.md` — this plan implements spec milestones 0–2 (spec §5–§7; definitions from §3.1–§3.2, §4.1–§4.3).

## Global Constraints

- All Lean code inside `namespace KRTheory`; all notation declared `scoped`.
- Carriers in `Type` (no universe polymorphism) — spec §2.
- Mathlib naming conventions: `UpperCamelCase` types/structures, `lowerCamelCase` defs, `snake_case` theorems.
- Every definitional file ends with `example`-based sanity checks — spec §6.
- No `sorry` in committed code at the end of any task.
- Docstrings cite [DKS] (= arXiv:1111.1585) section numbers where applicable.
- Commit messages: plain, no Co-Authored-By trailers.

## Formalization TDD mapping (read this first)

The red/green cycle for formalization work:

- **RED** = write the definitions and theorem *statements* with `:= sorry` bodies plus the `example` sanity checks, then `lake build`. Success at this stage means *the statements elaborate* (types are right); the build reports `sorry` warnings. If a statement doesn't elaborate, fix the statement — that's the analogue of a test that won't compile.
- **GREEN** = replace each `sorry` with a proof; `lake build` completes with **zero warnings about sorry** and `grep -rn "sorry" KRTheory/` prints nothing.
- Wrong-but-consistent definitions are the failure mode that costs months; the `example` checks on concrete instances (`trivialTM`, `TransMon.regular (ZMod 3)`, …) are the guard. Never skip them.

**Mathlib name drift:** Mathlib evolves; if a lemma name in this plan doesn't resolve (e.g. `Submonoid.topEquiv`), do NOT hand-roll a replacement — find the current name with `exact?` / `apply?` in-file, or https://loogle.lean-lang.org. The mathematical content of each step is fixed; exact Mathlib identifiers are best-effort.

---

### Task 1: Lake scaffold with Mathlib

**Files:**
- Create: `lean-toolchain` (fetched from Mathlib)
- Create: `lakefile.toml`
- Create: `.gitignore`
- Create: `KRTheory.lean`
- Created by tooling: `lake-manifest.json`

**Interfaces:**
- Produces: a building lake package named `krtheory` with library target `KRTheory`, Mathlib available for import. Later tasks add files under `KRTheory/` and import them from `KRTheory.lean`.

- [ ] **Step 1: Pin the toolchain to Mathlib's**

```bash
cd /Users/bono/formalizations/kr-theory
curl -L https://raw.githubusercontent.com/leanprover-community/mathlib4/master/lean-toolchain -o lean-toolchain
cat lean-toolchain
```

Expected: one line like `leanprover/lean4:v4.X.0`. (Mathlib's `lake update` post-update hook keeps this file in sync from now on.)

- [ ] **Step 2: Write `lakefile.toml`**

```toml
name = "krtheory"
defaultTargets = ["KRTheory"]

[[require]]
name = "mathlib"
git = "https://github.com/leanprover-community/mathlib4.git"
rev = "master"

[[lean_lib]]
name = "KRTheory"
```

- [ ] **Step 3: Write `.gitignore`**

```
.lake/
blueprint/src/*.aux
blueprint/src/*.log
blueprint/src/*.fls
blueprint/src/*.fdb_latexmk
blueprint/src/*.out
blueprint/src/*.toc
blueprint/src/*.pdf
```

- [ ] **Step 4: Write the root module `KRTheory.lean` (smoke test)**

```lean
import Mathlib.Tactic

-- Scaffold smoke test; replaced by library imports in Task 4.
example : (2 : ℕ) + 2 = 4 := by norm_num
```

- [ ] **Step 5: Fetch dependencies and the olean cache**

```bash
lake update && lake exe cache get
```

Expected: Mathlib clone + several GB of `.olean` downloads. This takes minutes to tens of minutes — run with a long timeout or in the background; do not interrupt. `lake update` may rewrite `lean-toolchain` (the post-update hook) — that is correct behavior.

- [ ] **Step 6: Build (RED→GREEN for the scaffold)**

```bash
lake build
```

Expected: compiles `KRTheory` with no errors. If Mathlib itself starts compiling from source (thousands of jobs), stop and re-run `lake exe cache get` — the cache fetch didn't take.

- [ ] **Step 7: Commit**

```bash
git add lean-toolchain lakefile.toml lake-manifest.json .gitignore KRTheory.lean
git commit -m "Scaffold lake project with Mathlib dependency"
```

---

### Task 2: CI workflow

**Files:**
- Create: `.github/workflows/ci.yml`

**Interfaces:**
- Produces: CI that builds the project on every push/PR once the repo is on GitHub. No other task depends on this.

- [ ] **Step 1: Write the workflow**

```yaml
name: CI

on:
  push:
    branches: [main]
  pull_request:

jobs:
  build:
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v4
      - uses: leanprover/lean-action@v1
```

(`lean-action` runs `lake exe cache get` and `lake build` automatically for Mathlib-dependent projects.)

- [ ] **Step 2: Verify locally what can be verified**

```bash
ruby -ryaml -e 'YAML.load_file(".github/workflows/ci.yml"); puts "yaml ok"' 2>/dev/null || python3 -c "import yaml,sys; yaml.safe_load(open('.github/workflows/ci.yml')); print('yaml ok')"
```

Expected: `yaml ok`. (Full CI verification happens on first GitHub push — the repo has no remote yet; that's fine and is the user's call per spec §6.)

- [ ] **Step 3: Commit**

```bash
git add .github/workflows/ci.yml
git commit -m "Add CI workflow using lean-action"
```

---

### Task 3: Blueprint skeleton with chapters for milestones 1–2

**Files:**
- Create: `blueprint/README.md`
- Create: `blueprint/src/print.tex`
- Create: `blueprint/src/content.tex`
- Create: `blueprint/src/chapters/transmon.tex`
- Create: `blueprint/src/chapters/division.tex`

**Interfaces:**
- Produces: compilable-with-plain-LaTeX blueprint whose \lean{} names are the contract for Tasks 4–8: `KRTheory.TransMon`, `KRTheory.TransMon.Faithful`, `KRTheory.TransMon.trivialTM`, `KRTheory.TransMon.regular`, `KRTheory.TransMon.regular_faithful`, `KRTheory.MonoidDivides`, `KRTheory.TransMon.StrongDivides`, `KRTheory.TransMon.Covering`, `KRTheory.TransMon.StrongDivides.monoidDivides`.

Per spec §6 the informal chapter precedes the Lean. The full plastex/`leanblueprint` web toolchain is deferred (Python/TeX environment setup is not worth blocking on); `print.tex` is self-contained standard LaTeX so the document compiles anywhere LaTeX exists, and upgrading to `leanblueprint` later only replaces the preamble.

- [ ] **Step 1: Write `blueprint/README.md`**

```markdown
# Blueprint

Human-readable mathematical companion to the Lean formalization, written
chapter-by-chapter *before* the corresponding Lean (spec §6).

- `src/print.tex` — self-contained LaTeX entry point: `latexmk -pdf print.tex`.
- `src/chapters/` — one file per theory layer, mirroring `KRTheory/`.
- `\lean{...}` names the Lean declaration; `\leanok` marks it formalized.

TODO(post-v1 or when publishing): migrate preamble to the `leanblueprint`
toolchain (plastex web build + dependency graph). Chapter sources are
already written in its macro dialect, so migration is preamble-only.
```

- [ ] **Step 2: Write `blueprint/src/print.tex`**

```latex
\documentclass[11pt]{report}
\usepackage{amsmath,amssymb,amsthm}
\usepackage[colorlinks=true]{hyperref}

% leanblueprint-compatible macros (print fallbacks)
\newcommand{\lean}[1]{\marginpar{\tiny\texttt{#1}}}
\newcommand{\leanok}{\marginpar{\tiny$\checkmark$}}
\newcommand{\uses}[1]{}
\newcommand{\notready}{}

\newtheorem{theorem}{Theorem}[chapter]
\newtheorem{lemma}[theorem]{Lemma}
\newtheorem{proposition}[theorem]{Proposition}
\theoremstyle{definition}
\newtheorem{definition}[theorem]{Definition}
\newtheorem{example}[theorem]{Example}
\theoremstyle{remark}
\newtheorem{remark}[theorem]{Remark}

\title{The Krohn--Rhodes Theorem in Lean 4\\\large Blueprint}
\author{Juan Bono}

\begin{document}
\maketitle
\tableofcontents
\input{content}
\end{document}
```

- [ ] **Step 3: Write `blueprint/src/content.tex`**

```latex
\chapter*{Introduction}

We formalize the Krohn--Rhodes theorem following the local divisor proof of
Diekert, Kufleitner and Steinberg~(arXiv:1111.1585, cited as [DKS]).
Every finite monoid divides an iterated wreath product whose factors are
flip-flops and finite simple groups dividing the original monoid.
Conventions: actions are \emph{right} actions, written $x \cdot m$; in a
product $mn$, the factor $m$ acts first.

\input{chapters/transmon}
\input{chapters/division}
```

- [ ] **Step 4: Write `blueprint/src/chapters/transmon.tex`**

```latex
\chapter{Transformation monoids}\label{ch:transmon}

\begin{definition}[Transformation monoid; DKS §2.1]\label{def:transmon}
  \lean{KRTheory.TransMon}
  A \emph{finite transformation monoid} $T = (X, M)$ consists of a finite
  set $X$ (the \emph{states}), a finite monoid $M$, and a right action
  $X \times M \to X$, written $x \cdot m$, satisfying $x \cdot 1 = x$ and
  $x \cdot (mn) = (x \cdot m) \cdot n$.
  We do \emph{not} require the action to be faithful.
\end{definition}

\begin{definition}[Faithfulness]\label{def:faithful}
  \lean{KRTheory.TransMon.Faithful}\uses{def:transmon}
  $T = (X,M)$ is \emph{faithful} if $x \cdot m = x \cdot n$ for all
  $x \in X$ implies $m = n$.
\end{definition}

\begin{definition}[Trivial transformation monoid]\label{def:trivialTM}
  \lean{KRTheory.TransMon.trivialTM}\uses{def:transmon}
  $\mathbf{1} = (\{*\}, \{1\})$: one state, trivial monoid. It is the base
  of iterated wreath products.
\end{definition}

\begin{definition}[Regular representation]\label{def:regular}
  \lean{KRTheory.TransMon.regular}\uses{def:transmon}
  For a finite monoid $M$, the transformation monoid $(M, M)$ where $M$
  acts on itself by right multiplication: $x \cdot m = xm$.
\end{definition}

\begin{lemma}\label{lem:regular-faithful}
  \lean{KRTheory.TransMon.regular_faithful}\uses{def:regular,def:faithful}
  The regular representation is faithful.
\end{lemma}
\begin{proof}
  If $xm = xn$ for all $x$, take $x = 1$.
\end{proof}
```

- [ ] **Step 5: Write `blueprint/src/chapters/division.tex`**

```latex
\chapter{Division}\label{ch:division}

Division is the ``is at most as complicated as'' preorder of the theory:
the Krohn--Rhodes theorem is a statement about division into wreath
products.

\begin{definition}[Monoid division; DKS §2.3]\label{def:mdiv}
  \lean{KRTheory.MonoidDivides}
  For monoids $M, N$: $M \prec_{\mathrm m} N$ iff $M$ is a quotient of a
  submonoid of $N$, i.e.\ there are a submonoid $N' \le N$ and a
  surjective monoid morphism $\psi : N' \twoheadrightarrow M$.
\end{definition}

\begin{lemma}[Preorder]\label{lem:mdiv-preorder}
  \lean{KRTheory.MonoidDivides.refl, KRTheory.MonoidDivides.trans}
  \uses{def:mdiv}
  $\prec_{\mathrm m}$ is reflexive and transitive.
\end{lemma}
\begin{proof}
  Reflexivity: $N' = N$, $\psi = \mathrm{id}$. Transitivity: given
  $\psi : N' \twoheadrightarrow M$ (with $N' \le N$) and
  $\chi : P' \twoheadrightarrow N$ (with $P' \le P$), let
  $Q = \chi^{-1}(N') \le P'$, a submonoid of $P$; then
  $\psi \circ \chi|_Q : Q \twoheadrightarrow M$ (surjective because
  $\chi$ is onto $N$, so onto $N'$ from $Q$).
\end{proof}

\begin{definition}[Strong division; DKS §2.3]\label{def:sdiv}
  \lean{KRTheory.TransMon.StrongDivides, KRTheory.TransMon.Covering}
  \uses{def:transmon}
  For transformation monoids $S = (X, M)$ and $T = (Y, N)$:
  $S \prec T$ iff there are a submonoid $N' \le N$, a surjection
  $\varphi : Y \twoheadrightarrow X$, and a surjective monoid morphism
  $\psi : N' \twoheadrightarrow M$ with
  $\varphi(y) \cdot \psi(n) = \varphi(y \cdot n)$ for all $y \in Y$,
  $n \in N'$. The witnessing triple is a \emph{covering}.
\end{definition}

\begin{lemma}[Preorder]\label{lem:sdiv-preorder}
  \lean{KRTheory.TransMon.StrongDivides.refl,
        KRTheory.TransMon.StrongDivides.trans}
  \uses{def:sdiv}
  $\prec$ is reflexive and transitive.
\end{lemma}
\begin{proof}
  Reflexivity: identity covering. Transitivity: compose the state
  surjections, and pull the monoid data back exactly as in
  Lemma~\ref{lem:mdiv-preorder}; equivariance is a two-step chase.
\end{proof}

\begin{lemma}[Glue]\label{lem:sdiv-mdiv}
  \lean{KRTheory.TransMon.StrongDivides.monoidDivides}
  \uses{def:sdiv,def:mdiv}
  $(X, M) \prec (Y, N)$ implies $M \prec_{\mathrm m} N$.
\end{lemma}
\begin{proof}
  Read $\psi$ off the covering and forget the states.
\end{proof}
```

- [ ] **Step 6: Compile if LaTeX is available**

```bash
command -v latexmk >/dev/null && (cd blueprint/src && latexmk -pdf -interaction=nonstopmode print.tex && latexmk -c) || echo "latexmk not installed - skipping compile (acceptable; see blueprint/README.md)"
```

Expected: `print.pdf` produced, or the skip message. Either outcome passes; a LaTeX *error* (with latexmk present) does not.

- [ ] **Step 7: Commit**

```bash
git add blueprint
git commit -m "Add blueprint skeleton with transformation monoid and division chapters"
```

---

### Task 4: TransMon structure, instances, notation, trivialTM

**Files:**
- Create: `KRTheory/TransMon/Basic.lean`
- Modify: `KRTheory.lean` (replace smoke test with library import)

**Interfaces:**
- Consumes: Mathlib (`Fintype`, `Monoid`, `PUnit` instances).
- Produces (used by every later task):
  - `structure KRTheory.TransMon : Type 1` with fields `X : Type`, `M : Type`, `fintypeX : Fintype X`, `monoidM : Monoid M`, `fintypeM : Fintype M`, `act : X → M → X`, `act_one : ∀ x, act x 1 = x`, `act_mul : ∀ x m n, act x (m * n) = act (act x m) n`; the three instance fields registered as instances; `act_one`/`act_mul` are `@[simp]`.
  - `KRTheory.TransMon.trivialTM : TransMon` (states `PUnit`, monoid `PUnit`).
  - Scoped notation `x ⊳ m` for `TransMon.act _ x m` (sugar only — plan code uses explicit `T.act`).

- [ ] **Step 1: Write the file with structure, attributes, and examples (RED)**

```lean
import Mathlib.Tactic

/-!
# Transformation monoids

The core object of the Krohn–Rhodes formalization [DKS §2.1]: a finite
state set with a right action of a finite monoid. Design decisions
(bundled structure, raw right action) are recorded in the design doc
§4.1. Right-action convention: in `x ⊳ (m * n)`, `m` acts first.
-/

namespace KRTheory

/-- A finite transformation monoid `(X, M)`: finite states `X`, finite
monoid `M`, right action `act`. Faithfulness is NOT required; see
`TransMon.Faithful`. [DKS §2.1] -/
structure TransMon : Type 1 where
  /-- The state set. -/
  X : Type
  /-- The monoid carrier. -/
  M : Type
  [fintypeX : Fintype X]
  [monoidM : Monoid M]
  [fintypeM : Fintype M]
  /-- The right action of `M` on `X`. -/
  act : X → M → X
  act_one : ∀ x, act x 1 = x
  act_mul : ∀ x m n, act x (m * n) = act (act x m) n

namespace TransMon

attribute [instance] fintypeX monoidM fintypeM
attribute [simp] act_one act_mul

/-- Right-action notation. `m` binds tighter so `x ⊳ m * n` parses as
`x ⊳ (m * n)`. Sugar over `T.act`; use `T.act` when the ambient `T` is a
compound object Lean cannot infer. -/
scoped notation:65 x:65 " ⊳ " m:66 => TransMon.act _ x m

/-- The one-state, one-element transformation monoid; base of iterated
wreath products. -/
def trivialTM : TransMon where
  X := PUnit
  M := PUnit
  act _ _ := PUnit.unit
  act_one x := by cases x; rfl
  act_mul _ _ _ := rfl

-- Sanity checks (spec §6): the trivial object is as small as it claims.
example : Fintype.card trivialTM.X = 1 := rfl
example : Fintype.card trivialTM.M = 1 := rfl
example (x : trivialTM.X) (m : trivialTM.M) : trivialTM.act x m = x := by
  cases x; rfl

end TransMon
end KRTheory
```

- [ ] **Step 2: Point the root module at the library**

Replace the entire content of `KRTheory.lean` with:

```lean
import KRTheory.TransMon.Basic
```

- [ ] **Step 3: Build and fix elaboration (RED→GREEN)**

```bash
lake build 2>&1 | tail -20
```

Expected: success, no warnings. Likely failure modes and fixes: notation precedence errors (adjust the `:65`/`:66` levels); `attribute [instance]` complaining (ensure it is inside `namespace TransMon` or use fully qualified names `TransMon.fintypeX` etc.).

- [ ] **Step 4: Confirm no sorry**

```bash
grep -rn "sorry" KRTheory/ KRTheory.lean; test $? -eq 1 && echo "clean"
```

Expected: `clean`.

- [ ] **Step 5: Commit**

```bash
git add KRTheory.lean KRTheory/TransMon/Basic.lean
git commit -m "Add TransMon structure with trivial instance"
```

---

### Task 5: Faithful, regular representation, regular_faithful

**Files:**
- Modify: `KRTheory/TransMon/Basic.lean` (append inside `namespace TransMon`, before `end TransMon`)

**Interfaces:**
- Consumes: `TransMon`, `trivialTM` (Task 4); Mathlib `ZMod`.
- Produces:
  - `def KRTheory.TransMon.Faithful (T : TransMon) : Prop` — `∀ ⦃m n : T.M⦄, (∀ x, T.act x m = T.act x n) → m = n`.
  - `def KRTheory.TransMon.regular (M : Type) [Monoid M] [Fintype M] : TransMon` with `X = M`, action = right multiplication.
  - `theorem KRTheory.TransMon.regular_faithful (M : Type) [Monoid M] [Fintype M] : (regular M).Faithful`.
  - `theorem KRTheory.TransMon.trivialTM_faithful : trivialTM.Faithful`.

- [ ] **Step 1: Append statements with sorry + examples (RED)**

```lean
/-- `T.Faithful`: the action distinguishes monoid elements. A `def`, not
a class — bundled values make instance search unreliable (spec §4.1). -/
def Faithful (T : TransMon) : Prop :=
  ∀ ⦃m n : T.M⦄, (∀ x : T.X, T.act x m = T.act x n) → m = n

theorem trivialTM_faithful : trivialTM.Faithful := sorry

/-- The regular representation `(M, M)`: `M` acting on itself by right
multiplication. Always faithful; the bridge from abstract monoids to
transformation monoids. [DKS §2.1] -/
def regular (M : Type) [Monoid M] [Fintype M] : TransMon where
  X := M
  M := M
  act x m := x * m
  act_one := mul_one
  act_mul x m n := (mul_assoc x m n).symm

theorem regular_faithful (M : Type) [Monoid M] [Fintype M] :
    (regular M).Faithful := sorry

-- Sanity checks (spec §6).
example : Fintype.card (regular (ZMod 3)).X = 3 := by
  simp [regular, ZMod.card]
example : (regular (ZMod 3)).act 2 2 = 1 := by decide  -- 2·2 = 4 ≡ 1
example : (regular (ZMod 4)).act 3 2 = 2 := by decide  -- 3·2 = 6 ≡ 2
```

- [ ] **Step 2: Build — statements must elaborate**

```bash
lake build 2>&1 | tail -20
```

Expected: builds with exactly two `declaration uses 'sorry'` warnings. The `example`s must already pass (they test `regular`'s definition, not the sorried theorems). If `simp [regular, ZMod.card]` fails, try `rfl` or `decide` — the goal is `Fintype.card (ZMod 3) = 3` after unfolding.

- [ ] **Step 3: Prove the two theorems (GREEN)**

```lean
theorem trivialTM_faithful : trivialTM.Faithful := by
  intro m n _
  rfl

theorem regular_faithful (M : Type) [Monoid M] [Fintype M] :
    (regular M).Faithful := by
  intro m n h
  simpa using h 1
```

(For `regular_faithful`: `h 1 : 1 * m = 1 * n`; `simpa` closes via `one_mul`. For `trivialTM_faithful`: `m n : PUnit`, so `rfl` — if it balks, `cases m; cases n; rfl`.)

- [ ] **Step 4: Build clean + no sorry**

```bash
lake build 2>&1 | tail -5 && (grep -rn "sorry" KRTheory/ KRTheory.lean; test $? -eq 1 && echo "clean")
```

Expected: build success, `clean`.

- [ ] **Step 5: Update blueprint checkmarks**

In `blueprint/src/chapters/transmon.tex`, add `\leanok` after the `\lean{...}` of: Definition `def:transmon`, Definition `def:faithful`, Definition `def:trivialTM`, Definition `def:regular`, Lemma `lem:regular-faithful`.

- [ ] **Step 6: Commit**

```bash
git add KRTheory/TransMon/Basic.lean blueprint/src/chapters/transmon.tex
git commit -m "Add faithfulness and the regular representation"
```

---

### Task 6: Monoid division and its preorder

**Files:**
- Create: `KRTheory/TransMon/Division.lean`
- Modify: `KRTheory.lean`

**Interfaces:**
- Consumes: `TransMon` API (Task 4–5); Mathlib `Submonoid`, `MonoidHom`, `Submonoid.topEquiv`, `Submonoid.comap`/`map`, `Submonoid.equivMapOfInjective`, `MonoidHom.submonoidComap`.
- Produces:
  - `def KRTheory.MonoidDivides (M N : Type) [Monoid M] [Monoid N] : Prop` — `∃ (N' : Submonoid N) (ψ : N' →* M), Function.Surjective ψ`; scoped infix `M ≺ₘ N` at precedence 50.
  - `theorem KRTheory.MonoidDivides.refl (M : Type) [Monoid M] : M ≺ₘ M`
  - `theorem KRTheory.MonoidDivides.trans : M ≺ₘ N → N ≺ₘ P → M ≺ₘ P` (implicit `{M N P : Type}` with instances)
  - `theorem KRTheory.MonoidDivides.of_surjective (f : N →* M) (hf : Function.Surjective f) : M ≺ₘ N`
  - `theorem KRTheory.MonoidDivides.of_submonoid (N' : Submonoid N) : (↥N') ≺ₘ N`

- [ ] **Step 1: Create the file with statements + sorries + examples (RED)**

```lean
import KRTheory.TransMon.Basic

/-!
# Division

Monoid division [DKS §2.3]: `M ≺ₘ N` iff `M` is a quotient of a
submonoid of `N` — the "at most as complicated as" preorder. Strong
division of transformation monoids lives in the second half of this
file (Tasks 7–8).
-/

namespace KRTheory

/-- `M ≺ₘ N`: `M` is a homomorphic image of a submonoid of `N`.
[DKS §2.3] -/
def MonoidDivides (M N : Type) [Monoid M] [Monoid N] : Prop :=
  ∃ (N' : Submonoid N) (ψ : N' →* M), Function.Surjective ψ

@[inherit_doc]
scoped infix:50 " ≺ₘ " => MonoidDivides

namespace MonoidDivides

variable {M N P : Type} [Monoid M] [Monoid N] [Monoid P]

theorem refl (M : Type) [Monoid M] : M ≺ₘ M := sorry

theorem of_surjective (f : N →* M) (hf : Function.Surjective f) :
    M ≺ₘ N := sorry

theorem of_submonoid (N' : Submonoid N) : (↥N') ≺ₘ N := sorry

theorem trans (h₁ : M ≺ₘ N) (h₂ : N ≺ₘ P) : M ≺ₘ P := sorry

end MonoidDivides

-- Sanity checks (spec §6).
example : ZMod 2 ≺ₘ (ZMod 2 × ZMod 3) :=
  .of_surjective (MonoidHom.fst _ _) Prod.fst_surjective
example : ZMod 6 ≺ₘ ZMod 6 := .refl _

end KRTheory
```

- [ ] **Step 2: Add the import and build**

`KRTheory.lean` becomes:

```lean
import KRTheory.TransMon.Basic
import KRTheory.TransMon.Division
```

```bash
lake build 2>&1 | tail -20
```

Expected: four sorry warnings; the two `example`s elaborate (they use the sorried `refl`/`of_surjective` statements — types must check even though proofs are pending).

- [ ] **Step 3: Prove refl, of_surjective, of_submonoid (GREEN part 1)**

```lean
theorem refl (M : Type) [Monoid M] : M ≺ₘ M :=
  ⟨⊤, Submonoid.topEquiv.toMonoidHom, Submonoid.topEquiv.surjective⟩

theorem of_surjective (f : N →* M) (hf : Function.Surjective f) :
    M ≺ₘ N :=
  ⟨⊤, f.comp (Submonoid.subtype ⊤), fun m => by
    obtain ⟨n, hn⟩ := hf m
    exact ⟨⟨n, trivial⟩, hn⟩⟩

theorem of_submonoid (N' : Submonoid N) : (↥N') ≺ₘ N :=
  ⟨N', MonoidHom.id ↥N', Function.surjective_id⟩
```

- [ ] **Step 4: Prove trans (GREEN part 2 — the comap/map dance)**

The math (blueprint `lem:mdiv-preorder`): pull `N'` back along `χ : P' →* N` to `Q := N'.comap χ ≤ P'`, push into `P` for the answer submonoid, and compose morphisms.

```lean
theorem trans (h₁ : M ≺ₘ N) (h₂ : N ≺ₘ P) : M ≺ₘ P := by
  obtain ⟨N', ψ, hψ⟩ := h₁
  obtain ⟨P', χ, hχ⟩ := h₂
  -- e : the preimage submonoid of P', viewed inside P
  let Q : Submonoid P' := N'.comap χ
  refine ⟨Q.map P'.subtype, ?_, ?_⟩
  · -- morphism: (Q in P) ≃* Q →* N' →* M
    exact ψ.comp ((χ.submonoidComap N').comp
      (Submonoid.equivMapOfInjective Q P'.subtype
        P'.subtype_injective).symm.toMonoidHom)
  · -- surjectivity: each stage is surjective
    apply hψ.comp
    apply Function.Surjective.comp
    · -- χ.submonoidComap N' is surjective because χ is
      rintro ⟨n, hn⟩
      obtain ⟨p, hp⟩ := hχ n
      exact ⟨⟨p, by simpa [Submonoid.mem_comap, hp] using hn⟩,
        Subtype.ext hp⟩
    · exact (Submonoid.equivMapOfInjective _ _ _).symm.surjective
```

Name-drift watchpoints (use `exact?` if these fail): `MonoidHom.submonoidComap`, `Submonoid.equivMapOfInjective`, `P'.subtype_injective` (may be `Submonoid.subtype_injective` or provable as `Subtype.coe_injective`). The `simpa [Submonoid.mem_comap, hp]` step shows `p ∈ Q`, i.e. `χ ⟨p, _⟩ ∈ N'` — if the subtype plumbing fights, prove membership as a `have` first.

- [ ] **Step 5: Build clean + no sorry**

```bash
lake build 2>&1 | tail -5 && (grep -rn "sorry" KRTheory/ KRTheory.lean; test $? -eq 1 && echo "clean")
```

Expected: build success, `clean`.

- [ ] **Step 6: Commit**

```bash
git add KRTheory.lean KRTheory/TransMon/Division.lean
git commit -m "Add monoid division with preorder lemmas"
```

---

### Task 7: Coverings, strong division, refl, glue lemma

**Files:**
- Modify: `KRTheory/TransMon/Division.lean` (append before `end KRTheory`, after the sanity examples of Task 6)

**Interfaces:**
- Consumes: `TransMon`, `trivialTM`, `regular`, `Faithful` (Tasks 4–5); `MonoidDivides` (`≺ₘ`, Task 6).
- Produces:
  - `structure KRTheory.TransMon.Covering (S T : TransMon) : Type` with fields `toSubmonoid : Submonoid T.M`, `stateMap : T.X → S.X`, `monoidMap : toSubmonoid →* S.M`, `stateMap_surj : Function.Surjective stateMap`, `monoidMap_surj : Function.Surjective monoidMap`, `equivariant : ∀ (y : T.X) (n : toSubmonoid), S.act (stateMap y) (monoidMap n) = stateMap (T.act y ↑n)`.
  - `def KRTheory.TransMon.StrongDivides (S T : TransMon) : Prop := Nonempty (Covering S T)`; scoped infix `S ≺ T` at precedence 50.
  - `theorem KRTheory.TransMon.StrongDivides.refl (T : TransMon) : T ≺ T`
  - `theorem KRTheory.TransMon.StrongDivides.monoidDivides : S ≺ T → S.M ≺ₘ T.M`

- [ ] **Step 1: Append statements (RED)**

```lean
namespace TransMon

/-- A covering witnessing strong division `S ≺ T` [DKS §2.3]: a
submonoid of `T.M` mapping onto `S.M`, equivariantly over a state
surjection `T.X ↠ S.X`. A `Type`-valued witness; the `Prop` is
`StrongDivides`. -/
structure Covering (S T : TransMon) : Type where
  /-- The submonoid `N' ≤ T.M` doing the covering. -/
  toSubmonoid : Submonoid T.M
  /-- `φ`: state surjection, from the big machine down to the small. -/
  stateMap : T.X → S.X
  /-- `ψ`: the monoid surjection. -/
  monoidMap : toSubmonoid →* S.M
  stateMap_surj : Function.Surjective stateMap
  monoidMap_surj : Function.Surjective monoidMap
  equivariant : ∀ (y : T.X) (n : toSubmonoid),
    S.act (stateMap y) (monoidMap n) = stateMap (T.act y ↑n)

/-- `S ≺ T`: strong division of transformation monoids [DKS §2.3]. -/
def StrongDivides (S T : TransMon) : Prop := Nonempty (Covering S T)

@[inherit_doc]
scoped infix:50 " ≺ " => StrongDivides

namespace StrongDivides

theorem refl (T : TransMon) : T ≺ T := sorry

/-- Strong division yields division of the underlying monoids — the
lemma through which every abstract corollary is extracted. -/
theorem monoidDivides {S T : TransMon} (h : S ≺ T) : S.M ≺ₘ T.M := sorry

end StrongDivides

-- Sanity checks (spec §6).
example : trivialTM ≺ trivialTM := .refl _
example : (regular (ZMod 3)) ≺ (regular (ZMod 3)) := .refl _
example (h : trivialTM ≺ regular (ZMod 2)) :
    trivialTM.M ≺ₘ (regular (ZMod 2)).M := h.monoidDivides

end TransMon
```

- [ ] **Step 2: Build — statements elaborate**

```bash
lake build 2>&1 | tail -20
```

Expected: two sorry warnings. Watchpoint: the `≺` scoped notation must not clash with anything Mathlib exports into scope (spec §8); if it does, Lean errors here — rename ours stays `≺`, resolve by `open scoped` hygiene or precedence adjustment, and record the outcome in the file's docstring.

- [ ] **Step 3: Prove both (GREEN)**

```lean
theorem refl (T : TransMon) : T ≺ T :=
  ⟨{ toSubmonoid := ⊤
     stateMap := id
     monoidMap := Submonoid.topEquiv.toMonoidHom
     stateMap_surj := Function.surjective_id
     monoidMap_surj := Submonoid.topEquiv.surjective
     equivariant := fun y n => rfl }⟩

theorem monoidDivides {S T : TransMon} (h : S ≺ T) : S.M ≺ₘ T.M := by
  obtain ⟨c⟩ := h
  exact ⟨c.toSubmonoid, c.monoidMap, c.monoidMap_surj⟩
```

(`equivariant := fun y n => rfl`: `Submonoid.topEquiv.toMonoidHom n` should be reducibly `↑n`; if `rfl` fails, use `by simp [Submonoid.topEquiv]` or `Subtype.eta`-style rewriting.)

- [ ] **Step 4: Build clean + no sorry**

```bash
lake build 2>&1 | tail -5 && (grep -rn "sorry" KRTheory/ KRTheory.lean; test $? -eq 1 && echo "clean")
```

Expected: build success, `clean`.

- [ ] **Step 5: Commit**

```bash
git add KRTheory/TransMon/Division.lean
git commit -m "Add coverings and strong division with glue lemma"
```

---

### Task 8: Strong division transitivity

**Files:**
- Modify: `KRTheory/TransMon/Division.lean` (insert after the `end StrongDivides` line of Task 7, before Task 7's sanity examples; both declarations carry qualified names so no namespace re-opening is needed)

**Interfaces:**
- Consumes: `Covering`, `StrongDivides` (Task 7); the comap/map pattern from `MonoidDivides.trans` (Task 6).
- Produces:
  - `def KRTheory.TransMon.Covering.comp : Covering S T → Covering T U → Covering S U` (the composed covering; separate `def` so the data is reusable and the proof reviewable in pieces)
  - `theorem KRTheory.TransMon.StrongDivides.trans : S ≺ T → T ≺ U → S ≺ U`

- [ ] **Step 1: State `Covering.comp` with sorried fields (RED)**

Insert at the position given in **Files** above (`Covering.comp` is data, `trans` is the Prop wrapper):

```lean
/-- Composition of coverings: witnesses transitivity of `≺`.
State maps compose contravariantly (`U.X → T.X → S.X`); the monoid data
is pulled back as in `MonoidDivides.trans`. -/
def Covering.comp {S T U : TransMon}
    (c₁ : Covering S T) (c₂ : Covering T U) : Covering S U where
  toSubmonoid :=
    ((c₁.toSubmonoid.comap c₂.monoidMap).map c₂.toSubmonoid.subtype)
  stateMap := c₁.stateMap ∘ c₂.stateMap
  monoidMap := sorry
  stateMap_surj := sorry
  monoidMap_surj := sorry
  equivariant := sorry

theorem StrongDivides.trans {S T U : TransMon}
    (h₁ : S ≺ T) (h₂ : T ≺ U) : S ≺ U :=
  sorry
```

Build: `lake build 2>&1 | tail -10` — expect sorry warnings only; the `toSubmonoid`/`stateMap` fields must elaborate as given.

- [ ] **Step 2: Fill the data and proofs (GREEN)**

```lean
def Covering.comp {S T U : TransMon}
    (c₁ : Covering S T) (c₂ : Covering T U) : Covering S U where
  toSubmonoid :=
    ((c₁.toSubmonoid.comap c₂.monoidMap).map c₂.toSubmonoid.subtype)
  stateMap := c₁.stateMap ∘ c₂.stateMap
  monoidMap :=
    c₁.monoidMap.comp ((c₂.monoidMap.submonoidComap c₁.toSubmonoid).comp
      (Submonoid.equivMapOfInjective _ c₂.toSubmonoid.subtype
        c₂.toSubmonoid.subtype_injective).symm.toMonoidHom)
  stateMap_surj := c₁.stateMap_surj.comp c₂.stateMap_surj
  monoidMap_surj := by
    apply c₁.monoidMap_surj.comp
    apply Function.Surjective.comp
    · rintro ⟨n, hn⟩
      obtain ⟨u, hu⟩ := c₂.monoidMap_surj n
      exact ⟨⟨u, by simpa [Submonoid.mem_comap, hu] using hn⟩,
        Subtype.ext hu⟩
    · exact (Submonoid.equivMapOfInjective _ _ _).symm.surjective
  equivariant := by
    rintro y ⟨_, ⟨n, hn, rfl⟩⟩
    -- goal: S.act (c₁.stateMap (c₂.stateMap y)) (monoidMap …)
    --     = c₁.stateMap (c₂.stateMap (U.act y ↑n))
    -- chase: apply c₁.equivariant at the T-level, then c₂.equivariant
    -- at the U-level.
    simp only [Function.comp_apply]
    sorry -- REPLACE during execution. Mathematical content: blueprint
          -- lem:sdiv-preorder — rewrite with c₁.equivariant, then
          -- congrArg c₁.stateMap (c₂.equivariant y ⟨↑n, hn⟩). Plumbing
          -- hint: with e := Submonoid.equivMapOfInjective _ _ _, reduce
          -- e.symm ⟨↑q, _⟩ to q via e.symm_apply_apply after showing
          -- e q = ⟨↑q, _⟩ by Subtype.ext rfl; `exact?` for name drift.

theorem StrongDivides.trans {S T U : TransMon}
    (h₁ : S ≺ T) (h₂ : T ≺ U) : S ≺ U := by
  obtain ⟨c₁⟩ := h₁; obtain ⟨c₂⟩ := h₂
  exact ⟨c₁.comp c₂⟩
```

**Note on the remaining `sorry` inside `equivariant`:** the two-step chase is mathematically trivial (blueprint `lem:sdiv-preorder`) but its Lean form depends on how `equivMapOfInjective` computes, which is best discovered interactively. This task is NOT done while it remains: work it out with `simp only [...]`, `Subtype.ext_iff`, and `exact?`; if `equivMapOfInjective` proves unwieldy, replace the `monoidMap` construction with a direct `MonoidHom.mk'` on the mapped submonoid (define the function by choosing the preimage via `Classical.choose` of membership, or restate `toSubmonoid` as `Submonoid.comap` composed differently) — any construction is acceptable provided the four `Covering` fields hold and the statement of `StrongDivides.trans` is unchanged.

- [ ] **Step 3: Sanity example**

Append after `end StrongDivides`:

```lean
example {S T U : TransMon} (h₁ : S ≺ T) (h₂ : T ≺ U) : S ≺ U :=
  h₁.trans h₂
```

- [ ] **Step 4: Build clean + no sorry**

```bash
lake build 2>&1 | tail -5 && (grep -rn "sorry" KRTheory/ KRTheory.lean; test $? -eq 1 && echo "clean")
```

Expected: build success, `clean`. **The grep gate is hard**: Step 2's placeholder sorry must be gone.

- [ ] **Step 5: Update blueprint checkmarks**

In `blueprint/src/chapters/division.tex`, add `\leanok` to `def:mdiv`, `lem:mdiv-preorder`, `def:sdiv`, `lem:sdiv-preorder`, `lem:sdiv-mdiv`.

- [ ] **Step 6: Commit**

```bash
git add KRTheory/TransMon/Division.lean blueprint/src/chapters/division.tex
git commit -m "Add strong division transitivity via covering composition"
```

---

### Task 9: Milestone acceptance sweep

**Files:**
- Modify: none expected (fixes only if the sweep finds problems)

**Interfaces:**
- Consumes: everything above.
- Produces: verified milestone 0–2 state matching spec §7 acceptance rows 0–2.

- [ ] **Step 1: Full clean-ish rebuild and sorry/axiom audit**

```bash
lake build 2>&1 | tail -3
grep -rn "sorry\|admit\|native_decide" KRTheory/ KRTheory.lean; test $? -eq 1 && echo "no escape hatches"
```

Expected: build success; `no escape hatches`.

- [ ] **Step 2: Axiom spot-check**

Create a scratch file `KRTheory/Scratch.lean` (do NOT import from root, do NOT commit):

```lean
import KRTheory.TransMon.Division
open KRTheory KRTheory.TransMon
#print axioms KRTheory.MonoidDivides.trans
#print axioms KRTheory.TransMon.StrongDivides.trans
```

```bash
lake env lean KRTheory/Scratch.lean && rm KRTheory/Scratch.lean
```

Expected: each line lists at most `Classical.choice`, `propext`, `Quot.sound` (spec §1.4).

- [ ] **Step 3: Spec acceptance check (milestones 0–2)**

Confirm against spec §7: `lake build` green (M0) ✓; blueprint sources exist and compile-or-skip cleanly (M0) ✓; `TransMon` examples pass and `regular_faithful` proved (M1) ✓; both preorders + glue lemma proved (M2) ✓. Any miss = fix before proceeding.

- [ ] **Step 4: Commit anything the sweep fixed; otherwise no commit**

```bash
git status --short
```

Expected: empty (Scratch.lean removed).

---

## Self-review record (per writing-plans skill)

- **Spec coverage (milestones 0–2):** M0 scaffold = Tasks 1–3 (lake ✓ CI ✓ blueprint ✓; git init already done at spec commit). M1 = Tasks 4–5 (structure, instances, notation, trivialTM, Faithful, regular, regular_faithful, examples). M2 = Tasks 6–8 (`≺ₘ` + preorder + feeders, `Covering`/`≺` + refl + glue, trans). Acceptance = Task 9. Not in scope here (deliberately): wreath products onward — next plan.
- **Placeholder scan:** one intentional interactive-discovery point (Task 8 `equivariant` chase) — explicitly gated by the hard no-sorry check in Task 8 Step 4, with fallback construction specified. No other TBDs.
- **Type consistency:** `TransMon` field names (`X`, `M`, `act`), `Covering` field names (`toSubmonoid`, `stateMap`, `monoidMap`, `*_surj`, `equivariant`), and notation precedences (both `≺ₘ` and `≺` at 50, `⊳` at 65/66) are used identically across Tasks 4–9 and match the blueprint's `\lean{}` names (Task 3).
