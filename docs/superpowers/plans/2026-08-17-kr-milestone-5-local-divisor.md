# Krohn–Rhodes Milestone 5 (Local Divisors) Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Prove the three load-bearing local-divisor lemmas ([DKS] 2.13 faithfulness, cardinality drop, division) on a `Finite`-bundled `TransMon`, with the repo published to GitHub and CI certifying build + axioms + blueprint.

**Architecture:** Foundation first: publish the known-good M0–4 state and get a CI baseline (Task 1), harden CI (Task 2), clear the ruled housekeeping (Task 3), then execute the §4.1 amendment — swap the bundled `Fintype` fields to `Finite` (Task 4). On that foundation: blueprint chapters (Task 5), `FiniteMonoid.lean` prelims (Task 6, **user-written carve-out**), and `LocalDivisor.lean` in three slices (Tasks 7–9: monoid, transformation monoid + 2.13, card-lt + divides). Task 10 closes the milestone.

**Tech Stack:** Lean 4 (`v4.34.0-rc1` toolchain), Mathlib pinned at `ac4c4bff` via `lake-manifest.json`, GitHub Actions `lean-action`, LaTeX (`print.tex` fallback preamble). Base code: branch `milestone-4` after the spec amendment `e38a716` and this plan's commit; implementation happens on a new `milestone-5` branch.

**Spec:** `docs/superpowers/specs/2026-08-17-krohn-rhodes-formalization-design.md` — §3.6 (local divisors), §4.1 **as amended 2026-08-17** (`Finite` bundling), §4.3 rows `FiniteMonoid.lean` / `TransMon/LocalDivisor.lean`, §7 row 5 acceptance ("2.13 + card-lt + divides proved; CI green on published repo").

## Global Constraints

- All Lean code inside `namespace KRTheory` (and `TransMon` where stated); notation scoped; carriers in `Type`.
- **`Finite`, never `Fintype`, in bundled positions** (spec §4.1 as amended). Cardinality talk is `Nat.card`; concrete computations bridge via `Nat.card_eq_fintype_card` + native instances. Conditional `Fintype`/`DecidableEq` instances on bare type parameters (`Resets X`, `BarMonoid T`) stay — they serve `decide`.
- Docstrings on every new public declaration, including instances; module docstrings cite [DKS §2.5] and blueprint labels.
- Guard-example discipline (spec §6): every asymmetric operation gets an example a transposed definition would fail, with a comment naming the wrong definition it kills.
- Zero-warning builds; no `sorry`/`admit`/`native_decide`; plain commit messages, no trailers.
- Formalization-TDD: RED = statements + `sorry` stubs + examples elaborate; GREEN = proofs in, `grep -rn "sorry" KRTheory/ KRTheory.lean` empty.
- Established elaboration repairs when goals stall at projected types: `show` the defeq-unfolded goal, then rewrite with concrete hypotheses (documented in `Wreath.lean` mirror-kit and `Reset.lean` §preamble).
- New `Classical.choose` may appear **only** inside `LocalDivisor.lean`'s two definitional sites (`mul`, `act`); every downstream proof goes through the `*_spec` characterization lemmas. (`Covering.extMap` in `Division.lean` is the existing, similarly quarantined use.)

## Decisions this plan records

1. **Verified against the pinned Mathlib (planning-session probes):** `mul_eq_one_comm : a * b = 1 ↔ b * a = 1` and `IsUnit.of_mul_eq_one_right` exist for `[Monoid M] [Finite M]` — the spec §3.6 "one-sided inverse ⇒ unit" prelim is Mathlib-supplied, not ours to write. `Nat.card_eq_one_iff_unique`, `Finite.injective_iff_surjective`, `Finite.exists_ne_map_eq_of_infinite`, `Finite.one_lt_card_iff_nontrivial` all exist. `Nat.card_subtype_lt` does **not** exist — Task 4 adds it (upstream candidate, spec §9).
2. **Dropped:** a `Trans` instance for `≺ₘ` (suggested in the pre-M5 review) is not statable: `Trans` takes a bare relation `α → β → Sort u`, and `MonoidDivides` has `[Monoid _]` binders between its arguments. `≺ₘ` chains use `.trans`; Task 3 leaves a comment saying so.
3. **Deferred:** `isUnit_of_generators_units` (spec §4.3) is only consumed by the M8 induction; blueprint states it `\notready`, Lean waits for M8 (YAGNI).
4. The monoid carrier is a fresh one-field-plus-proofs structure `LocalDivisor c`, **not** a raw subtype: its product is *not* the restriction of `M`'s product ((mc)∘(cn) = mcn ≠ mc·cn), so planting a `Monoid` instance on a subtype of `M` would be a diamond trap — same rationale as `WreathMonoid`/`BarMonoid`/`Resets`.
5. `resetMonoid_div_flipFlop_of_card_one` and `reset_div_flipFlops` restate their cardinality hypotheses with `Nat.card`; `reset_div_flipFlops`' final step becomes a `calc … _ = … := by rw [List.replicate_succ']` step (core provides `Trans r Eq r`; the contrary comment at `Reset.lean:408` was wrong — verified by compilation).

---

### Task 1: Publish the repo and establish the CI baseline

**Files:** none (git/GitHub state only). Remote `origin = git@github.com:juanbono/krohn-rhodes-theory.git` already added by the user.

**Interfaces:**
- Consumes: the milestone-4 branch containing spec amendment `e38a716` and this plan's commit.
- Produces: `main` fast-forwarded to the milestone-4 tip; all branches pushed; one green Actions run on `main`; local branch `milestone-5` for all subsequent tasks.

- [ ] **Step 1: Fast-forward `main` and push everything**

```bash
git checkout main
git merge --ff-only milestone-4
git push -u origin main
git push -u origin milestones-0-2 milestone-3 milestone-4
```

`--ff-only` is a safety check: the stack is one straight line, so anything but a fast-forward means the world changed — stop and look.

- [ ] **Step 2: Watch the first CI run**

```bash
gh run list --limit 3
gh run watch
```

Expected: the `build` job (checkout + `lean-action`) goes green — first Mathlib cache fetch makes this slow (~10–20 min). If `gh` is absent, check the Actions tab in the browser. A red run here is a stop-the-line event: diagnose (usually toolchain/cache), do not proceed on red.

- [ ] **Step 3: Create the implementation branch**

```bash
git checkout milestone-4
git checkout -b milestone-5
```

No commit in this task.

---

### Task 2: CI hardening — axiom certificate, blueprint build, concurrency

**Files:**
- Modify: `.github/workflows/ci.yml`
- Create: `scripts/AxiomCertificate.lean`
- Modify: `blueprint/src/print.tex` (the `\lean` macro — load-bearing here: the blueprint job cannot pass without it)

**Interfaces:**
- Consumes: nothing from other tasks.
- Produces: CI jobs later tasks rely on; `scripts/AxiomCertificate.lean`, which Task 10 extends with the M5 theorems.

- [ ] **Step 1: Fix the `\lean` print-fallback macro**

In `blueprint/src/print.tex`, replace

```latex
\newcommand{\lean}[1]{\marginpar{\tiny\texttt{#1}}}
```

with

```latex
\newcommand{\lean}[1]{\marginpar{\tiny\ttfamily\detokenize{#1}}}
```

Why: `\texttt` typesets the raw name in text mode, where `_` is catcode 8 — every underscored Lean name (first: `\lean{KRTheory.TransMon.regular_faithful}`) kills `latexmk` with "Missing $ inserted". `\detokenize` prints the argument verbatim. No local TeX exists to verify; the CI job in Step 3 is the test rig.

- [ ] **Step 2: Write the axiom certificate script**

Create `scripts/AxiomCertificate.lean`:

```lean
import KRTheory

open KRTheory KRTheory.TransMon

/-! One `#print axioms` per milestone-terminal theorem. CI parses the
output and fails on any axiom outside {propext, Classical.choice,
Quot.sound} (spec §1 item 4). Extend this list as milestones land. -/

#print axioms regular_faithful
#print axioms StrongDivides.trans
#print axioms StrongDivides.wreath
#print axioms wreath_assoc_div
#print axioms wreathList_append
#print axioms bar_divides
#print axioms reset_split
#print axioms reset_div_flipFlops
```

- [ ] **Step 3: Rewrite the workflow**

Replace `.github/workflows/ci.yml` with:

```yaml
name: CI

on:
  push:
    branches: [main]
  pull_request:

concurrency:
  group: ${{ github.workflow }}-${{ github.ref }}
  cancel-in-progress: true

jobs:
  build:
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v4
      - uses: leanprover/lean-action@v1
      - name: Axiom certificate
        run: |
          lake env lean scripts/AxiomCertificate.lean | tee axioms.out
          test -s axioms.out
          python3 - <<'EOF'
          import re, sys
          allowed = {"propext", "Classical.choice", "Quot.sound"}
          bad = False
          for line in open("axioms.out"):
              m = re.search(r"depends on axioms: \[(.*)\]", line)
              if m:
                  extra = {a.strip() for a in m.group(1).split(",")} - allowed
                  if extra:
                      print("DISALLOWED:", extra, "<-", line.strip())
                      bad = True
          sys.exit(1 if bad else 0)
          EOF

  blueprint:
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v4
      - name: Install TeX
        run: |
          sudo apt-get update
          sudo apt-get install -y --no-install-recommends texlive-latex-extra latexmk
      - name: Build blueprint PDF
        run: latexmk -pdf -interaction=nonstopmode print.tex
        working-directory: blueprint/src
      - name: Upload PDF
        uses: actions/upload-artifact@v4
        with:
          name: blueprint-pdf
          path: blueprint/src/print.pdf
```

- [ ] **Step 4: Verify locally what can be verified locally**

```bash
lake env lean scripts/AxiomCertificate.lean
```

Expected: eight lines, each ending `[propext, Classical.choice, Quot.sound]`.

- [ ] **Step 5: Commit, push, open a draft PR so CI runs per push**

```bash
git add .github/workflows/ci.yml scripts/AxiomCertificate.lean blueprint/src/print.tex
git commit -m "Add axiom-certificate and blueprint CI jobs; fix lean macro for underscores"
git push -u origin milestone-5
gh pr create --draft --base main --title "Milestone 5: local divisors" \
  --body "Tracking PR so CI runs per push. Merge policy stays manual."
gh pr checks --watch
```

Expected: both jobs green on the PR. The blueprint job failing on a *TeX packaging* issue (missing `.sty`) means widen the apt package list (`texlive-latex-extra` → add `texlive-fonts-recommended`); failing on an *underscore* error means Step 1 regressed.

---

### Task 3: Lean housekeeping bundle (ruled at M4 close + pre-M5 review additions)

**Files:**
- Modify: `KRTheory/TransMon/Reset.lean`, `KRTheory/TransMon/Division.lean`, `KRTheory/TransMon/Bar.lean`

All items are docs/comments plus one dead tactic — no statement changes. The spec-side renames were already fixed by amendment `e38a716`. The `Reset.lean:408` comment and calc shape are **not** touched here — Task 4 rewrites that proof wholesale (Decision 5).

**Interfaces:** none produced; keep each item byte-small.

- [ ] **Step 1: `Reset.lean` doc nits**

  1. Module docstring (`:7–19`): after the sentence introducing `reset_split`, add: `The file closes with the DKS 2.12 induction itself (\`reset_div_flipFlops\`), peeling one state per flip-flop factor.`
  2. Section preamble (`:113` area): "The four private helpers below" → "The five private helpers below" (`to_ne_id`, `splitState`, `splitMap`, `splitSub`, `splitCovering`).
  3. `splitSub` docstring (`:168` area): "together they are exactly closure under the twisted multiplication" → "together they are closed under the twisted multiplication and are precisely what `splitMap` needs to be a homomorphism".
  4. `splitCovering.monoidMap.map_mul'` (`:235`): above `rintro ⟨w, -, -, -⟩ ⟨w', hw1', hw2', hw3'⟩` add comment: `-- The left factor's membership conditions are discarded: the product's value only reads w.left true and w.right, and it is w'’s conditions that decide which splitMap branch fires.`

- [ ] **Step 2: `Reset.lean` dead tactic**

`Resets.mul_assoc` (`:40`): `by cases c <;> cases b <;> rfl` → `by cases c <;> rfl`. (The multiplication only matches on its right argument, so casing `b` splits goals that were already `rfl`.)

- [ ] **Step 3: `Division.lean` — restore the section docstring and record the calc fact**

  1. Above `Covering.stateMap_sect` (`:225`):

```lean
/-- The defining property of the section: `stateMap` retracts it. -/
```

  2. Below the `scoped infix:50 " ≺ₘ "` declaration, add:

```lean
-- No `Trans` instance (hence no `calc` support) is possible for `≺ₘ`:
-- `Trans` wants a bare relation `α → β → Sort u`, and `MonoidDivides`
-- carries `[Monoid _]` binders between its arguments. Chains use `.trans`.
-- (`≺` on `TransMon` has no such binders; it does get `calc` support.)
```

- [ ] **Step 4: `Bar.lean` — DecidableEq docstring note**

Append to the `DecidableEq (BarMonoid T)` instance docstring (`:95–104`): `At semireducible concrete transformation monoids the conditional hypotheses are not found by search on the projected types; bridge with e.g. \`inferInstanceAs (DecidableEq (BarMonoid (regular (ZMod 3))))\` after a \`show\` at the unfolded type.`

- [ ] **Step 5: Build, verify, commit**

```bash
lake build 2>&1 | tail -3
git add KRTheory
git commit -m "Housekeeping: M4-ruled doc nits, dead cases b, calc-support note"
```

Expected: green, zero warnings.

---

### Task 4: The `Finite` swap (spec §4.1 amendment executed)

**Files:**
- Modify: `KRTheory/TransMon/Basic.lean`, `KRTheory/TransMon/Wreath.lean`, `KRTheory/TransMon/Bar.lean`, `KRTheory/TransMon/Reset.lean`, `KRTheory.lean`
- Create: `KRTheory/FiniteMonoid.lean` (seeded with `Nat.card_subtype_lt` only; Task 6 extends it)
- Unchanged by design (verify they still build): `Division.lean`, `WreathDivision.lean` — neither mentions finiteness.

**Interfaces:**
- Produces: `TransMon` with `[finiteX : Finite X]` / `[finiteM : Finite M]` instance fields; `Nat.card_subtype_lt {p : α → Prop} {x} (hx : ¬ p x) : Nat.card {a // p a} < Nat.card α` (for `[Finite α]`); `Resets.instFinite [Finite X] : Finite (Resets X)`; `resetMonoid` / `reset_split` / `reset_div_flipFlops` / `resetMonoid_div_flipFlop_of_card_one` restated over `Finite`/`Nat.card` (exact signatures below — Tasks 7–9 and M6+ consume them).

- [ ] **Step 1: Seed `KRTheory/FiniteMonoid.lean`**

```lean
import Mathlib.Tactic

/-!
# Finite monoid preliminaries

Counting and unit lemmas for finite monoids [spec §3.6 prelims,
blueprint ch. `ch:finitemonoid`]. Mathlib already provides the
one-sided-inverse lemmas (`mul_eq_one_comm`,
`IsUnit.of_mul_eq_one_right`); this file holds what it lacks.
Upstream candidates (spec §9).
-/

namespace KRTheory

/-- A predicate that fails somewhere carves out a strictly smaller
subtype. `Nat.card` analogue of `Fintype.card_subtype_lt`
[blueprint `lem:card-subtype-lt`]. -/
theorem Nat.card_subtype_lt {α : Type} [Finite α] {p : α → Prop} {x : α}
    (hx : ¬ p x) : Nat.card {a // p a} < Nat.card α := by
  have : Fintype α := Fintype.ofFinite α
  classical
  simpa [Nat.card_eq_fintype_card] using
    Fintype.card_subtype_lt (p := p) (x := x) hx

end KRTheory
```

Add `import KRTheory.FiniteMonoid` as the **first** import in `KRTheory.lean`.

Note: inside `namespace KRTheory` this declares `KRTheory.Nat.card_subtype_lt`; call sites in the namespace write `Nat.card_subtype_lt` unqualified. If root-`Nat` ambiguity bites at a call site, qualify as `KRTheory.Nat.card_subtype_lt`.

- [ ] **Step 2: `Basic.lean`**

Structure fields and attribute:

```lean
  /-- `X` is finite. -/
  [finiteX : Finite X]
  /-- `M` has a monoid structure. -/
  [monoidM : Monoid M]
  /-- `M` is finite. -/
  [finiteM : Finite M]
```

```lean
attribute [instance] finiteX monoidM finiteM
```

`regular` and `regular_faithful` hypotheses: `[Monoid M] [Fintype M]` → `[Monoid M] [Finite M]`.

Card examples (the `show` line is the standard semireducible repair — instance search will not unfold `trivialTM.X` to `PUnit`):

```lean
example : Nat.card trivialTM.X = 1 := by
  show Nat.card PUnit = 1
  exact Nat.card_unique
example : Nat.card trivialTM.M = 1 := by
  show Nat.card PUnit = 1
  exact Nat.card_unique
example : Nat.card (regular (ZMod 3)).X = 3 := by
  show Nat.card (ZMod 3) = 3
  rw [Nat.card_eq_fintype_card, ZMod.card]
```

The action examples (`rfl` on `act`) are untouched.

- [ ] **Step 3: `Wreath.lean`**

Delete `noncomputable` from `wreath` and `wreathList`; delete the line `fintypeM := Fintype.ofFinite _` (the `Finite (WreathMonoid S T)` instance already present fills the field via search). Rewrite the `wreath` docstring's computability sentence to: `Computable — under the 2026-08-17 §4.1 amendment the bundled finiteness is the Prop-valued `Finite`, so there is no data field to obstruct it.`

Replace the 8-element example:

```lean
example :
    Nat.card (WreathMonoid (regular (ZMod 2)) (regular (ZMod 2))) = 8 := by
  rw [WreathMonoid.natCard]
  show Nat.card (ZMod 2) ^ Nat.card (ZMod 2) * Nat.card (ZMod 2) = 8
  rw [Nat.card_eq_fintype_card, ZMod.card]
```

- [ ] **Step 4: `Bar.lean`**

```lean
/-- `BarMonoid T` is finite, transported from the `Finite (T.M ⊕ T.X)`
instance across `equivSum`. -/
instance : Finite (BarMonoid T) := Finite.of_equiv _ equivSum.symm
```

(replaces the `Fintype` instance). The conditional `DecidableEq` instance stays. Replace the 6-element example:

```lean
example : Nat.card (BarMonoid (regular (ZMod 3))) = 6 := by
  rw [BarMonoid.natCard]
  show Nat.card (ZMod 3) + Nat.card (ZMod 3) = 6
  rw [Nat.card_eq_fintype_card, ZMod.card]
```

- [ ] **Step 5: `Reset.lean`**

  1. Keep the conditional `Fintype`/`DecidableEq` instances (they serve `decide` at concrete types); **add** below them:

```lean
/-- `Resets X` is finite whenever `X` is, transported across
`equivOption`. Prop-level counterpart of the `Fintype` instance above;
this is what the bundled `TransMon` fields consume. -/
instance [Finite X] : Finite (Resets X) := Finite.of_equiv _ equivOption.symm
```

  2. Hypothesis swaps `[Fintype _]` → `[Finite _]` on: `Resets.natCard`, `resetMonoid`, `resetMonoid_act_id`, `resetMonoid_act_to`, `splitSub`, `splitCovering`.
  3. `reset_split`: delete `open scoped Classical in`; hypothesis `[Finite X]`. Replace the docstring's classical-recipe paragraph with: `Under the amended §4.1 bundling, \`Finite {x : X // x ≠ x₀}\` is found by plain instance search (\`Subtype.finite\` needs no decidability); the classical statement decoration and the callers' \`convert\`-plus-\`Subsingleton (Fintype _)\` repair that the original \`Fintype\` bundling forced are gone.`
  4. The `U(2) ≺ U(1) ≀ U(2)` sanity example: `convert reset_split Bool true` → `exact reset_split Bool true`; rewrite its comment: `-- \`exact\` now suffices: \`Finite\` is a Prop, so there is no instance data to mismatch.`
  5. Base case, restated over `Nat.card`:

```lean
theorem resetMonoid_div_flipFlop_of_card_one (X : Type) [Finite X]
    (h : Nat.card X = 1) : resetMonoid X ≺ flipFlop := by
  obtain ⟨hsub, ⟨pt⟩⟩ := Nat.card_eq_one_iff_unique.mp h
  have hpt : ∀ x : X, x = pt := fun x => Subsingleton.elim x pt
  -- body unchanged from here down (it only ever used `pt` and `hpt`)
```

  6. The induction, restated over `Nat.card` — full replacement (note the `classical` line is gone, and the final calc uses the now-verified `=`-step, deleting the wrong comment; the `-- N = 1` comment is updated to cite `Nat.card_pos`):

```lean
theorem reset_div_flipFlops (X : Type) [Finite X] [Nonempty X] :
    ∃ n : ℕ, resetMonoid X ≺ wreathList (List.replicate n flipFlop) := by
  generalize hcard : Nat.card X = N
  induction N using Nat.strong_induction_on generalizing X with
  | _ N ih =>
    rcases Nat.lt_or_ge N 2 with hN | hN
    · -- N = 1 (N = 0 contradicts Nonempty: Nat.card_pos gives card ≥ 1)
      have h1 : Nat.card X = 1 := by
        have := Nat.card_pos (α := X); omega
      exact ⟨1, (resetMonoid_div_flipFlop_of_card_one X h1).trans
        (div_wreathList_singleton flipFlop)⟩
    · obtain ⟨x₀⟩ := ‹Nonempty X›
      have : Nonempty {x : X // x ≠ x₀} := by
        have hnt : Nontrivial X :=
          Finite.one_lt_card_iff_nontrivial.mp (by omega)
        obtain ⟨y, hy⟩ := exists_ne x₀
        exact ⟨⟨y, hy⟩⟩
      obtain ⟨n, hn⟩ := ih (Nat.card {x : X // x ≠ x₀})
        (by
          have := Nat.card_subtype_lt (α := X) (p := (· ≠ x₀))
            (x := x₀) (by simp)
          omega)
        {x : X // x ≠ x₀} rfl
      refine ⟨n + 1, ?_⟩
      calc resetMonoid X
          ≺ resetMonoid {x : X // x ≠ x₀} ≀ flipFlop := reset_split X x₀
        _ ≺ wreathList (List.replicate n flipFlop) ≀ wreathList [flipFlop] :=
            hn.wreath (div_wreathList_singleton flipFlop)
        _ ≺ wreathList (List.replicate n flipFlop ++ [flipFlop]) :=
            wreathList_append _ _
        _ = wreathList (List.replicate (n + 1) flipFlop) := by
            rw [List.replicate_succ']
```

  7. The flip-flop 3-element and 27-element examples already go through `show` + concrete `Nat.card_eq_fintype_card` at `Resets Bool`/`Bool` with native `Fintype` instances — untouched; if elaboration of the conditional `Fintype (Resets Bool)` stalls, the `Bar.lean` `inferInstanceAs` bridge note (Task 3 Step 4) is the repair.

  8. Module docstring `:14`: "Everything here is computable." now holds without a hedge — extend to: `Everything here is computable, including (post-§4.1-amendment) the statement of \`reset_split\`.`

- [ ] **Step 6: Build, audit, grep-guard, commit**

```bash
lake build 2>&1 | tail -3
lake env lean scripts/AxiomCertificate.lean
grep -rn "noncomputable" KRTheory/TransMon/Wreath.lean
grep -rn "Fintype" KRTheory/ | grep -v "Nat.card_eq_fintype_card" \
  | grep -v "Fintype.ofFinite" | grep -v "Fintype.card_subtype_lt"
```

Expected: green build, certificate lines unchanged (`[propext, Classical.choice, Quot.sound]`), **no** `noncomputable` left in `Wreath.lean`, and the `Fintype` grep shows only `Reset.lean`'s conditional instances (`[Fintype X]`, `[DecidableEq X]` block). Commit:

```bash
git add KRTheory KRTheory.lean
git commit -m "Swap bundled Fintype fields to Finite per amended spec 4.1"
git push
```

CI on the draft PR must be green before Task 5.

---

### Task 5: Blueprint chapters (informal math first, spec §6 discipline)

**Files:**
- Create: `blueprint/src/chapters/finitemonoid.tex`, `blueprint/src/chapters/localdivisor.tex`
- Modify: `blueprint/src/content.tex` (two `\input` lines after `chapters/reset`)

**Interfaces:**
- Produces: labels `ch:finitemonoid`, `lem:finite-unit`, `lem:idem-pow`, `lem:card-subtype-lt`, `ch:localdivisor`, `def:localdiv`, `def:localdiv-tm`, `lem:localdiv-faithful`, `lem:localdiv-card`, `lem:localdiv-divides` — Tasks 6–9 cite them in docstrings; Task 10 stamps `\leanok`.

- [ ] **Step 1: `finitemonoid.tex`**

```latex
\chapter{Finite monoid preliminaries}\label{ch:finitemonoid}

\begin{lemma}[One-sided inverses]\label{lem:finite-unit}
  \lean{mul_eq_one_comm, IsUnit.of_mul_eq_one_right}
  In a finite monoid, $ab = 1$ implies $ba = 1$; in particular either
  one-sided inverse relation makes both factors units. (Supplied by
  Mathlib; recorded because the cardinality bound
  Lemma~\ref{lem:localdiv-card} hinges on it.)
\end{lemma}
\begin{proof}
  $x \mapsto bx$ is injective ($a$ retracts it: $a(bx) = (ab)x = x$),
  hence surjective by finiteness; a preimage $q$ of $1$ gives $bq = 1$,
  and $q = (ab)q = a(bq) = a$, so $ba = 1$.
\end{proof}

\begin{lemma}[Idempotent power]\label{lem:idem-pow}
  \lean{KRTheory.exists_pow_idempotent}
  Every element $a$ of a finite monoid has a power $a^n$ with
  $n \ge 1$ and $a^n a^n = a^n$.
\end{lemma}
\begin{proof}
  Pigeonhole on $n \mapsto a^n$ gives $i < j$ with $a^i = a^j$; put
  $p := j - i \ge 1$. Then $a^{i+t+p} = a^{i+p} a^t = a^i a^t =
  a^{i+t}$ for every $t$, hence by induction
  $a^{i+t+mp} = a^{i+t}$ for every $m$. Take $n := p(i+1)$: then
  $n \ge i$, so writing $n = i + t_0$ we get
  $a^{2n} = a^{i + t_0 + (i+1)p} = a^{i+t_0} = a^n$.
\end{proof}

\begin{lemma}[Strict subtype count]\label{lem:card-subtype-lt}
  \lean{KRTheory.Nat.card_subtype_lt}
  A predicate on a finite type that fails at some point carves out a
  strictly smaller subtype.
\end{lemma}
\begin{proof}
  Transport of the corresponding \texttt{Fintype} fact along a
  classically chosen enumeration.
\end{proof}

\begin{remark}[Deferred to milestone 8]
  \notready
  The remaining \S 3.6 preliminary — a monoid generated by units is a
  group — is consumed only by the main induction and is deliberately
  not formalized yet.
\end{remark}
```

- [ ] **Step 2: `localdivisor.tex`**

```latex
\chapter{Local divisors}\label{ch:localdivisor}

\begin{definition}[Local divisor]\label{def:localdiv}
  \lean{KRTheory.TransMon.LocalDivisor}
  For $c \in M$: carrier $M_c := cM \cap Mc$, product
  $(mc) \circ (cn) := mcn$, identity $c$. Well defined: if
  $u = mc = m'c$ and $v = cn$, then
  $mv = m(cn) = (mc)n = un = (m'c)n = m'v$ — the product depends only
  on $u$ and $v$, not on the chosen decomposition. Note $\circ$ is
  \emph{not} the restriction of the ambient product.
\end{definition}

\begin{definition}[Local divisor as a transformation monoid]
  \label{def:localdiv-tm}
  \lean{KRTheory.TransMon.localDivisor}
  \uses{def:localdiv,def:transmon}
  For a transformation monoid $(X, M)$ and $c \in M$: states
  $X_c := X \cdot c$, action $\xi \circ (cm) := \xi \cdot m$. Well
  defined and lands in $X_c$: writing $\xi = y \cdot c$ and
  $u = cm = m'c$, we get
  $\xi \cdot m = y \cdot (cm) = y \cdot (m'c) = (y \cdot m') \cdot c$.
\end{definition}

\begin{lemma}[{[DKS] 2.13}: faithfulness]\label{lem:localdiv-faithful}
  \lean{KRTheory.TransMon.localDivisor_faithful}
  \uses{def:localdiv-tm,def:faithful}
  If $(X, M)$ is faithful, so is $(X_c, M_c)$.
\end{lemma}
\begin{proof}
  Let $u = cm_u$, $v = cm_v$ in $M_c$ act equally on all of $X_c$. For
  every $x \in X$: $x \cdot u = (x \cdot c) \cdot m_u =
  (x \cdot c) \circ u = (x \cdot c) \circ v = x \cdot v$, and
  faithfulness of $(X, M)$ gives $u = v$.
\end{proof}

\begin{lemma}[Cardinality drop]\label{lem:localdiv-card}
  \lean{KRTheory.TransMon.localDivisor_card_lt}
  \uses{def:localdiv,lem:finite-unit,lem:card-subtype-lt}
  If $c$ is not a unit, then $|M_c| < |M|$.
\end{lemma}
\begin{proof}
  $1 \notin M_c$: from $1 = cm$ finiteness (Lemma~\ref{lem:finite-unit})
  makes $c$ a unit. So the carrier misses $1$ and
  Lemma~\ref{lem:card-subtype-lt} applies.
\end{proof}

\begin{lemma}[Division]\label{lem:localdiv-divides}
  \lean{KRTheory.TransMon.localDivisor_divides}
  \uses{def:localdiv,def:mdiv}
  $M_c \prec_m M$. This is what makes the strong form of Krohn--Rhodes
  survive recursion: simple groups produced inside $M_c$ divide $M_c$,
  hence divide $M$.
\end{lemma}
\begin{proof}
  $N := \{\, m \mid cm \in Mc \,\}$ is a submonoid of $M$
  ($c1 = 1c$; if $cm = m_2 c$ and $cn = n_2 c$ then
  $c(mn) = m_2 c n = m_2 n_2 c$), and $\psi(m) := cm$ is a
  homomorphism $N \to M_c$: $\psi(m)\circ\psi(n) = (m_2 c)\circ(cn)
  = m_2 c n = c(mn) = \psi(mn)$, with $\psi(1) = c$ the identity of
  $M_c$. Surjectivity: $u = cm = m_2 c \in M_c$ gives $m \in N$ and
  $\psi(m) = u$.
\end{proof}
```

- [ ] **Step 3: Wire into `content.tex`, push, let CI's blueprint job verify the LaTeX**

Append after `\input{chapters/reset}`:

```latex
\input{chapters/finitemonoid}
\input{chapters/localdivisor}
```

```bash
git add blueprint/src
git commit -m "Add finite-monoid and local-divisor blueprint chapters"
git push
gh pr checks --watch
```

Expected: blueprint job green (this is the LaTeX test rig — no local TeX).

---

### Task 6: `FiniteMonoid.lean` — the idempotent-power lemma (USER CARVE-OUT)

**Files:**
- Modify: `KRTheory/FiniteMonoid.lean`

**Interfaces:**
- Consumes: `Finite.exists_ne_map_eq_of_infinite`, `IsIdempotentElem` (Mathlib, probe-verified).
- Produces: `KRTheory.exists_pow_idempotent (a : M) : ∃ n : ℕ, 0 < n ∧ IsIdempotentElem (a ^ n)` for `[Monoid M] [Finite M]` — not consumed until M7; built now per spec §4.3 and for its learning value.

**Process note (project charter):** this task is the milestone's learning carve-out. Scaffold the statement + stub (RED), hand the proof to the user with the blueprint proof (`lem:idem-pow`) as the guide, and only fall back to the reference proof below if they ask for it. The reference proof is untested against the compiler; treat it as a map, not a rail.

- [ ] **Step 1 (RED): statement + stub + examples elaborate**

Append to `KRTheory/FiniteMonoid.lean` inside `namespace KRTheory`:

```lean
variable {M : Type} [Monoid M] [Finite M]

/-- Every element of a finite monoid has an idempotent power `a ^ n`,
`n ≥ 1` [blueprint `lem:idem-pow`]. Pigeonhole gives `a ^ i = a ^ j`
with `i < j`; the period `p := j - i` then absorbs (`a ^ (k + p) =
a ^ k` for `k ≥ i`), and `n := p * (i + 1)` is a multiple of `p` at
least `i`. -/
theorem exists_pow_idempotent (a : M) :
    ∃ n : ℕ, 0 < n ∧ IsIdempotentElem (a ^ n) := by
  sorry

-- Sanity (spec §6): in `ZMod 4`, the element `2` squares to `0`, and
-- `0` is idempotent; `exists_pow_idempotent` must therefore be
-- satisfiable at `n = 2` — witness check, plus the generic call.
example : IsIdempotentElem ((2 : ZMod 4) ^ 2) := by
  -- `show` unfolds the semireducible `IsIdempotentElem` so `decide`
  -- finds its `Decidable` instance at the bare equation
  show (2 : ZMod 4) ^ 2 * (2 : ZMod 4) ^ 2 = (2 : ZMod 4) ^ 2
  decide
example : ∃ n : ℕ, 0 < n ∧ IsIdempotentElem ((2 : ZMod 4) ^ n) :=
  exists_pow_idempotent 2
```

Run `lake build` — must elaborate with exactly the one `sorry` warning.

- [ ] **Step 2 (GREEN, user-first): prove it**

Reference proof (fallback only):

```lean
theorem exists_pow_idempotent (a : M) :
    ∃ n : ℕ, 0 < n ∧ IsIdempotentElem (a ^ n) := by
  -- pigeonhole: two powers coincide
  obtain ⟨s, t, hne, hst⟩ :=
    Finite.exists_ne_map_eq_of_infinite (fun n : ℕ => a ^ n)
  obtain ⟨i, j, hlt, hij⟩ : ∃ i j : ℕ, i < j ∧ a ^ i = a ^ j := by
    rcases lt_or_gt_of_ne hne with h | h
    · exact ⟨s, t, h, hst⟩
    · exact ⟨t, s, h, hst.symm⟩
  set p := j - i with hp
  have hp1 : 0 < p := by omega
  -- one period absorbs past the ramp `i`
  have hstep : ∀ t : ℕ, a ^ (i + t + p) = a ^ (i + t) := by
    intro t
    have h1 : i + t + p = j + t := by omega
    rw [h1, pow_add, pow_add, ← hij]
  -- …hence any number of periods
  have habs : ∀ m t : ℕ, a ^ (i + t + m * p) = a ^ (i + t) := by
    intro m
    induction m with
    | zero => intro t; simp
    | succ m ihm =>
      intro t
      have h1 : i + t + (m + 1) * p = i + (t + m * p) + p := by
        rw [Nat.succ_mul]; omega
      rw [h1, hstep (t + m * p)]
      have h2 : i + (t + m * p) = i + t + m * p := by omega
      rw [h2, ihm t]
  -- the witness: a p-multiple past the ramp
  have hile : i + 1 ≤ p * (i + 1) := Nat.le_mul_of_pos_left _ hp1
  refine ⟨p * (i + 1), by positivity, ?_⟩
  set t₀ := p * (i + 1) - i with ht₀
  have hsplit : p * (i + 1) = i + t₀ := by omega
  have e1 : p * (i + 1) + p * (i + 1) = i + t₀ + (i + 1) * p := by
    rw [Nat.mul_comm (i + 1) p]; omega
  show a ^ (p * (i + 1)) * a ^ (p * (i + 1)) = a ^ (p * (i + 1))
  calc a ^ (p * (i + 1)) * a ^ (p * (i + 1))
      = a ^ (p * (i + 1) + p * (i + 1)) := (pow_add a _ _).symm
    _ = a ^ (i + t₀ + (i + 1) * p) := by rw [e1]
    _ = a ^ (i + t₀) := habs (i + 1) t₀
    _ = a ^ (p * (i + 1)) := by rw [← hsplit]
```

(`omega` treats `p * (i + 1)` as an opaque atom, which is why `hsplit`/`hile` are stated before the lines that need them, and why `e1` first rewrites `(i+1)*p` to the same atom via `Nat.mul_comm`.)

- [ ] **Step 3: Verify and commit**

```bash
lake build 2>&1 | tail -3
grep -rn "sorry" KRTheory/ KRTheory.lean
git add KRTheory/FiniteMonoid.lean
git commit -m "Prove idempotent-power lemma for finite monoids"
```

Expected: green, no sorries, zero warnings.

---

### Task 7: `LocalDivisor.lean` — the monoid

**Files:**
- Create: `KRTheory/TransMon/LocalDivisor.lean`
- Modify: `KRTheory.lean` (add `import KRTheory.TransMon.LocalDivisor` last)

**Interfaces:**
- Consumes: `mul_eq_one_comm` (Mathlib), `KRTheory.Nat.card_subtype_lt` (Task 4).
- Produces (Tasks 8–9 consume these exact names):
  - `LocalDivisor (c : M) : Type` — fields `val : M`, `mem_left : ∃ m, val = c * m`, `mem_right : ∃ m, val = m * c`; `@[ext]` on `val`.
  - `LocalDivisor.equivSubtype : LocalDivisor c ≃ {u : M // (∃ m, u = c * m) ∧ ∃ m, u = m * c}`
  - `noncomputable instance : Monoid (LocalDivisor c)`; `LocalDivisor.val_one : (1 : LocalDivisor c).val = c`
  - `LocalDivisor.mul_spec (u v) {m} (hm : u.val = m * c) : (u * v).val = m * v.val`
  - `LocalDivisor.mul_spec_right (u v) {n} (hn : v.val = c * n) : (u * v).val = u.val * n`

- [ ] **Step 1 (RED): definitions, statements with `sorry`, examples elaborate**

Create the file:

```lean
import KRTheory.FiniteMonoid
import KRTheory.TransMon.Division

/-!
# Local divisors

The local divisor `Mc = cM ∩ Mc` at `c : M` [DKS §2.5, blueprint
`ch:localdivisor`]: product `(mc) ∘ (cn) = mcn`, identity `c`. The
recursion of the Krohn–Rhodes induction descends into local divisors;
the three lemmas here (faithfulness [DKS 2.13], cardinality drop,
division) are what make that descent sound — see spec §3.6.

The carrier is a fresh structure, NOT a subtype of `M`: the product is
not the restriction of `M`'s product, so a `Monoid` instance on a
subtype would be a diamond trap (same rationale as `WreathMonoid`).
The product reads a decomposition witness via `Classical.choose`; the
`mul_spec`/`mul_spec_right` lemmas quarantine that choice — nothing
downstream ever mentions it (spec §8 mitigation).
-/

namespace KRTheory
namespace TransMon

variable {M : Type} [Monoid M] [Finite M]

/-- An element of the local divisor at `c`: a value in `cM ∩ Mc`
[DKS §2.5, blueprint `def:localdiv`]. -/
@[ext]
structure LocalDivisor (c : M) : Type where
  /-- The underlying element of `M`. -/
  val : M
  /-- Membership in `cM`. -/
  mem_left : ∃ m, val = c * m
  /-- Membership in `Mc`. -/
  mem_right : ∃ m, val = m * c

namespace LocalDivisor

variable {c : M}

/-- As a type, `LocalDivisor c` is the subtype `cM ∩ Mc` of `M`. -/
def equivSubtype :
    LocalDivisor c ≃ {u : M // (∃ m, u = c * m) ∧ ∃ m, u = m * c} where
  toFun u := ⟨u.val, u.mem_left, u.mem_right⟩
  invFun s := ⟨s.1, s.2.1, s.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- `LocalDivisor c` is finite, via `equivSubtype` and `Subtype.finite`
(no decidability needed — the point of the amended §4.1 bundling). -/
instance : Finite (LocalDivisor c) := Finite.of_equiv _ equivSubtype.symm

/-- The twisted product `(mc) ∘ (cn) := mcn` and identity `c`
[DKS §2.5]. The product reads an `Mc`-decomposition of the left factor
via `Classical.choose`; use `mul_spec`, never the definition. -/
noncomputable instance : Monoid (LocalDivisor c) where
  mul u v :=
    { val := Classical.choose u.mem_right * v.val
      mem_left := sorry
      mem_right := sorry }
  one := ⟨c, ⟨1, (mul_one c).symm⟩, ⟨1, (one_mul c).symm⟩⟩
  mul_assoc u v w := sorry
  one_mul u := sorry
  mul_one u := sorry

/-- The identity of the local divisor is `c` itself. -/
@[simp] theorem val_one : (1 : LocalDivisor c).val = c := rfl

/-- Choose-independence [DKS §2.5, blueprint `def:localdiv`]: ANY
`Mc`-witness for the left factor computes the product. This is the
lemma that quarantines `Classical.choose`. -/
theorem mul_spec (u v : LocalDivisor c) {m : M} (hm : u.val = m * c) :
    (u * v).val = m * v.val := sorry

/-- The dual computation: any `cM`-witness for the RIGHT factor gives
`(u * v).val = u.val * n`. -/
theorem mul_spec_right (u v : LocalDivisor c) {n : M} (hn : v.val = c * n) :
    (u * v).val = u.val * n := sorry

end LocalDivisor
end TransMon
end KRTheory
```

Add sanity examples at file bottom (inside the namespaces, after `end LocalDivisor`) — they must elaborate at RED and pass at GREEN:

```lean
-- Sanity (spec §6): in `ZMod 4` at `c = 2` the carrier is `{0, 2}`,
-- `2` is the identity, `0` absorbs. Products are evaluated through
-- `mul_spec` (the definition's `choose` does not compute).
private def ld0 : LocalDivisor (2 : ZMod 4) :=
  ⟨0, ⟨0, by decide⟩, ⟨0, by decide⟩⟩
private def ld2 : LocalDivisor (2 : ZMod 4) :=
  ⟨2, ⟨1, by decide⟩, ⟨1, by decide⟩⟩
example : (ld0 * ld2).val = 0 :=
  (LocalDivisor.mul_spec ld0 ld2 (m := 0) (by decide)).trans (by decide)
example : (ld2 * ld0).val = 0 :=
  (LocalDivisor.mul_spec ld2 ld0 (m := 1) (by decide)).trans (by decide)
-- Chirality guard: `mul_spec` multiplies the witness on the LEFT of
-- `v.val`. In `Function.End (Fin 2)` (a noncommutative non-group
-- monoid) a transposed definition `v.val * m` would differ; the
-- concrete instance is built in Task 8's guard once `act` exists, at
-- the transformation-monoid level where chirality is observable.
```

Run `lake build`: elaborates, `sorry` warnings only at the five stub sites.

- [ ] **Step 2 (GREEN): fill the proofs**

The computations, in dependency order (each is 3–8 lines):

  - `mul_spec`: `show Classical.choose u.mem_right * v.val = m * v.val`. Obtain `⟨n, hn⟩ := v.mem_left`; rewrite `hn`, reassociate both sides to `(_ * c) * n`, and close with `← Classical.choose_spec u.mem_right` and `← hm` — both sides are `u.val * n`:

```lean
  show Classical.choose u.mem_right * v.val = m * v.val
  obtain ⟨n, hn⟩ := v.mem_left
  rw [hn, ← mul_assoc, ← mul_assoc, ← Classical.choose_spec u.mem_right, ← hm]
```

  - `mem_left` of the product: with `⟨m₁, hm₁⟩ := u.mem_left` and `⟨n, hn⟩ := v.mem_left`, the value is `u.val * n = c * (m₁ * n)`:

```lean
      mem_left := by
        obtain ⟨n, hn⟩ := v.mem_left
        obtain ⟨m₁, hm₁⟩ := u.mem_left
        refine ⟨m₁ * n, ?_⟩
        rw [hn, ← mul_assoc, ← Classical.choose_spec u.mem_right, hm₁,
          mul_assoc]
```

  - `mem_right` of the product: with `⟨n₂, hn₂⟩ := v.mem_right`, the value is `(choose * n₂) * c`:

```lean
      mem_right := by
        obtain ⟨n₂, hn₂⟩ := v.mem_right
        exact ⟨Classical.choose u.mem_right * n₂, by rw [hn₂, mul_assoc]⟩
```

  - `one_mul u`: `ext`; apply `mul_spec 1 u (m := 1)` with witness `(1 : LocalDivisor c).val = c = 1 * c` (`(one_mul c).symm`), then `one_mul`.
  - `mul_one u`: `ext`; obtain `⟨m₂, hm₂⟩ := u.mem_right`; `mul_spec u 1 hm₂` gives `(u * 1).val = m₂ * c = u.val`.
  - `mul_assoc u v w`: `ext`; obtain `⟨m₂, hm₂⟩ := u.mem_right` and `⟨n, hn⟩ := v.mem_left` and `⟨q₂, hq₂⟩ := v.mem_right`. Left side: `mul_spec (u*v) w` with the `Mc`-witness of `u*v` from `mul_spec u v hm₂ : (u*v).val = m₂ * v.val` and `hq₂` (`(u*v).val = m₂ * (q₂ * c) = (m₂ * q₂) * c`). Right side: `mul_spec u (v*w) hm₂` and `mul_spec v w hq₂`. Both sides land on `m₂ * (q₂ * w.val)` after `mul_assoc` rewrites.
  - `mul_spec_right`: obtain `⟨m₂, hm₂⟩ := u.mem_right`; `mul_spec u v hm₂` gives `(u*v).val = m₂ * v.val = m₂ * (c * n) = (m₂ * c) * n = u.val * n`.

Latitude: exact rewrite sequences may need adjustment at the compiler; the *statements* are fixed.

- [ ] **Step 3: Wire the root import, build, commit**

`KRTheory.lean` gains `import KRTheory.TransMon.LocalDivisor` (last line).

```bash
lake build 2>&1 | tail -3
grep -rn "sorry" KRTheory/ KRTheory.lean
git add KRTheory
git commit -m "Add local divisor monoid with choose-independent product"
```

---

### Task 8: `localDivisor` transformation monoid + faithfulness (DKS 2.13)

**Files:**
- Modify: `KRTheory/TransMon/LocalDivisor.lean`

**Interfaces:**
- Consumes: `LocalDivisor c`, `mul_spec`, `mul_spec_right`, `val_one` (Task 7); `TransMon`, `Faithful`, `regular` (Basic).
- Produces:
  - `localDivisor (T : TransMon) (c : T.M) : TransMon` — states `{x : T.X // ∃ y, x = T.act y c}`, monoid `LocalDivisor c`.
  - `localDivisor_act_spec (T) (c) (ξ) (u) {m} (hm : u.val = c * m) : ((localDivisor T c).act ξ u).val = T.act ξ.val m`
  - `localDivisor_faithful {T} (hT : T.Faithful) (c : T.M) : (localDivisor T c).Faithful`

- [ ] **Step 1 (RED): definitions + stubs + examples**

Append (still inside `namespace TransMon`):

```lean
/-- The local divisor as a transformation monoid [DKS §2.5, blueprint
`def:localdiv-tm`]: `LocalDivisor c` acting on the image `X·c` by
`ξ ∘ (cm) := ξ · m`. The action reads a `cM`-decomposition via
`Classical.choose`; use `localDivisor_act_spec`, never the
definition. -/
noncomputable def localDivisor (T : TransMon) (c : T.M) : TransMon where
  X := {x : T.X // ∃ y, x = T.act y c}
  M := LocalDivisor c
  act ξ u :=
    ⟨T.act ξ.val (Classical.choose u.mem_left), by sorry⟩
  act_one ξ := by sorry
  act_mul ξ u v := by sorry

/-- Choose-independence for the action: ANY `cM`-witness computes it. -/
theorem localDivisor_act_spec (T : TransMon) (c : T.M) (ξ : (localDivisor T c).X)
    (u : (localDivisor T c).M) {m : T.M} (hm : u.val = c * m) :
    ((localDivisor T c).act ξ u).val = T.act ξ.val m := by sorry

/-- [DKS] 2.13 (blueprint `lem:localdiv-faithful`): local divisors of
faithful transformation monoids are faithful — the induction may
recurse into them. -/
theorem localDivisor_faithful {T : TransMon} (hT : T.Faithful)
    (c : T.M) : (localDivisor T c).Faithful := by sorry
```

Examples (elaborate at RED, pass at GREEN). The chirality guard uses `Function.End (Fin 2)` — composition order makes wrong-sided definitions observable; `Function.End` multiplication in Mathlib is `f * g = f ∘ g`, and `TransMon`-side we go through `regular`:

```lean
-- Sanity (spec §6). Over `regular (ZMod 4)` at `c = 2`: the state
-- space is the image `{0, 2}`, and acting by the reset-like element
-- `0` of the local divisor sends every state to `0 · m`-form values.
-- Chirality guard: `act ξ u = ξ · m` for `u = c * m` — the witness
-- multiplies on the RIGHT of the state. With the noncommutative
-- `regular (Function.End (Fin 2))`, a transposed definition
-- (`ξ ∘ u := ξ · m'` read from `u = m' * c`) picks the OTHER
-- factorization and produces a different state; the example below
-- pins the correct one via `localDivisor_act_spec` + `decide`.
```

(Concrete guard construction: `c := (fun _ => 0 : Function.End (Fin 2))` — the constant map, a non-unit; `u := c` with witnesses `c = c * 1` and `c = 1 * c`... the identity witnesses make both sides agree, so instead take `σ := Equiv.swap 0 1` as an `End`, `u.val := c * σ`-form vs `σ' * c`-form values and check the two `act_spec` reads differ as functions by `decide`. The executor has latitude on the exact elements; the example must be one a transposed `act` definition fails, comment saying so.)

- [ ] **Step 2 (GREEN): fill the four proofs**

  - membership (act lands in `X·c`): obtain `⟨y, hy⟩ := ξ.2` and `⟨m₂, hm₂⟩ := u.mem_right`; with `hspec := Classical.choose_spec u.mem_left : u.val = c * choose`, compute `T.act ξ.val choose = T.act y (c * choose) = T.act y u.val = T.act y (m₂ * c) = T.act (T.act y m₂) c` (via `T.act_mul` both ways), witness `T.act y m₂`.
  - `localDivisor_act_spec`: `show T.act ξ.val (Classical.choose u.mem_left) = T.act ξ.val m`; obtain `⟨y, hy⟩ := ξ.2`; rewrite `hy`, fold both sides with `← T.act_mul`, and rewrite the exponents `c * choose = u.val = c * m` via `Classical.choose_spec u.mem_left` and `hm`.
  - `act_one`: `Subtype.ext`; `localDivisor_act_spec` with witness `(1 : LocalDivisor c).val = c = c * 1` (`(mul_one c).symm`), then `T.act_one`.
  - `act_mul`: `Subtype.ext`; obtain `⟨mᵤ, hmᵤ⟩ := u.mem_left`, `⟨mᵥ, hmᵥ⟩ := v.mem_left`. Key identity: `(u * v).val = u.val * mᵥ` (`mul_spec_right u v hmᵥ`), so `(u * v).val = c * (mᵤ * mᵥ)` via `hmᵤ` + associativity — a `cM`-witness for `u * v`. Then `localDivisor_act_spec` three times: `act ξ (u*v) = ξ · (mᵤ * mᵥ) = (ξ · mᵤ) · mᵥ = act (act ξ u) v` via `T.act_mul`.
  - `localDivisor_faithful`: intro `u v h`; `ext` (goal `u.val = v.val`); `refine hT fun x => ?_`; obtain `⟨mu, hmu⟩ := u.mem_left`, `⟨mv, hmv⟩ := v.mem_left`; then

```lean
    calc T.act x u.val
        = T.act (T.act x c) mu := by rw [hmu, T.act_mul]
      _ = ((localDivisor T c).act ⟨T.act x c, x, rfl⟩ u).val :=
          (localDivisor_act_spec T c _ u hmu).symm
      _ = ((localDivisor T c).act ⟨T.act x c, x, rfl⟩ v).val := by
          rw [h ⟨T.act x c, x, rfl⟩]
      _ = T.act (T.act x c) mv := localDivisor_act_spec T c _ v hmv
      _ = T.act x v.val := by rw [hmv, ← T.act_mul]
```

- [ ] **Step 3: Build, verify, commit**

```bash
lake build 2>&1 | tail -3
grep -rn "sorry" KRTheory/ KRTheory.lean
git add KRTheory/TransMon/LocalDivisor.lean
git commit -m "Prove DKS 2.13: local divisors preserve faithfulness"
```

---

### Task 9: Cardinality drop + division

**Files:**
- Modify: `KRTheory/TransMon/LocalDivisor.lean`

**Interfaces:**
- Consumes: `equivSubtype` (Task 7), `KRTheory.Nat.card_subtype_lt` (Task 4), `mul_eq_one_comm` (Mathlib), `mul_spec_right` (Task 7), `MonoidDivides`/`≺ₘ` (Division).
- Produces (spec §4.3 names, declared at `TransMon`-namespace level, not inside `namespace LocalDivisor`):
  - `localDivisor_card_lt {c : M} (hc : ¬ IsUnit c) : Nat.card (LocalDivisor c) < Nat.card M`
  - `localDivisor_divides (c : M) : LocalDivisor c ≺ₘ M`

- [ ] **Step 1 (RED): statements + stubs + examples**

At `TransMon`-namespace level (after the Task 8 material):

```lean
/-- Cardinality drop (blueprint `lem:localdiv-card`): a non-unit's
local divisor is strictly smaller — the recursion's measure. `1` is
not in the carrier: `1 = c * m` would make `c` a unit by finiteness
(`mul_eq_one_comm`). -/
theorem localDivisor_card_lt {c : M} (hc : ¬ IsUnit c) :
    Nat.card (LocalDivisor c) < Nat.card M := by sorry

/-- Division (blueprint `lem:localdiv-divides`): `Mc ≺ₘ M` via the
submonoid `N = {m | c * m ∈ Mc}` and `ψ : m ↦ c * m`. THE lemma that
keeps the strong form alive through recursion (spec §3.6): simple
groups arising inside `Mc` divide `Mc`, hence divide `M`. -/
theorem localDivisor_divides (c : M) : LocalDivisor c ≺ₘ M := by sorry
```

Examples:

```lean
-- Sanity (spec §6): `2` is not a unit in `ZMod 4`, so its local
-- divisor (carrier `{0, 2}`) is strictly smaller and divides.
example : ¬ IsUnit (2 : ZMod 4) := by decide
example : Nat.card (LocalDivisor (2 : ZMod 4)) < Nat.card (ZMod 4) :=
  localDivisor_card_lt (by decide)
example : LocalDivisor (2 : ZMod 4) ≺ₘ ZMod 4 := localDivisor_divides _
-- Milestone acceptance shape (spec §7 row 5): the measure and the
-- division hold together for any non-unit.
example (c : ZMod 4) (h : ¬ IsUnit c) :
    LocalDivisor c ≺ₘ ZMod 4 ∧ Nat.card (LocalDivisor c) < Nat.card (ZMod 4) :=
  ⟨localDivisor_divides c, localDivisor_card_lt h⟩
```

- [ ] **Step 2 (GREEN): `localDivisor_card_lt`**

```lean
  rw [Nat.card_congr (LocalDivisor.equivSubtype (c := c))]
  refine Nat.card_subtype_lt (x := (1 : M)) ?_
  rintro ⟨⟨m, hm⟩, -⟩
  -- hm : (1 : M) = c * m — c is right-invertible, hence (finite) a unit
  exact hc ⟨⟨c, m, hm.symm, mul_eq_one_comm.mp hm.symm⟩, rfl⟩
```

- [ ] **Step 3 (GREEN): `localDivisor_divides`**

```lean
  refine ⟨{ carrier := {m | ∃ m₂, c * m = m₂ * c}
            one_mem' := ⟨1, by rw [mul_one, one_mul]⟩
            mul_mem' := ?_ },
    { toFun := fun m => ⟨c * m.1, ⟨m.1, rfl⟩, m.2⟩
      map_one' := ?_
      map_mul' := ?_ }, ?_⟩
  · -- mul_mem': c(mn) = m₂(cn) = m₂n₂c
    rintro m n ⟨m₂, hm₂⟩ ⟨n₂, hn₂⟩
    exact ⟨m₂ * n₂, by rw [← mul_assoc, hm₂, mul_assoc, hn₂, ← mul_assoc]⟩
  · -- ψ 1 = ⟨c * 1⟩ = ⟨c⟩ = 1
    ext
    simp
  · -- ψ(m n) = ψ m * ψ n via mul_spec_right with witness ψ n = c * n
    rintro ⟨m, hm⟩ ⟨n, hn⟩
    ext
    rw [LocalDivisor.mul_spec_right _ _ (n := n) rfl]
    show c * (m * n) = c * m * n
    rw [mul_assoc]
  · -- surjective: u = c * m = m₂ * c puts m in N with ψ m = u
    rintro ⟨u, ⟨m, hm⟩, ⟨m₂, hm₂⟩⟩
    exact ⟨⟨m, m₂, by rw [← hm, hm₂]⟩, by ext; exact hm.symm⟩
```

Latitude on tactic details (e.g. whether `map_mul'`'s `show` is needed); statements fixed. Note `map_one'` needs `(1 : LocalDivisor c).val = c` — that is `val_one`; if `simp` doesn't close it, `exact val_one.symm ▸ rfl`-style or `ext; exact (mul_one c)` variants.

- [ ] **Step 4: Build, verify, commit**

```bash
lake build 2>&1 | tail -3
grep -rn "sorry" KRTheory/ KRTheory.lean
git add KRTheory/TransMon/LocalDivisor.lean
git commit -m "Prove local divisor cardinality drop and division"
```

---

### Task 10: Milestone close

**Files:**
- Modify: `scripts/AxiomCertificate.lean`, `blueprint/src/chapters/finitemonoid.tex`, `blueprint/src/chapters/localdivisor.tex`

**Interfaces:** consumes everything; produces the milestone-acceptance state.

- [ ] **Step 1: Extend the axiom certificate**

Append to `scripts/AxiomCertificate.lean`:

```lean
#print axioms KRTheory.exists_pow_idempotent
#print axioms localDivisor_faithful
#print axioms localDivisor_card_lt
#print axioms localDivisor_divides
```

Run `lake env lean scripts/AxiomCertificate.lean` — every line must end `[propext, Classical.choice, Quot.sound]`.

- [ ] **Step 2: Stamp the blueprint**

Add `\leanok` after each `\lean{...}` in the two new chapters (all lemmas now formalized; the `\notready` remark stays). Push and confirm the blueprint CI job stays green.

- [ ] **Step 3: Full verification sweep**

```bash
lake build 2>&1 | tail -5          # green, zero warnings
grep -rn "sorry" KRTheory/ KRTheory.lean   # empty
gh pr checks --watch                # both jobs green
```

- [ ] **Step 4: Review, memory, handoff**

Request a code review of the milestone diff (`superpowers:requesting-code-review` per repo process; base `milestone-4`). After the review verdict: update the auto-memory file `kr-theory-project.md` process state (M5 done: Finite swap executed, repo published, three local-divisor lemmas proved; next: plan M6 group case — note `Covering.sect`/`stateMap_sect` are public for Kaloujnine–Krasner, and DKS 2.11 needs the nonempty-state care recorded in the memory). Commit any review fixes. Merging the PR stays the user's call.
