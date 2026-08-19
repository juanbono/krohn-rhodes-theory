# Krohn–Rhodes Milestone 9 (Semigroup form + polish) Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Close v1 — prove `krohnRhodes_semigroup` (the classical 1965 finite-semigroup statement, spec §1 item 3), migrate the blueprint to the real `leanblueprint` toolchain so its dependency graph builds green in CI (spec §1 item 5), and clear the M7/M8 parked cosmetics.

**Architecture:** One new Lean file `KRTheory/SemigroupVersion.lean` on branch `milestone-9` (stacked on `milestone-8`, PR #8), one new blueprint chapter `semigroup.tex`, a blueprint toolchain migration (scaffolded by `leanblueprint new`, keeping our proven pdflatex print path), and a CI extension that builds the web/graph version. The Lean is pure gluing over M8's `krohnRhodes_monoid`: `S ≺ₛ S¹`, `S¹ ≺ₘ W` transferred to `≺ₛ`, and a factor-transport lemma. No new coverings, no wreath manipulation.

**Tech Stack:** Lean 4 (`v4.34.0-rc1`), Mathlib pinned `ac4c4bff`, existing CI, plus (new) Python + `leanblueprint`/plasTeX/graphviz in CI only. Base: `milestone-8` @ `e8a2e41`.

**Spec:** `docs/superpowers/specs/2026-08-17-krohn-rhodes-formalization-design.md` — §1 items 3 and 5 (definition of done), §3.2 (semigroup division), §3.9 (`krohnRhodes_semigroup` target signature + the deferred factor-condition question), §4.3 `SemigroupVersion.lean` row, §7 row 9 acceptance ("all of §1 done; axiom certificate").

## Global Constraints

- All Lean inside `namespace KRTheory`; `Finite` bundling; `Nat.card`; docstrings on every public declaration citing blueprint labels; zero-warning builds; no `sorry` at task end; plain single-line commits, no trailers (never `Co-Authored-By`).
- Formalization-TDD: statements below are FIXED (the entire chain was proved end-to-end in this planning session's probe, `#print axioms` = `[propext, Classical.choice, Quot.sound]`); tactic scripts have latitude.
- Notation: `≺ₛ` is scoped to `KRTheory` and clash-free (checked against Mathlib and the repo). `scoped infix` MUST sit inside `namespace KRTheory` — it errors at top level.
- Deprecation/linter state at this pin: `push_neg` → `push Not`; `letI`/`haveI` → `let`/`have` in Prop-goal proofs.
- **Blueprint deployment is NOT in scope.** CI builds the web version and uploads it as an artifact; publishing it to GitHub Pages is the user's decision (see Decision 5). No task may enable Pages or add a deploy step.

## Decisions this plan records

1. **The spec §3.9 deferred question resolves in favor of the STRONG phrasing** — `G.carrier ≺ₛ S`, exactly as the spec's target signature already reads; no weakening. Probe-proved via `semigroupDivides_of_monoidDivides_withOne`: given a submonoid `N' ≤ S¹` surjecting onto `G`, the `S`-elements of `N'` form a subsemigroup covering every `g ≠ 1`, and `1` is recovered as `h · h⁻¹`. **Nontriviality is load-bearing** and comes free from `IsSimpleGroup` (which extends `Nontrivial`); `Group` is needed for the inverse.
2. **`≺ₛ` gets `refl`/`of_subsemigroup`/`trans`** (mirroring `MonoidDivides`), because the final assembly needs `trans` once (`S ≺ₛ S¹ ≺ₛ W.M`). Not a full preorder API beyond that — YAGNI.
3. **A Mathlib gap is filled inline:** `MonoidHom.submonoidComap_surjective_of_surjective` exists, but there is NO `Subsemigroup`/`MulHom` analogue, so `SemigroupDivides.trans` proves that surjectivity in a `have` (recorded in the spec §9 upstreaming ledger — natural first PR alongside `FiniteMonoid.lean`).
4. **`Finite (WithOne S)` is supplied locally, not as a global instance:** `WithOne α` is a transparent synonym for `Option α` but instance search does not cross it, so the one call site uses `have : Finite (WithOne S) := inferInstanceAs (Finite (Option S))`. No global instance is planted on a Mathlib type (same rationale as §4.1's `Monoid (Option _)` avoidance).
5. **Spec §1 item 5 is read as "CI BUILDS the dependency graph, green"** — not "the site is published". Deploying a public GitHub Pages site is a publish and belongs to the user; the plan wires the build + artifact upload and Task 7 hands the user the one-line follow-up if they want it live. `blueprint/README.md`'s "post-v1" note is superseded for the build, retained for deployment.
6. **The PDF path stays pdflatex.** `leanblueprint new` generates a xelatex/unicode-math `print.tex`; we keep our existing pdflatex-compatible one (CI-proven, and commit `0d4cac8` already fixed unicode for it). The scaffolder is used for the WEB side only. Shared theorem environments move to `macros/common.tex`; our `\lean`/`\leanok`/`\uses`/`\notready` marginpar definitions move to `macros/print.tex`.
7. **`tag_mul` consolidation (M7 park) is included but droppable** — it refactors ~60 duplicated lines inside `decompInv_of_mem`, a delicate M7 proof. Acceptance is "build green, no statement changes"; if it does not converge in one fix round, revert it and re-park to post-v1 (Task 5 states this explicitly).

## Probe findings that shape this plan (this planning session, all verified)

- The whole Lean chain compiles verbatim (Task 4's code is the probe file, unedited), and `krohnRhodes_semigroup` instantiates non-vacuously at `ZMod 6`.
- `MulMemClass.subtype` is the subsemigroup inclusion hom (there is no `Subsemigroup.subtype`); `Subsemigroup.equivMapOfInjective` and `MulHom.subsemigroupComap` exist.
- **plasTeX resolves `\input` via `kpsewhich`, so the web build REQUIRES a TeX installation.** Verified by minimal test: on a machine without TeX, a two-line document fails to find `\input{sub/child}`, and `leanblueprint`'s own generated skeleton fails to find its own `macros/common` — independent of plasTeX version (3.1 vs git master) and Python (3.13 vs 3.14). This is why the web build is wired into a CI job that installs TeX, and why a developer without TeX cannot build it locally.
- `leanblueprint new` requires a git repo with a CLEAN working tree, asks 11 questions + a `y/n` confirm + 2 lakefile questions, and generates `blueprint/src/{web.tex,print.tex,plastex.cfg,latexmkrc,blueprint.sty,extra_styles.css,content.tex,macros/{common,web,print}.tex}`. `blueprint.sty` is the piece a hand-rolled config misses.
- `leanblueprint web` runs `plastex -c plastex.cfg web.tex` with `cwd=blueprint/src`; `leanblueprint checkdecls` runs `lake exe checkdecls blueprint/lean_decls`, which needs the `checkdecls` dependency in the lakefile (the scaffolder offers to add it) AND a built Lean project AND a prior web build (the plugin writes `lean_decls`).
- Blueprint inventory: 71 labeled items, 58 statement-level `\leanok`, 36 `proof` environments, **0** proof-level `\leanok` — the graph's proof nodes are all non-green until Task 6 stamps them.

---

### Task 1: Spec amendments + branch/PR

**Files:**
- Modify: `docs/superpowers/specs/2026-08-17-krohn-rhodes-formalization-design.md` (§3.2, §3.9, §4.3 row, §9 ledger, §1 item 5 clarification)

**Interfaces:** none produced.

- [ ] **Step 0: Create the branch**

```bash
git checkout milestone-8
git checkout -b milestone-9
```

- [ ] **Step 1: §3.9 — record the resolved factor condition**

Replace the parenthetical paragraph

```markdown
(The factor condition is the same in all three; in the semigroup form the group divisors are semigroup divisors of S — the exact phrasing of that last conjunct is settled at milestone 9, since `G ≺ₛ S` vs `G ≺ₘ WithOne S` are interderivable there.)
```

with

```markdown
(The factor condition is the same in all three. **Resolved 2026-08-19 (M9):** the strong phrasing `G ≺ₛ S` is what we prove — the signature above stands unweakened. From `G ≺ₘ S¹` the `S`-elements of the covering submonoid form a subsemigroup that covers every `g ≠ 1`, and `1 = h · h⁻¹` for any `h ≠ 1`; nontriviality of the factor is load-bearing and comes free from `IsSimpleGroup`.)
```

- [ ] **Step 2: §3.2 — record the Mathlib gap**

Append to the `Semigroup division` bullet: ` (2026-08-19: transitivity must prove `MulHom`-level comap surjectivity inline — Mathlib has `submonoidComap_surjective_of_surjective` but no `Subsemigroup` analogue; upstreaming candidate, §9.)`

- [ ] **Step 3: §4.3 row**

Replace the `SemigroupVersion.lean` row with

```markdown
| `SemigroupVersion.lean` | `SemigroupDivides` (`≺ₛ`) + `refl`/`of_subsemigroup`/`trans`, `monoidDivides_semigroupDivides` (feeder), `withOne_transfer`, `semigroupDivides_of_monoidDivides_withOne` (factor transport), `krohnRhodes_semigroup` |
```

- [ ] **Step 4: §1 item 5 clarification + §9 ledger**

  1. §1 item 5: replace `5. CI builds the project and the blueprint; blueprint dependency graph fully green.` with `5. CI builds the project and the blueprint — including the \`leanblueprint\` web build — and the dependency graph is fully green. (Publishing that site to GitHub Pages is deliberately out of v1 scope: it is a publication decision, not a correctness one.)`
  2. §9 ledger, the **Upstreaming plan** bullet: append ` Also: a `MulHom`/`Subsemigroup` analogue of `submonoidComap_surjective_of_surjective`, which M9 had to prove inline.`

- [ ] **Step 5: Commit, open the stacked draft PR**

```bash
git add docs/superpowers/specs
git commit -m "Record M9 spec amendments: resolved factor condition, Mathlib gap, blueprint scope"
git push -u origin milestone-9
gh pr create --draft --base milestone-8 --title "Milestone 9: semigroup form and v1 polish" \
  --body "Tracking PR so CI runs per push. Merge policy stays manual."
```

Record the ACTUAL PR number returned; later tasks use it for `gh pr checks`.

---

### Task 2: Blueprint chapter `semigroup.tex`

**Files:**
- Create: `blueprint/src/chapters/semigroup.tex`
- Modify: `blueprint/src/content.tex` (add `\input{chapters/semigroup}` after `chapters/krohnrhodes`)

**Interfaces:**
- Produces labels Tasks 4/6 cite: `ch:semigroup`, `def:semdiv`, `lem:semdiv-preorder`, `lem:semdiv-of-mdiv`, `lem:withone-transfer`, `lem:semdiv-group-withone`, `thm:krohnrhodes-semigroup`.

- [ ] **Step 1: Write the chapter**

```latex
\chapter{The semigroup form}\label{ch:semigroup}

The classical Krohn--Rhodes theorem (Krohn--Rhodes 1965) speaks of finite
semigroups. This chapter derives it from the monoid form
(Theorem~\ref{thm:krohnrhodes-monoid}) by adjoining an identity.

\begin{definition}[Semigroup division]\label{def:semdiv}
  \lean{KRTheory.SemigroupDivides}
  \uses{def:mdiv}
  $S \prec_s T$ iff $S$ is the image of a subsemigroup of $T$ under a
  surjective semigroup homomorphism. Same shape as
  Definition~\ref{def:mdiv}, with submonoids and monoid homomorphisms
  replaced by subsemigroups and semigroup homomorphisms.
\end{definition}

\begin{lemma}[Reflexivity and transitivity]\label{lem:semdiv-preorder}
  \lean{KRTheory.SemigroupDivides.refl, KRTheory.SemigroupDivides.of_subsemigroup, KRTheory.SemigroupDivides.trans}
  \uses{def:semdiv}
  $\prec_s$ is reflexive and transitive, and every subsemigroup divides
  its ambient semigroup.
\end{lemma}
\begin{proof}
  Reflexivity uses the top subsemigroup, and a subsemigroup $A \le T$
  divides $T$ via $A$ itself and the identity homomorphism. For
  transitivity, pull the subsemigroup witnessing $S \prec_s T$ back
  along the second homomorphism and push it into $U$, exactly as in the
  monoid case
  (Lemma~\ref{lem:mdiv-preorder}). One step Mathlib supplies for
  monoids but not for semigroups --- surjectivity of the comap
  homomorphism --- is proved inline.
\end{proof}

\begin{lemma}[Monoid division is semigroup division]\label{lem:semdiv-of-mdiv}
  \lean{KRTheory.monoidDivides_semigroupDivides}
  \uses{def:semdiv,def:mdiv}
  $M \prec_m N$ implies $M \prec_s N$.
\end{lemma}
\begin{proof}
  A submonoid is a subsemigroup and a monoid homomorphism is a
  semigroup homomorphism; surjectivity is unchanged.
\end{proof}

\begin{lemma}[Adjoining an identity]\label{lem:withone-transfer}
  \lean{KRTheory.withOne_transfer}
  \uses{def:semdiv}
  $S \prec_s S^1$, where $S^1$ is $S$ with an identity adjoined.
\end{lemma}
\begin{proof}
  The image of $S$ in $S^1$ is a subsemigroup (a product of two
  non-identity elements is again one), and the inverse of the
  injection $S \hookrightarrow S^1$ is a surjective homomorphism onto
  $S$.
\end{proof}

\begin{lemma}[Factor transport]\label{lem:semdiv-group-withone}
  \lean{KRTheory.semigroupDivides_of_monoidDivides_withOne}
  \uses{def:semdiv,def:mdiv}
  Let $G$ be a \emph{nontrivial} finite group and $S$ a semigroup. If
  $G \prec_m S^1$ then $G \prec_s S$.
\end{lemma}
\begin{proof}
  Let $N \le S^1$ be a submonoid with a surjection $\psi : N \to G$,
  and let $T := \{\, x \in S \mid x \in N \,\}$, a subsemigroup of $S$
  (again because products of non-identity elements are non-identity).
  For $g \neq 1$ choose $n \in N$ with $\psi(n) = g$; then $n \neq 1$,
  since $\psi(1) = 1 \neq g$, so $n$ lies in $T$. Thus $\psi(T)$
  contains every $g \neq 1$. Nontriviality now supplies the identity
  as well: pick $h \neq 1$, take preimages $x, y \in T$ of $h$ and
  $h^{-1}$, and $xy \in T$ maps to $1$. Hence $\psi$ restricted to $T$
  is onto $G$.
\end{proof}

\begin{remark}[Why nontriviality is needed]\label{rem:semdiv-nontrivial}
  Without it the argument fails at exactly one point: the preimage of
  the identity. A trivial group divides $S^1$ (via $\{1\}$) but need
  not divide $S$ --- $S$ may be empty. In our application the factors
  are simple groups, which are nontrivial by definition, so the
  hypothesis is free.
\end{remark}

\begin{theorem}[Krohn--Rhodes, semigroup form]\label{thm:krohnrhodes-semigroup}
  \lean{KRTheory.krohnRhodes_semigroup}
  \uses{def:krprime,thm:krohnrhodes-monoid,lem:withone-transfer,lem:semdiv-of-mdiv,lem:semdiv-preorder,lem:semdiv-group-withone}
  Every finite semigroup $S$ divides, as a semigroup, the wreath-product
  monoid of a list of Krohn--Rhodes primes whose group factors are
  nontrivial finite simple groups dividing $S$ (as semigroups).
\end{theorem}
\begin{proof}
  Apply Theorem~\ref{thm:krohnrhodes-monoid} to the finite monoid
  $S^1$, giving $S^1 \prec_m W$ for the wreath monoid $W$ of some
  prime list, with each group factor dividing $S^1$. Then
  $S \prec_s S^1$ (Lemma~\ref{lem:withone-transfer}),
  $S^1 \prec_s W$ (Lemma~\ref{lem:semdiv-of-mdiv}), and transitivity
  (Lemma~\ref{lem:semdiv-preorder}) gives $S \prec_s W$. Each group
  factor is simple, hence nontrivial, so
  Lemma~\ref{lem:semdiv-group-withone} converts $G \prec_m S^1$ into
  $G \prec_s S$.
\end{proof}
```

- [ ] **Step 2: Wire and cross-check**

Append `\input{chapters/semigroup}` to `content.tex` after the `chapters/krohnrhodes` line, then run the house label cross-check:

```bash
cd blueprint/src && grep -ho '\\label{[^}]*}' chapters/*.tex | sed 's/\\label{\(.*\)}/\1/' | sort > /tmp/labels.txt && grep -ho '\\uses{[^}]*}' chapters/semigroup.tex | sed 's/\\uses{//;s/}//' | tr ',' '\n' | sed 's/^[[:space:]]*//;s/[[:space:]]*$//' | sort -u | while read u; do grep -qx "$u" /tmp/labels.txt || echo "MISSING: $u"; done; cd ../..
```

Expected: no MISSING. Then commit and push:

```bash
git add blueprint/src
git commit -m "Add semigroup blueprint chapter"
git push
gh pr checks <PR> --watch
```

**This chapter is the milestone's math gate — review it before any Lean.**

---

### Task 3: Blueprint cosmetics batch (M7 + M8 parks)

**Files:**
- Modify: `blueprint/src/chapters/localdivisor.tex`, `decomposition.tex`, `krohnrhodes.tex`

**Interfaces:** none produced; all edits are typography/dependency-edge fixes.

- [ ] **Step 1: Notation consistency**

  1. `localdivisor.tex`, `lem:localdiv-nonempty` (the M8 lemma): change `$X{\cdot}c$` to `$X_c$` (the spelling `def:localdiv-tm` establishes in the same chapter).
  2. `krohnrhodes.tex`, `thm:kr-bar`'s statement/proof display: change `$X{\cdot}c$` to `$X_c$` and `$X \sqcup N$` to `$X \mathbin{\dot\cup} N$` (matching `decomposition.tex`).

- [ ] **Step 2: Define the wreath shorthand**

In `krohnrhodes.tex`, immediately after the chapter's opening paragraph, insert:

```latex
Throughout this chapter, $\wr L$ abbreviates the iterated wreath product
$\mathrm{wreathList}$ (Definition~\ref{def:wreathList}) of the
transformation monoids of the primes in the list $L$.
```

- [ ] **Step 3: Fix the M7 `\uses` nits**

  1. `decomposition.tex`, `lem:decomp-cover-unique`: add `lem:nonempty-of-nonunit` to its `\uses` list (the uniqueness proof needs nonempty states).
  2. `decomposition.tex`, `thm:decomposition`: remove `lem:right-factor-faithful` from its `\uses` list (the theorem's own proof does not use right-factor faithfulness — that is M8's consumer).

- [ ] **Step 4: Sentence order in `lem:kr-group-branch`**

In `krohnrhodes.tex`, that lemma's proof currently opens with the `groupOfIsUnit` sentence before citing `lem:group-bar`, implying the group structure feeds `group-bar`. Reorder so the group-bar citation comes first:

```latex
  Lemma~\ref{lem:group-bar} gives
  $\bar{T} \prec U(X) \wr (M, M)$ directly from the hypothesis that
  every element of $M$ is a unit. To resolve the right factor we need
  $M$ as an actual group: its inverse is read off the unit witness
  (Mathlib's \texttt{groupOfIsUnit}, which extends the ambient monoid
  structure in place), and then
```

adjusting the following sentence so it continues grammatically into the `lem:reset-div-flipflops` / `lem:group-series` citations (keep both citations and the existing `\uses` list unchanged).

- [ ] **Step 5: Polish `semigroup.tex` (from Task 2's math-gate review)**

  1. The phrase "non-identity element" is imprecise at exactly the two places where closure under multiplication is argued (`lem:withone-transfer`'s proof and `lem:semdiv-group-withone`'s proof): if `S` already has an identity `e`, then `e`'s image is a "non-identity element" of `S¹` under the literal reading. In both proofs replace the parenthetical
     `(a product of two non-identity elements is again one)` / `(again because products of non-identity elements are non-identity)`
     with `(a product of two elements of the copy of $S$ inside $S^1$ is again one)`.
  2. After `rem:semdiv-nontrivial`, add a second remark recording that the semigroup form — unlike `thm:krohnrhodes` — needs no nonemptiness hypothesis:

```latex
\begin{remark}[No nonemptiness hypothesis]\label{rem:semigroup-empty}
  Theorem~\ref{thm:krohnrhodes} must assume a nonempty state set, but
  Theorem~\ref{thm:krohnrhodes-semigroup} needs no such hypothesis:
  $S^1$ is nonempty even when $S$ is not, and for $S = \emptyset$ the
  factor condition is vacuous, since no nontrivial group divides the
  trivial monoid $\emptyset^1$.
\end{remark}
```

  3. NOT changed, deliberately: `def:semdiv`'s `\uses{def:mdiv}` (an expository edge to a `\leanok`'d node — a reader expects the comparison, and a spurious edge here is harmless), the unused finiteness hypothesis on `G` in `lem:semdiv-group-withone` (kept for uniformity with the application), and the `\prec_s`/`\prec` symbol proximity (the labels already dodge the clash; renaming is post-v1).

- [ ] **Step 6: Verify and commit**

Re-run the Task 2 Step 2 cross-check over all chapters (`chapters/*.tex` instead of just `semigroup.tex`); expect no MISSING. Then:

```bash
git add blueprint/src
git commit -m "Clear parked blueprint cosmetics from milestones 7 and 8"
git push
```

---

### Task 4: `SemigroupVersion.lean`

**Files:**
- Create: `KRTheory/SemigroupVersion.lean`
- Modify: `KRTheory.lean` (append `import KRTheory.SemigroupVersion`)

**Interfaces:**
- Consumes: `krohnRhodes_monoid` (M8), `MonoidDivides` (M2), Mathlib `Subsemigroup`/`MulHom`/`WithOne`.
- Produces: `SemigroupDivides` (`≺ₛ`) + `refl`/`of_subsemigroup`/`trans`, `monoidDivides_semigroupDivides`, `withOne_transfer`, `semigroupDivides_of_monoidDivides_withOne`, `krohnRhodes_semigroup`.

- [ ] **Step 1: Write the file**

Every declaration below compiled verbatim in planning (`#print axioms krohnRhodes_semigroup` = `[propext, Classical.choice, Quot.sound]`).

```lean
import KRTheory.KrohnRhodes

/-!
# The semigroup form of Krohn–Rhodes

The classical 1965 statement [spec §1 item 3, §3.9; blueprint
`ch:semigroup`]: every finite semigroup divides an iterated wreath
product of flip-flops and simple groups. Derived from the monoid form
by adjoining an identity (`WithOne`).

Semigroup division `≺ₛ` mirrors `≺ₘ` (`Division.lean`) with
subsemigroups and `MulHom`s in place of submonoids and `MonoidHom`s.
-/

namespace KRTheory

/-- `S ≺ₛ T` [DKS §2.3, blueprint `def:semdiv`]: `S` is a homomorphic
image of a subsemigroup of `T`. -/
def SemigroupDivides (S T : Type) [Semigroup S] [Semigroup T] : Prop :=
  ∃ (T' : Subsemigroup T) (ψ : T' →ₙ* S), Function.Surjective ψ

@[inherit_doc]
scoped infix:50 " ≺ₛ " => SemigroupDivides

namespace SemigroupDivides

variable {S T U : Type} [Semigroup S] [Semigroup T] [Semigroup U]

/-- `≺ₛ` is reflexive, via the top subsemigroup [blueprint
`lem:semdiv-preorder`]. Mirrors `MonoidDivides.refl` exactly, down to
using the `topEquiv` Mathlib provides for each. -/
theorem refl (S : Type) [Semigroup S] : S ≺ₛ S :=
  ⟨⊤, Subsemigroup.topEquiv.toMulHom, Subsemigroup.topEquiv.surjective⟩

/-- Subsemigroups divide their ambient semigroup [blueprint
`lem:semdiv-preorder`]. -/
theorem of_subsemigroup (T' : Subsemigroup T) : (↥T') ≺ₛ T :=
  ⟨T', MulHom.id ↥T', Function.surjective_id⟩

/-- `≺ₛ` is transitive [blueprint `lem:semdiv-preorder`]: pull the
subsemigroup witnessing `T ≺ₛ U` back along `χ` and push it into `U`,
mirroring `MonoidDivides.trans`. Mathlib supplies
`submonoidComap_surjective_of_surjective` for monoids but has no
subsemigroup analogue, so that step is proved inline (spec §9
upstreaming candidate). -/
theorem trans (h₁ : S ≺ₛ T) (h₂ : T ≺ₛ U) : S ≺ₛ U := by
  obtain ⟨T', ψ, hψ⟩ := h₁
  obtain ⟨U', χ, hχ⟩ := h₂
  -- Q : the preimage of T' along χ, as a subsemigroup of U'
  let Q : Subsemigroup U' := T'.comap χ
  -- e : Q, viewed inside U via the inclusion U' ↪ U, is isomorphic to Q
  let e : Q ≃* Q.map (MulMemClass.subtype U') :=
    Subsemigroup.equivMapOfInjective Q (MulMemClass.subtype U')
      (MulMemClass.subtype_injective U')
  have hcomap : Function.Surjective (χ.subsemigroupComap T') := by
    rintro ⟨t, ht⟩
    obtain ⟨u, hu⟩ := hχ t
    refine ⟨⟨u, ?_⟩, Subtype.ext hu⟩
    show χ u ∈ T'
    rw [hu]; exact ht
  exact ⟨Q.map (MulMemClass.subtype U'),
    ψ.comp ((χ.subsemigroupComap T').comp e.symm.toMulHom),
    hψ.comp (hcomap.comp e.symm.surjective)⟩

end SemigroupDivides

/-- Monoid division is semigroup division [blueprint
`lem:semdiv-of-mdiv`]: forget the units. -/
theorem monoidDivides_semigroupDivides {M N : Type} [Monoid M] [Monoid N]
    (h : M ≺ₘ N) : M ≺ₛ N := by
  obtain ⟨N', ψ, hψ⟩ := h
  exact ⟨N'.toSubsemigroup, ψ.toMulHom, hψ⟩

/-- Adjoining an identity is harmless [blueprint `lem:withone-transfer`]:
`S ≺ₛ S¹`. The copy of `S` inside `WithOne S` is a subsemigroup (a
product of two non-identity elements is non-identity), and the
coercion's inverse is a surjective homomorphism onto `S`. -/
theorem withOne_transfer (S : Type) [Semigroup S] : S ≺ₛ WithOne S := by
  refine ⟨{ carrier := Set.range ((↑) : S → WithOne S)
            mul_mem' := ?_ },
    { toFun := fun x => Classical.choose x.2
      map_mul' := ?_ }, ?_⟩
  · rintro a b ⟨x, rfl⟩ ⟨y, rfl⟩
    exact ⟨x * y, WithOne.coe_mul x y⟩
  · rintro a b
    -- both sides are the unique `S`-preimages; compare after coercion
    apply WithOne.coe_inj.mp
    rw [WithOne.coe_mul, Classical.choose_spec a.2, Classical.choose_spec b.2,
      Classical.choose_spec (a * b).2]
    rfl
  · intro s
    refine ⟨⟨(s : WithOne S), s, rfl⟩, ?_⟩
    apply WithOne.coe_inj.mp
    exact Classical.choose_spec (⟨(s : WithOne S), s, rfl⟩ :
      { x : WithOne S // x ∈ Set.range ((↑) : S → WithOne S) }).2

/-- Factor transport [blueprint `lem:semdiv-group-withone`, spec §3.9 as
resolved 2026-08-19]: a NONTRIVIAL group dividing `S¹` as a monoid
already divides `S` as a semigroup. Nontriviality is load-bearing — it
supplies the preimage of `1` as a product `h * h⁻¹` — and comes free
from `IsSimpleGroup` at the call site. -/
theorem semigroupDivides_of_monoidDivides_withOne {G S : Type} [Group G]
    [Nontrivial G] [Semigroup S] (h : G ≺ₘ WithOne S) : G ≺ₛ S := by
  obtain ⟨N', ψ, hψ⟩ := h
  have hmul : ∀ {x y : S}, (x : WithOne S) ∈ N' → (y : WithOne S) ∈ N' →
      ((x * y : S) : WithOne S) ∈ N' := by
    intro x y hx hy
    rw [WithOne.coe_mul]
    exact N'.mul_mem hx hy
  -- every non-identity element of `G` is hit by an `S`-element of `N'`
  have hne : ∀ g : G, g ≠ 1 → ∃ x : S, ∃ hx : (x : WithOne S) ∈ N', ψ ⟨_, hx⟩ = g := by
    intro g hg
    obtain ⟨n, hn⟩ := hψ g
    have hn1 : n.1 ≠ 1 := by
      intro h1
      apply hg
      rw [← hn]
      have : n = 1 := Subtype.ext h1
      rw [this, map_one]
    obtain ⟨x, hx⟩ := WithOne.ne_one_iff_exists.mp hn1
    refine ⟨x, hx ▸ n.2, ?_⟩
    rw [← hn]
    congr 1
    exact Subtype.ext hx
  refine ⟨{ carrier := {x : S | (x : WithOne S) ∈ N'}
            mul_mem' := fun hx hy => hmul hx hy },
    { toFun := fun x => ψ ⟨(x.1 : WithOne S), x.2⟩
      map_mul' := ?_ }, ?_⟩
  · intro a b
    rw [← map_mul]
    congr 1
  · intro g
    rcases eq_or_ne g 1 with rfl | hg
    · -- the identity: `h * h⁻¹` for any `h ≠ 1` — this is why `Nontrivial` is needed
      obtain ⟨h, hh⟩ := exists_ne (1 : G)
      obtain ⟨x, hx, hxg⟩ := hne h hh
      obtain ⟨y, hy, hyg⟩ := hne h⁻¹ (inv_ne_one.mpr hh)
      refine ⟨⟨x * y, hmul hx hy⟩, ?_⟩
      show ψ ⟨((x * y : S) : WithOne S), _⟩ = 1
      have : (⟨((x * y : S) : WithOne S), hmul hx hy⟩ : N') = ⟨_, hx⟩ * ⟨_, hy⟩ :=
        Subtype.ext (WithOne.coe_mul x y)
      rw [this, map_mul, hxg, hyg, mul_inv_cancel]
    · obtain ⟨x, hx, hxg⟩ := hne g hg
      exact ⟨⟨x, hx⟩, hxg⟩

open TransMon in
/-- **The Krohn–Rhodes theorem**, classical semigroup form (Krohn–Rhodes
1965) [spec §1 item 3, §3.9; blueprint `thm:krohnrhodes-semigroup`]:
every finite semigroup divides an iterated wreath product of flip-flops
and regular representations of finite simple groups, each group factor
dividing `S`. `Finite (WithOne S)` is supplied locally —
instance search does not cross the `WithOne`/`Option` synonym. -/
theorem krohnRhodes_semigroup (S : Type) [Semigroup S] [Finite S] :
    ∃ L : List KRPrime,
      S ≺ₛ (wreathList (L.map KRPrime.toTransMon)).M ∧
      ∀ p ∈ L, ∀ G, p = KRPrime.grp G →
        IsSimpleGroup G.carrier ∧ G.carrier ≺ₛ S := by
  have : Finite (WithOne S) := inferInstanceAs (Finite (Option S))
  obtain ⟨L, hdiv, hfac⟩ := krohnRhodes_monoid (WithOne S)
  refine ⟨L, (withOne_transfer S).trans (monoidDivides_semigroupDivides hdiv), ?_⟩
  intro p hp G hpG
  obtain ⟨hsimple, hdivG⟩ := hfac p hp G hpG
  have : Nontrivial G.carrier := hsimple.toNontrivial
  exact ⟨hsimple, semigroupDivides_of_monoidDivides_withOne hdivG⟩

-- Sanity (spec §6): the theorem instantiates on a concrete finite
-- semigroup (every finite monoid is one).
open TransMon in
example : ∃ L : List KRPrime,
    ZMod 6 ≺ₛ (wreathList (L.map KRPrime.toTransMon)).M ∧
    ∀ p ∈ L, ∀ G, p = KRPrime.grp G →
      IsSimpleGroup G.carrier ∧ G.carrier ≺ₛ ZMod 6 :=
  krohnRhodes_semigroup _

/-- Sanity (spec §6), the case the semigroup form exists for: a genuine
NON-monoid semigroup. `LeftZero` is the two-element left-zero semigroup
`x * y = x`. A `def` rather than an `abbrev`, so its `Mul` never leaks
onto `Bool`. -/
private def LeftZero : Type := Bool

private instance : Semigroup LeftZero where
  mul x _ := x
  mul_assoc _ _ _ := rfl

private instance : Finite LeftZero := inferInstanceAs (Finite Bool)

-- It really has no identity: `e * x = x` forces `e = x` for every `x`.
example : ¬ ∃ e : LeftZero, ∀ x : LeftZero, e * x = x := by
  rintro ⟨e, he⟩
  have h1 : e = (show LeftZero from true) := he _
  have h2 : e = (show LeftZero from false) := he _
  have h3 : (show LeftZero from true) = (show LeftZero from false) := h1 ▸ h2
  exact Bool.noConfusion h3

open TransMon in
example : ∃ L : List KRPrime,
    LeftZero ≺ₛ (wreathList (L.map KRPrime.toTransMon)).M ∧
    ∀ p ∈ L, ∀ G, p = KRPrime.grp G →
      IsSimpleGroup G.carrier ∧ G.carrier ≺ₛ LeftZero :=
  krohnRhodes_semigroup _

end KRTheory
```

Note on `open TransMon in`: verified at planning time in the exact namespace layout above (statement elaborates inside `namespace KRTheory` with the per-declaration `open TransMon in`, `≺ₛ` scoped alongside). No adjustment expected.

- [ ] **Step 2: Wire the root import**

Append to `KRTheory.lean`: `import KRTheory.SemigroupVersion`

- [ ] **Step 3: Verify and commit**

```bash
lake build 2>&1 | tail -3
grep -rn "sorry" KRTheory/ KRTheory.lean
git add KRTheory KRTheory.lean
git commit -m "Prove the semigroup form of Krohn-Rhodes"
git push
```

Expected: green, zero warnings, empty grep.

---

### Task 5: Lean cleanup parks

**Files:**
- Modify: `KRTheory/FiniteMonoid.lean` (dead derivation), `KRTheory/KrohnRhodes.lean` (inert line), `KRTheory/Decomposition.lean` (`tag_mul` consolidation — droppable per Decision 7)

**Interfaces:** none produced; no statement may change.

- [ ] **Step 1: `FiniteMonoid.lean` — remove the dead derivation**

In `exists_gen_nonunit`'s properness branch, `hgen'` proves a proposition syntactically identical to the hypothesis `htop` introduced two lines above, so `hcmem` and `hgen'` are a circular detour. Replace the block

```lean
    intro htop
    have hcmem : c ∈ Submonoid.closure ((A.erase c : Finset M) : Set M) :=
      htop ▸ Submonoid.mem_top c
    have hgen' : Submonoid.closure ((A.erase c : Finset M) : Set M) = ⊤ := by
      rw [eq_top_iff, ← hAgen]
      refine Submonoid.closure_le.mpr fun a ha => ?_
      by_cases hac : a = c
      · exact hac ▸ hcmem
      · exact Submonoid.subset_closure (Finset.mem_erase.mpr ⟨hac, ha⟩)
    have h1 := hmin' (A.erase c) hgen'
```

with

```lean
    intro htop
    have h1 := hmin' (A.erase c) htop
```

leaving the following two lines (`h2`, `omega`) untouched.

- [ ] **Step 2: `KrohnRhodes.lean` — drop the inert line**

In `krohnRhodes_bar_of_units`, delete the line `  have := hX` (line ~74). `hX` is already a parameter, hence already a local instance for the `reset_div_flipFlops` instance search. If the build then fails to find `Nonempty T.X`, restore the line and note it in the report (the reviewer's claim that it is inert was verified empirically at review time, so a failure here is worth recording).

- [ ] **Step 3 (DROPPABLE — Decision 7): `Decomposition.lean` `tag_mul` consolidation**

`decompInv_of_mem`'s `mul` case contains ~60 lines duplicated across its branches (M7 park). Extract the repeated product-tag computation into a `private theorem tag_mul` above `decompInv_of_mem`, stating exactly the shared step, and replace each duplicated block with a call.

Rules: no public statement may change; `decomposition`'s statement and proof structure stay intact; the axiom certificate must be unchanged. **If this does not build after one honest attempt, `git checkout -- KRTheory/Decomposition.lean`, report it as dropped, and Task 7 re-parks it to post-v1.** Do not spend a second fix round on it.

- [ ] **Step 4: Verify and commit**

```bash
lake build 2>&1 | tail -3
lake env lean scripts/AxiomCertificate.lean | wc -l   # expect 18 (Task 6 adds the 19th)
git add KRTheory
git commit -m "Clear parked Lean cleanups from milestones 7 and 8"
git push
```

---

### Task 6: leanblueprint migration + proof-level `\leanok`

**Files:**
- Create: `blueprint/src/{web.tex,plastex.cfg,latexmkrc,blueprint.sty,extra_styles.css}`, `blueprint/src/macros/{common,web,print}.tex`, `blueprint/requirements.txt`
- Modify: `blueprint/src/print.tex`, all `blueprint/src/chapters/*.tex` (proof `\leanok`), `lakefile.toml`, `lake-manifest.json`, `blueprint/README.md`, `.gitignore`

**Interfaces:** produces a `leanblueprint web`-buildable blueprint whose graph is fully green; Task 7 wires CI.

- [ ] **Step 1: Scaffold with the tool**

The scaffolder needs a clean tree and a git repo. From the repo root:

```bash
git status --porcelain   # must be empty
python3 -m venv /tmp/bp && /tmp/bp/bin/pip install leanblueprint
```

Move our authored sources aside so the scaffolder cannot overwrite them, then run it:

```bash
mv blueprint/src/content.tex /tmp/content.tex.ours
mv blueprint/src/print.tex /tmp/print.tex.ours
mv blueprint/src/chapters /tmp/chapters.ours
PATH=/tmp/bp/bin:$PATH leanblueprint new
```

Answer the eleven prompts in order: title `The Krohn--Rhodes Theorem in Lean 4`; author `Juan Bono`; GitHub URL `https://github.com/juanbono/krohn-rhodes-theory`; project website `` (empty); API docs `` (empty); document class `report`; paper `a4paper`; show-proof buttons `y`; toc depth `3`; split level `0`; local toc depth `0`. Then `y` to "Proceed with blueprint creation?", `y` to "Modify lakefile and lake-manifest to allow checking declarations exist?" (this adds the `checkdecls` dependency `leanblueprint checkdecls` needs), and **`n` to any question offering to create a GitHub Actions workflow or Pages deployment** — CI is ours to wire (Task 7) and deployment is out of scope (Decision 5).

Then restore our sources over the generated placeholders:

```bash
mv /tmp/content.tex.ours blueprint/src/content.tex
mv /tmp/chapters.ours blueprint/src/chapters
mv /tmp/print.tex.ours blueprint/src/print.tex
```

- [ ] **Step 2: Reconcile the macro split (Decision 6)**

Our `print.tex` currently carries both the theorem environments and the marginpar definitions of `\lean`/`\leanok`/`\uses`/`\notready`. Split them:

  1. `macros/common.tex` (shared, overwriting the generated placeholder) gets the theorem environments exactly as our `print.tex` declares them today:

```latex
\newtheorem{theorem}{Theorem}[chapter]
\newtheorem{lemma}[theorem]{Lemma}
\newtheorem{proposition}[theorem]{Proposition}
\theoremstyle{definition}
\newtheorem{definition}[theorem]{Definition}
\newtheorem{example}[theorem]{Example}
\theoremstyle{remark}
\newtheorem{remark}[theorem]{Remark}
```

  2. `macros/print.tex` gets our marginpar macros (moved verbatim out of `print.tex`):

```latex
\newcommand{\lean}[1]{\marginpar{\tiny\ttfamily\detokenize{#1}}}
\newcommand{\leanok}{\marginpar{\tiny$\checkmark$}}
\newcommand{\uses}[1]{}
\newcommand{\notready}{}
```

  3. `macros/web.tex` stays as generated (the web `\lean`/`\leanok`/`\uses` come from the plasTeX plugin — do NOT redefine them there).
  4. Our `print.tex` keeps its `\documentclass[11pt]{report}`, its `amsmath,amssymb,amsthm` + `hyperref` preamble (pdflatex path, Decision 6), and now reads `\input{macros/common}` and `\input{macros/print}` in place of the inline definitions, keeping `\input{content}` and the title/author block.
  5. The generated `latexmkrc` sets xelatex; since we keep pdflatex, delete `blueprint/src/latexmkrc` (our CI calls `latexmk -pdf print.tex` directly).

- [ ] **Step 3: Pin the Python toolchain**

Create `blueprint/requirements.txt`:

```
leanblueprint
plastexdepgraph
plastexshowmore
```

(Deliberately unpinned to versions here: the versions are exercised by CI in Task 7. If the CI web build fails on a toolchain regression, pin the three packages plus `plasTeX` to the newest versions that build, and record the pins in this file with a one-line comment.)

- [ ] **Step 4: Proof-level `\leanok` (the green-graph requirement)**

A dependency-graph node is fully green only when the proof, not just the statement, is marked formalized. There are 36 `proof` environments across `blueprint/src/chapters/*.tex` and none carries `\leanok`. Every one of them corresponds to a Lean proof that is complete (the project is sorry-free), so add `\leanok` as the first line inside each `\begin{proof}`:

```bash
grep -c 'begin{proof}' blueprint/src/chapters/*.tex   # inventory before
```

For each `\begin{proof}` in each chapter, insert `  \leanok` on the line immediately after it. Two exceptions to check individually rather than stamping blindly:
  - proofs of statements whose `\lean{}` points at a Mathlib declaration (`lem:finite-unit`, `lem:card-subtype-lt`, `lem:idem-pow`'s neighbours in `finitemonoid.tex`) — these are formalized (by Mathlib) and DO get `\leanok`;
  - any proof whose statement lacks `\leanok` — there should be none left after M8; if one appears, do NOT stamp it, and report it.

Verify the count afterwards: `grep -c 'leanok' blueprint/src/chapters/*.tex` should have risen by exactly the number of `\begin{proof}` occurrences stamped.

- [ ] **Step 5: Ignore build outputs; update the README**

Add to `.gitignore`:

```
blueprint/web/
blueprint/print/
blueprint/src/web.paux
blueprint/lean_decls
```

In `blueprint/README.md`, replace the `TODO(post-v1 ...)` paragraph with:

```markdown
Two build paths:

- `latexmk -pdf print.tex` (from `src/`) — the PDF, pdflatex.
- `leanblueprint web` (from the repo root) — the web version with the
  dependency graph. Needs `pip install -r blueprint/requirements.txt`
  AND a TeX installation: plasTeX resolves `\input` via `kpsewhich`, so
  without TeX every chapter silently fails to load.

`leanblueprint checkdecls` verifies every `\lean{...}` name exists; it
needs a built project (`lake build`) and a prior `leanblueprint web`.

Publishing the web version to GitHub Pages is deliberately not wired up
(a publication decision, not a correctness one); CI builds it and
uploads it as an artifact.
```

- [ ] **Step 6: Commit**

The local machine may have no TeX (see this plan's probe findings), in which case `leanblueprint web` cannot be verified here — Task 7's CI is the verification point. If TeX IS available locally, run it and report the result:

```bash
PATH=/tmp/bp/bin:$PATH leanblueprint web 2>&1 | grep -i "not found" | head
```

```bash
git add -A
git commit -m "Migrate blueprint to the leanblueprint toolchain"
git push
```

---

### Task 7: CI, certificate, milestone close

**Files:**
- Modify: `.github/workflows/ci.yml`, `scripts/AxiomCertificate.lean`

**Interfaces:** consumes everything; produces the v1 acceptance state.

- [ ] **Step 0a: Stamp `semigroup.tex` (the last `\leanok` gap)**

`blueprint/src/chapters/semigroup.tex` was written in Task 2, before its Lean existed, so it carries no `\leanok` at all — 6 `\lean{}` macros and 5 `proof` environments, all now formalized by Task 4. Task 6 correctly declined to stamp its proofs while the statements were unstamped. Close both halves here (the same move M7's close commit made):

  1. Add `\leanok` after each of the SIX `\lean{...}` macros (`def:semdiv`, `lem:semdiv-preorder`, `lem:semdiv-of-mdiv`, `lem:withone-transfer`, `lem:semdiv-group-withone`, `thm:krohnrhodes-semigroup`), matching the placement style used in the other chapters.
  2. Add `\leanok` as the first line inside each of the FIVE `\begin{proof}` environments in that file.

The two remarks (`rem:semdiv-nontrivial`, `rem:semigroup-empty`) have no `\lean{}` and get nothing. Verify afterwards: `grep -c '\\leanok' blueprint/src/chapters/semigroup.tex` returns 11, and repo-wide the count rises from 94 to 105 with 41 proof environments all stamped.

- [ ] **Step 0: Stale docstring from Task 5's refactor**

`KRTheory/Decomposition.lean`, the docstring of the relocated `tag_mul` (~line 289), still says it was *"isolated from `decompInv_of_mem`'s mul case (item 2 there) so `decompMap_mul` can cite it"*. Task 5 deleted that inline "item 2", and `decompInv_of_mem` is now a caller rather than the source. Reword that clause to *"isolated so both `decompInv_of_mem`'s mul case and `decompMap_mul` can cite it"*, changing nothing else in the docstring or the theorem. (Task 5 deliberately left this to preserve the byte-identity that made its refactor auditable.)

- [ ] **Step 1: Axiom certificate**

Append to `scripts/AxiomCertificate.lean`:

```lean
#print axioms krohnRhodes_semigroup
```

Update `.github/workflows/ci.yml`'s count assertion from `-eq 18` to `-eq 19` and its adjacent comment ("19 = current certificate entries"). Verify locally:

```bash
lake env lean scripts/AxiomCertificate.lean | wc -l          # 19
lake env lean scripts/AxiomCertificate.lean | grep -v "propext\|Classical.choice\|Quot.sound"   # only the no-axiom line, if any
```

- [ ] **Step 2: Web-build CI**

The web build needs a TeX installation (plasTeX's `kpsewhich` lookup), a built Lean project (for `checkdecls`), Python, and graphviz. The existing `build` job already has the Lean build and its cache, so extend THAT job — do not create a second Lean build. After its existing steps, add:

```yaml
      - name: Install blueprint toolchain
        run: |
          sudo apt-get update
          sudo apt-get install -y --no-install-recommends \
            texlive-latex-base texlive-latex-extra graphviz libgraphviz-dev
          python3 -m pip install --upgrade pip
          python3 -m pip install -r blueprint/requirements.txt
      - name: Build blueprint web version
        run: |
          set -o pipefail
          leanblueprint web 2>&1 | tee web.log
          # plasTeX reports missing inputs as warnings, not failures
          ! grep -q "File not found" web.log
      - name: Check blueprint declarations exist
        run: leanblueprint checkdecls
      - name: Upload blueprint web
        uses: actions/upload-artifact@v4
        with:
          name: blueprint-web
          path: blueprint/web
```

Leave the existing `blueprint` (PDF) job untouched. Do NOT add a Pages deployment step (Decision 5).

- [ ] **Step 3: Push and watch**

```bash
git add -A
git commit -m "Close milestone 9: certificate, blueprint web CI"
git push
gh pr checks <PR> --watch
```

Expected: build job green (including the two new blueprint steps), PDF job green. Known failure modes and their responses:
  - `File not found` in `web.log` → a chapter did not load; check `\input` paths and that TeX installed.
  - apt hang → cancel and re-run the job once (`gh run rerun --failed`); this is a known transient in this project.
  - a plasTeX/plugin regression → pin versions in `blueprint/requirements.txt` (Task 6 Step 3) and push again.
  - `checkdecls` failure → a `\lean{...}` name does not exist; fix the NAME in the blueprint (never delete the annotation), or report if the declaration was renamed.

- [ ] **Step 4: Verify the graph is green**

Download the artifact (or inspect locally if TeX is available) and confirm the dependency graph shows no non-green node:

```bash
gh run download <run-id> -n blueprint-web -D /tmp/bpweb
grep -o 'class="[^"]*"' /tmp/bpweb/dep_graph_document.html | sort | uniq -c | head -20
```

Every theorem/lemma/definition node must carry the fully-proved styling; any node that does not is either missing a statement `\leanok` or a proof `\leanok` (Task 6 Step 4) — fix and push. Record the final node counts in the report.

- [ ] **Step 5: v1 acceptance sweep**

Verify spec §1's five items explicitly and record each with its evidence in the report:

```bash
lake build 2>&1 | tail -3
grep -rn "sorry" KRTheory/ KRTheory.lean
lake env lean scripts/AxiomCertificate.lean | tail -3
gh pr checks <PR>
```

  1. `krohnRhodes` proved — M8, in the certificate.
  2. `krohnRhodes_monoid` proved — M8, in the certificate.
  3. `krohnRhodes_semigroup` proved — Task 4, now in the certificate.
  4. `#print axioms` on all three ⊆ {`propext`, `Classical.choice`, `Quot.sound`} — certificate output.
  5. CI builds project + blueprint (PDF and web); graph fully green — Steps 2–4.

- [ ] **Step 6 (controller): final review, memory, handoff**

SDD final whole-branch review serves as the milestone review. After it: update `kr-theory-project.md` (v1 COMPLETE; record what shipped, any re-parked items such as a dropped `tag_mul` refactor, and the post-v1 ledger from spec §9 — aperiodic corollary, automata cascade, holonomy, size bounds, Green's relations, upstreaming, paper). Surface to the user: the Pages-deployment follow-up (one workflow step, their call) and the merge sequence for the seven stacked PRs.

---

## Self-review (performed at planning time)

- **Spec coverage:** §1 item 3 → Task 4; §1 item 5 → Tasks 6–7 (as clarified by Decision 5, recorded in Task 1); §3.2 → Task 4's `≺ₛ` + feeder; §3.9 target signature and its deferred question → Task 4 + Task 1 Step 1; §4.3 row → Task 1 Step 3; §7 row 9 ("all of §1 done; axiom certificate") → Task 7 Steps 1, 5. Parked items from M7/M8 → Tasks 3 and 5.
- **Placeholder scan:** every Lean and LaTeX step carries full content; the two open-ended spots are bounded and stated as such (Task 5 Step 3 is explicitly droppable; Task 6 Step 3's version pins are deferred to CI evidence with a stated fallback).
- **Type consistency:** `withOne_transfer S` and `monoidDivides_semigroupDivides hdiv` feed `SemigroupDivides.trans` in that order; `semigroupDivides_of_monoidDivides_withOne` takes `[Group G] [Nontrivial G]` and is called under `hsimple.toNontrivial`; `krohnRhodes_monoid (WithOne S)` needs the local `Finite` instance introduced one line earlier. All exercised in the probe.
