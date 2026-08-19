# Krohn–Rhodes Milestone 8 (Main Induction / `KrohnRhodes.lean`) Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Prove `krohnRhodes` (transformation form, strong version) and `krohnRhodes_monoid` (abstract finite-monoid form) — [DKS] Theorem 4.1 — by strong induction on `|M|`, gluing milestone 6's group case with milestone 7's decomposition theorem.

**Architecture:** One new file `KRTheory/KrohnRhodes.lean` on branch `milestone-8` (stacked on `milestone-7`, PR #7), plus four small prelims added to existing files (`FiniteMonoid.lean` ×3, `LocalDivisor.lean` ×1). The induction predicate Q(T) of spec §3.9 is the theorem `krohnRhodes_bar`; its group branch is a separate lemma `krohnRhodes_bar_of_units` (no faithfulness needed — the M6 strengthening carries through). M8 is a *gluing* milestone: no new coverings are built, no wreath elements are manipulated — every step composes existing division facts, so the M5–M7 projected-type combat is expected to be light here.

**Tech Stack:** Lean 4 (`v4.34.0-rc1`), Mathlib pinned `ac4c4bff`, existing CI. Base: `milestone-7` @ `6fca15a`; implementation on new `milestone-8`.

**Spec:** `docs/superpowers/specs/2026-08-17-krohn-rhodes-formalization-design.md` — §3.9 (the induction and target signatures), §3.7 (group-case pieces), §3.6 (prelims sentence), §4.3 `FiniteMonoid.lean`/`LocalDivisor.lean`/`KrohnRhodes.lean` rows, §7 row 8 acceptance ("`krohnRhodes`, `krohnRhodes_monoid`").

## Global Constraints

- All Lean inside `namespace KRTheory` (FiniteMonoid) / `namespace KRTheory`+`namespace TransMon` (everything else); `Finite` bundling; `Nat.card`; docstrings on every public declaration citing blueprint labels; zero-warning builds; no `sorry` at task end; plain commits, no trailers (never `Co-Authored-By`).
- Formalization-TDD: statements below are FIXED (each was elaboration-verified by this planning session's probe file); tactic scripts have latitude. The two main-theorem signatures must match spec §3.9 verbatim (modulo the named-hypothesis spellings noted in Task 6).
- Deprecations/linters at this pin (probe-observed): `push_neg` is deprecated → use `push Not`; the `haveILetI` style linter rejects `letI`/`haveI` in Prop-goal proofs → use `let` / `have` (a plain local hypothesis of class type IS found by instance search).
- Instance-search landmine (§4.1 amendment note): instance search will NOT unfold the semireducible projection `(regular M).X`, so `Nonempty (regular M).X` must be provided manually (`have : Nonempty (regular M).X := ⟨(1 : M)⟩`) — it will not be found from `Nonempty M`.
- Deeply-projected types (M5–M7 intel): expected mild here (gluing only). Where the IH wants `Nat.card (localDivisor T c).M` and a lemma supplies `Nat.card (LocalDivisor c)` (defeq), `exact` should unify; if it balks, bridge with `show`/`have` at the reduced type — never restate a theorem.
- Probe-verified (this planning session, all green): Mathlib's `groupOfIsUnit` exists (`Mathlib/Algebra/Group/Units/Defs.lean`, `{ hM with … }` — it EXTENDS the ambient monoid instance) and `regular T.M` is defeq-stable across it (glue through `StrongDivides.trans`/`.wreath` typechecks, and `H.carrier ≺ₘ T.M` transports back to the bundled instance); the induction skeleton `revert…; generalize hcard : Nat.card T.M = n; induction n using Nat.strong_induction_on generalizing T` produces the IH `∀ m, m < n → ∀ T', Nat.card T'.M = m → T'.Faithful → Nonempty T'.X → …`; both spec §3.9 target statements elaborate verbatim against a `KRPrime` inductive in `Type 1`; `Finset.exists_min_image` + `let := Fintype.ofFinite M` yields a minimal-cardinality generating finset; `Finite.card_subtype_lt (p := (· ∈ N))` proves the submonoid card drop; the closure-induction proof of `isUnit_of_generators_units` and the full `exists_gen_nonunit` proof compile as written below; `rw [List.map_append]` + `wreathList_append` and `rw [List.map_replicate, KRPrime.toTransMon_flipflop]` close the list glue (the equation lemmas are REQUIRED — the match-compiled `toTransMon` does not `rfl`-close under `rw`).

## Decisions this plan records

1. **Measure: plain strong induction on `|M|`** — spec §3.9 announces lex `(|M|, |X|)`, but both recursive calls strictly shrink `|M|` (`|Mc| < |M|` by `localDivisor_card_lt`, `|N| < |M|` by the new `card_submonoid_lt_of_ne_top`) and the group case recurses no further (M6 fused its own induction into `transfGroup_div_wreath_simples`). The lex second component is never exercised. Recorded as a spec §3.9 note (Task 1) and blueprint `rem:kr-measure` (Task 2); the state-set growth `X ⊔ N` remains the reason no `|X|`-leading measure could work.
2. **`groupOfIsUnit` comes from Mathlib** — the §8 risk row "build it by EXTENDING the bundled instance" is discharged: Mathlib's `groupOfIsUnit` is literally `{ hM with … }` and the probe confirmed `regular T.M` defeq-stability. Risk row updated to RESOLVED (Task 1).
3. **The whole minimal-generating-set analysis is ONE decidability-free prelim** `exists_gen_nonunit : (¬ ∀ m : M, IsUnit m) → ∃ N c, ¬ IsUnit c ∧ N ≠ ⊤ ∧ closure (↑N ∪ {c}) = ⊤`. `Finset.erase` needs `DecidableEq`, so all Finset work (minimal-cardinality set, erase, card arithmetic) stays INSIDE the proof behind `classical`; the statement mentions only `Submonoid`s. This is exactly the tuple `decomposition` consumes.
4. **Prelim placement:** monoid-level prelims → `FiniteMonoid.lean` (`isUnit_of_generators_units` per spec §4.3 — with `omit [Finite M]`, it needs no finiteness; `card_submonoid_lt_of_ne_top` mirroring M6's subgroup name; `exists_gen_nonunit`). `localDivisor_X_nonempty` → `LocalDivisor.lean` (its subject home, blueprint-visible). The other two nonemptiness facts are inlined at call sites (`⟨Sum.inr 1⟩` for `rightFactor`, `⟨(1 : M)⟩` for `regular`) — too trivial to name.
5. **Names:** master lemma `krohnRhodes_bar` (this IS Q(T): `T.bar ≺ …`); group branch `krohnRhodes_bar_of_units` (takes `Nonempty T.X` + `∀ m, IsUnit m`, NOT faithfulness). The factor condition is inlined in all statements (spec-verbatim), not extracted into a def.
6. **`KRPrime` equation lemmas are simp lemmas** (`toTransMon_flipflop`, `toTransMon_grp`): probe showed `rw`'s closing `rfl` does not reduce the match-compiled `toTransMon` applied to a literal constructor (term-level `rfl` does — the lemmas are `:= rfl`).
7. **`exists_pow_idempotent` stays unused** — M8 planning confirmed the induction has no use for it; its consumer remains the v2 aperiodic corollary. §3.6's "unless M8 finds a use" is closed (Task 1).

---

### Task 1: Spec amendments + branch/PR

**Files:**
- Modify: `docs/superpowers/specs/2026-08-17-krohn-rhodes-formalization-design.md` (§3.6 close-out, §3.9 measure note, §4.3 three rows, §8 row resolution)

**Interfaces:** none produced; every edit enumerated below.

- [ ] **Step 0: Create the branch**

```bash
git checkout milestone-7
git checkout -b milestone-8
```

- [ ] **Step 1: Spec §3.9 measure note**

After the Claim paragraph (the one beginning `**Claim: Q holds for all faithful finite T with nonempty states**, by strong induction on (|M|, |X|) lexicographically.` and ending `…is excluded.)`), insert a new paragraph:

```markdown
**Note (2026-08-18, M8 planning):** the formal induction is plain strong induction on |M| — both recursive calls strictly shrink |M| (3.6.2 for Mc; proper-submonoid counting for N) and the group case recurses no further (its induction was fused into §3.7's `transfGroup_div_wreath_simples` at M6), so the lex second component is never exercised. The state-set growth X ⊔ N remains the reason no |X|-leading measure could work.
```

- [ ] **Step 2: Spec §3.6 close-out**

In the §3.6 prelims sentence, replace `— its consumer is the v2 aperiodic corollary (§9) unless M8 finds a use.)` with `— its consumer is the v2 aperiodic corollary (§9); M8 planning confirmed the induction has no use for it.)`.

- [ ] **Step 3: Spec §4.3 rows**

  1. `FiniteMonoid.lean` row: replace with

     ```markdown
     | `FiniteMonoid.lean` | `exists_pow_idempotent`, `isUnit_of_mul_eq_one_right/left` (finite), `isUnit_of_generators_units` (units-only generating set ⇒ group), `card_submonoid_lt_of_ne_top`, `exists_gen_nonunit` (minimal-generating-set split) |
     ```

  2. `TransMon/LocalDivisor.lean` row: append `, \`localDivisor_X_nonempty\`` before the closing `|`.
  3. `KrohnRhodes.lean` row: replace with

     ```markdown
     | `KrohnRhodes.lean` | `KRPrime` (consuming `GroupCase.BundledFinGroup`), `KRPrime.toTransMon` (+ simp equation lemmas), `krohnRhodes_bar_of_units` (group branch), `krohnRhodes_bar` (the induction), `krohnRhodes`, `krohnRhodes_monoid` |
     ```

- [ ] **Step 4: Spec §8 risk row resolution**

Replace the row

```markdown
| M8's group branch needs `Group T.M` from `∀ m, IsUnit m` | Build it by EXTENDING the bundled instance (`{ ‹Monoid T.M› with inv := … }`) so `regular T.M` stays defeq-stable; adjacent to the deferred `isUnit_of_generators_units` |
```

with

```markdown
| M8's group branch needs `Group T.M` from `∀ m, IsUnit m` (RESOLVED 2026-08-18, M8 planning) | Mathlib's `groupOfIsUnit` already extends the ambient instance (`{ hM with … }`); `regular T.M` defeq-stability across it probe-verified |
```

- [ ] **Step 5: Commit, open the stacked draft PR**

```bash
git add docs/superpowers/specs
git commit -m "Record M8 spec amendments: measure note, prelim rows, resolved group-bridge risk"
git push -u origin milestone-8
gh pr create --draft --base milestone-7 --title "Milestone 8: the Krohn-Rhodes theorem" \
  --body "Tracking PR so CI runs per push. Merge policy stays manual."
```

Expected: PR #7 open; CI green (doc-only).

---

### Task 2: Blueprint chapters

**Files:**
- Modify: `blueprint/src/chapters/finitemonoid.tex` (replace the `\notready` remark with three lemmas)
- Modify: `blueprint/src/chapters/localdivisor.tex` (append one lemma)
- Create: `blueprint/src/chapters/krohnrhodes.tex`
- Modify: `blueprint/src/content.tex` (add `\input{chapters/krohnrhodes}` after `chapters/decomposition`)

**Interfaces:**
- Produces labels Tasks 3–6 cite in docstrings: `lem:units-generated`, `lem:submonoid-card`, `lem:gen-split`, `lem:localdiv-nonempty`, `ch:krohnrhodes`, `def:krprime`, `lem:kr-group-branch`, `thm:kr-bar`, `rem:kr-measure`, `thm:krohnrhodes`, `thm:krohnrhodes-monoid`. Task 7 stamps `\leanok`.

- [ ] **Step 1: `finitemonoid.tex` — replace the deferred remark**

Delete the block

```latex
\begin{remark}[Deferred to milestone 8]
  \notready
  The remaining \S 3.6 preliminary --- a monoid generated by units is a
  group --- is consumed only by the main induction and is deliberately
  not formalized yet.
\end{remark}
```

and put in its place:

```latex
\begin{lemma}[Units-generated monoids are groups]\label{lem:units-generated}
  \lean{KRTheory.isUnit_of_generators_units}
  If a monoid $M$ is generated by a set of units, every element of $M$
  is a unit. (No finiteness needed.)
\end{lemma}
\begin{proof}
  Induction over the submonoid closure: $1$ is a unit, and a product
  of units is a unit.
\end{proof}

\begin{lemma}[Proper submonoids are smaller]\label{lem:submonoid-card}
  \lean{KRTheory.card_submonoid_lt_of_ne_top}
  \uses{lem:card-subtype-lt}
  A proper submonoid $N \lneq M$ of a finite monoid has $|N| < |M|$.
\end{lemma}
\begin{proof}
  Properness produces a point outside the carrier and
  Lemma~\ref{lem:card-subtype-lt} counts. (The subgroup analogue in
  the group chapter went through the quotient's cardinality; this one
  is bare counting.)
\end{proof}

\begin{lemma}[Generator split]\label{lem:gen-split}
  \lean{KRTheory.exists_gen_nonunit}
  \uses{lem:units-generated}
  If a finite monoid $M$ has a non-unit, then there are a proper
  submonoid $N \lneq M$ and a non-unit $c$ with
  $\langle N \cup \{c\} \rangle = M$.
\end{lemma}
\begin{proof}
  Pick a generating set $A$ of minimal cardinality (one exists: $M$
  itself generates, and cardinalities are well-ordered). If every
  element of $A$ were a unit, Lemma~\ref{lem:units-generated} would
  make every element of $M$ a unit; so some $c \in A$ is not a unit.
  Set $N := \langle A \setminus \{c\} \rangle$. If $c$ lay in $N$,
  then $A \setminus \{c\}$ would already generate $M$, beating $A$'s
  minimality; hence $N$ is proper. Finally
  $A \subseteq N \cup \{c\}$, so $N \cup \{c\}$ generates.
\end{proof}
```

- [ ] **Step 2: `localdivisor.tex` — append after `lem:localdiv-divides`**

```latex
\begin{lemma}[Nonempty local states]\label{lem:localdiv-nonempty}
  \lean{KRTheory.TransMon.localDivisor_X_nonempty}
  \uses{def:localdiv-tm}
  If $X \neq \emptyset$ then $X{\cdot}c \neq \emptyset$.
\end{lemma}
\begin{proof}
  $x \cdot c$ witnesses, for any $x \in X$.
\end{proof}
```

- [ ] **Step 3: Write `blueprint/src/chapters/krohnrhodes.tex`**

```latex
\chapter{The Krohn--Rhodes theorem}\label{ch:krohnrhodes}

This chapter assembles the main induction --- the Krohn--Rhodes
theorem, [DKS] Theorem~4.1 --- from the decomposition theorem
(Chapter~\ref{ch:decomposition}) and the group case
(Chapter~\ref{ch:groupcase}).

\begin{definition}[Krohn--Rhodes primes]\label{def:krprime}
  \lean{KRTheory.TransMon.KRPrime, KRTheory.TransMon.KRPrime.toTransMon}
  \uses{def:flipflop,def:bundledfingroup,def:regular}
  A \emph{Krohn--Rhodes prime} is either the flip-flop symbol or a
  bundled finite group $G$; the associated transformation monoid is
  the flip-flop $U_2$, respectively the regular representation
  $(G, G)$. Carrying canonical objects keeps the main statements free
  of any isomorphism API (spec \S 3.9).
\end{definition}

\begin{lemma}[Group branch]\label{lem:kr-group-branch}
  \lean{KRTheory.TransMon.krohnRhodes_bar_of_units}
  \uses{def:krprime,lem:group-bar,lem:reset-div-flipflops,lem:group-series,lem:wreath-mono,lem:wreathList-append,lem:sdiv-preorder}
  Let $T = (X, M)$ with $X \neq \emptyset$ and every element of $M$ a
  unit. Then there is a list $L$ of primes with
  $\bar{T} \prec \wr L$, every group factor being a nontrivial finite
  simple group dividing $M$. Faithfulness is not required
  (Lemma~\ref{lem:group-bar} does not need it).
\end{lemma}
\begin{proof}
  $M$ carries a group structure (each element is a unit; the inverse
  is read off the unit witness --- Mathlib's \texttt{groupOfIsUnit},
  which extends the ambient monoid structure in place).
  Lemma~\ref{lem:group-bar} gives
  $\bar{T} \prec U(X) \wr (M, M)$.
  Lemma~\ref{lem:reset-div-flipflops} resolves $U(X)$ into flip-flops
  (this is where $X \neq \emptyset$ enters);
  Lemma~\ref{lem:group-series} resolves $(M, M)$ into simple-group
  regulars dividing $M$. Glue with wreath monotonicity
  (Lemma~\ref{lem:wreath-mono}), list concatenation
  (Lemma~\ref{lem:wreathList-append}), and transitivity.
\end{proof}

\begin{theorem}[The induction]\label{thm:kr-bar}
  \lean{KRTheory.TransMon.krohnRhodes_bar}
  \uses{def:krprime,lem:kr-group-branch,lem:gen-split,lem:submonoid-card,thm:decomposition,lem:localdiv-faithful,lem:localdiv-card,lem:localdiv-divides,lem:localdiv-nonempty,lem:right-factor-faithful,lem:mdiv-of-submonoid,lem:mdiv-preorder,lem:sdiv-preorder,lem:wreath-mono,lem:wreathList-append}
  For every faithful finite $T = (X, M)$ with $X \neq \emptyset$
  there is a list $L$ of primes such that $\bar{T} \prec \wr L$, with
  every group factor a nontrivial finite simple group dividing $M$.
  (This is the predicate $Q(T)$ of spec \S 3.9.)
\end{theorem}
\begin{proof}
  Strong induction on $|M|$ (Remark~\ref{rem:kr-measure}). If every
  element of $M$ is a unit, Lemma~\ref{lem:kr-group-branch} closes
  the case directly. Otherwise the generator split
  (Lemma~\ref{lem:gen-split}) yields a proper submonoid $N \lneq M$
  and a non-unit $c$ with $\langle N \cup \{c\} \rangle = M$, and
  Theorem~\ref{thm:decomposition} gives
  \[
    \bar{T} \;\prec\; \overline{(X{\cdot}c,\, M_c)} \,\wr\,
      \overline{(X \sqcup N,\, N)} .
  \]
  The left factor is faithful (Lemma~\ref{lem:localdiv-faithful}),
  has nonempty states (Lemma~\ref{lem:localdiv-nonempty}) and a
  strictly smaller monoid (Lemma~\ref{lem:localdiv-card}), so the
  induction hypothesis applies; its group factors divide $M_c$, hence
  $M$ by Lemma~\ref{lem:localdiv-divides} and transitivity
  (Lemma~\ref{lem:mdiv-preorder}). The right factor is faithful
  (Lemma~\ref{lem:right-factor-faithful}), has nonempty states
  ($1 \in N$) and a strictly smaller monoid
  (Lemma~\ref{lem:submonoid-card}); its group factors divide
  $N \le M$ (Lemma~\ref{lem:mdiv-of-submonoid}). Concatenate the two
  lists and glue with Lemmas~\ref{lem:wreath-mono}
  and~\ref{lem:wreathList-append}.
\end{proof}

\begin{remark}[The measure]\label{rem:kr-measure}
  Spec \S 3.9 announces a lexicographic induction on $(|M|, |X|)$.
  Both recursive calls strictly shrink $|M|$, and the group case
  recurses no further --- its composition-series induction was fused
  into Lemma~\ref{lem:group-series} at milestone 6. Plain strong
  induction on $|M|$ therefore suffices; the second component is
  never exercised. The state set still grows on the right factor
  ($X \sqcup N$), which is why no measure led by $|X|$ could work.
\end{remark}

\begin{theorem}[Krohn--Rhodes, transformation form]\label{thm:krohnrhodes}
  \lean{KRTheory.TransMon.krohnRhodes}
  \uses{def:krprime,thm:kr-bar,lem:bar-divides,lem:sdiv-preorder}
  Every faithful finite transformation monoid $T = (X, M)$ with
  $X \neq \emptyset$ strongly divides an iterated wreath product of
  Krohn--Rhodes primes whose group factors are nontrivial finite
  simple groups dividing $M$ ([DKS] Theorem~4.1, strong form).
  Nonemptiness is necessary: an empty-state transformation monoid
  strongly divides no wreath of primes (their state sets are
  nonempty).
\end{theorem}
\begin{proof}
  $T \prec \bar{T}$ (Lemma~\ref{lem:bar-divides}), then
  Theorem~\ref{thm:kr-bar}, then transitivity.
\end{proof}

\begin{theorem}[Krohn--Rhodes, monoid form]\label{thm:krohnrhodes-monoid}
  \lean{KRTheory.TransMon.krohnRhodes_monoid}
  \uses{def:krprime,thm:krohnrhodes,def:regular,lem:regular-faithful,lem:sdiv-mdiv}
  Every finite monoid $M$ divides (as a monoid) the wreath-product
  monoid of a list of Krohn--Rhodes primes whose group factors are
  nontrivial finite simple groups dividing $M$.
\end{theorem}
\begin{proof}
  Apply Theorem~\ref{thm:krohnrhodes} to the regular representation
  $(M, M)$ --- faithful by Lemma~\ref{lem:regular-faithful}, states
  nonempty since $1 \in M$ --- and extract the monoid division with
  the glue lemma (Lemma~\ref{lem:sdiv-mdiv}).
\end{proof}
```

- [ ] **Step 4: Wire, cross-check labels, commit, CI**

Append to `blueprint/src/content.tex` after `\input{chapters/decomposition}`:

```latex
\input{chapters/krohnrhodes}
```

Run the house label/uses cross-check over the three touched chapters:

```bash
cd blueprint/src && grep -ho '\\label{[^}]*}' chapters/*.tex | sed 's/\\label{\(.*\)}/\1/' | sort > /tmp/labels.txt && grep -ho '\\uses{[^}]*}' chapters/krohnrhodes.tex chapters/finitemonoid.tex chapters/localdivisor.tex | sed 's/\\uses{//;s/}//' | tr ',' '\n' | sed 's/^[[:space:]]*//;s/[[:space:]]*$//' | sort -u | while read u; do grep -qx "$u" /tmp/labels.txt || echo "MISSING: $u"; done; cd ../..
```

Expected: no MISSING. Then:

```bash
git add blueprint/src
git commit -m "Add Krohn-Rhodes blueprint chapter; state M8 prelims"
git push
gh pr checks 7 --watch
```

Expected: blueprint job green. **This chapter is the milestone's math gate — review it before any Lean.**

---

### Task 3: Prelims in Lean

**Files:**
- Modify: `KRTheory/FiniteMonoid.lean` (three theorems before `end KRTheory`; extend the file docstring's last sentence)
- Modify: `KRTheory/TransMon/LocalDivisor.lean` (one theorem after `localDivisor_faithful`)

**Interfaces:**
- Consumes: `Finite.card_subtype_lt`, `Submonoid.closure_induction`, `Finset.exists_min_image`, `Fintype.ofFinite` (Mathlib); `localDivisor` (M5).
- Produces (Task 6 consumes exactly these):
  - `KRTheory.isUnit_of_generators_units (A : Set M) (hA : Submonoid.closure A = ⊤) (h : ∀ a ∈ A, IsUnit a) (m : M) : IsUnit m` — section `{M : Type} [Monoid M]`, `omit [Finite M]`
  - `KRTheory.card_submonoid_lt_of_ne_top (N : Submonoid M) (h : N ≠ ⊤) : Nat.card ↥N < Nat.card M`
  - `KRTheory.exists_gen_nonunit (hM : ¬ ∀ m : M, IsUnit m) : ∃ (N : Submonoid M) (c : M), ¬ IsUnit c ∧ N ≠ ⊤ ∧ Submonoid.closure (↑N ∪ {c}) = ⊤`
  - `KRTheory.TransMon.localDivisor_X_nonempty (T : TransMon) (c : T.M) (hX : Nonempty T.X) : Nonempty (localDivisor T c).X`

- [ ] **Step 1: `FiniteMonoid.lean` — the three prelims**

In the file docstring, replace `this file holds the idempotent-power lemma, still an upstream candidate (spec §9).` with `this file holds the idempotent-power lemma (still an upstream candidate, spec §9) and milestone 8's generating-set prelims.`

Insert before `end KRTheory` (after the existing examples):

**Carve-out candidate (user):** `isUnit_of_generators_units` is a self-contained 6-liner that teaches `Submonoid.closure_induction` — the workhorse eliminator of this project. If the user opted in, pause here and let them write its proof from the statement + the hint "induct over the closure membership; the three cases are the generator case, `1`, and products".

```lean
omit [Finite M] in
/-- A monoid generated by units consists of units [blueprint
`lem:units-generated`]: closure induction — `1` is a unit and units
multiply. The §3.9 branch fact: if the non-group branch runs, some
generator is a non-unit. Needs no finiteness. -/
theorem isUnit_of_generators_units (A : Set M)
    (hA : Submonoid.closure A = ⊤) (h : ∀ a ∈ A, IsUnit a) (m : M) :
    IsUnit m := by
  have hm : m ∈ Submonoid.closure A := hA ▸ Submonoid.mem_top m
  induction hm using Submonoid.closure_induction with
  | mem a ha => exact h a ha
  | one => exact isUnit_one
  | mul a b _ _ iha ihb => exact iha.mul ihb

/-- Proper submonoids of a finite monoid are strictly smaller
[blueprint `lem:submonoid-card`] — the right factor's measure drop in
the milestone-8 induction. Bare counting via `Finite.card_subtype_lt`
(unlike the subgroup version in `GroupCase.lean`, which went through
the quotient's cardinality). -/
theorem card_submonoid_lt_of_ne_top (N : Submonoid M) (h : N ≠ ⊤) :
    Nat.card ↥N < Nat.card M := by
  obtain ⟨m, hm⟩ : ∃ m, m ∉ N := by
    by_contra h'
    push Not at h'
    exact h ((Submonoid.eq_top_iff' N).mpr h')
  exact Finite.card_subtype_lt (p := (· ∈ N)) hm

/-- The generator split [blueprint `lem:gen-split`]: a finite monoid
with a non-unit is generated by a proper submonoid `N` together with a
non-unit `c` — exactly the hypothesis tuple of [DKS] Thm 3.1
(`decomposition`). Proof: a minimal-cardinality generating finset has
a non-unit element `c` (else `isUnit_of_generators_units` makes every
element a unit), and `N := ⟨A ∖ {c}⟩` is proper by minimality. All
`Finset`/decidability bookkeeping stays inside the proof — the
statement is decidability-free. -/
theorem exists_gen_nonunit (hM : ¬ ∀ m : M, IsUnit m) :
    ∃ (N : Submonoid M) (c : M), ¬ IsUnit c ∧ N ≠ ⊤ ∧
      Submonoid.closure (↑N ∪ {c}) = ⊤ := by
  classical
  let _ := Fintype.ofFinite M
  -- minimal-cardinality generating finset
  obtain ⟨A, hA, hmin⟩ := Finset.exists_min_image
    (Finset.univ.filter fun B : Finset M => Submonoid.closure (B : Set M) = ⊤)
    Finset.card
    ⟨Finset.univ, Finset.mem_filter.mpr ⟨Finset.mem_univ _, by
      simp [Submonoid.closure_univ]⟩⟩
  have hAgen : Submonoid.closure (A : Set M) = ⊤ := (Finset.mem_filter.mp hA).2
  have hmin' : ∀ B : Finset M, Submonoid.closure (B : Set M) = ⊤ →
      A.card ≤ B.card := fun B hB =>
    hmin B (Finset.mem_filter.mpr ⟨Finset.mem_univ B, hB⟩)
  -- some generator is a non-unit
  have hex : ∃ c ∈ A, ¬ IsUnit c := by
    by_contra hall
    push Not at hall
    exact hM fun m => isUnit_of_generators_units (A : Set M) hAgen
      (fun a ha => hall a ha) m
  obtain ⟨c, hcA, hc⟩ := hex
  refine ⟨Submonoid.closure ((A.erase c : Finset M) : Set M), c, hc, ?_, ?_⟩
  · -- proper: c ∈ closure (A.erase c) would beat A's minimality
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
    have h2 : (A.erase c).card < A.card := Finset.card_erase_lt_of_mem hcA
    omega
  · -- ↑N ∪ {c} recovers A, which generates
    rw [eq_top_iff, ← hAgen]
    refine Submonoid.closure_le.mpr fun a ha => ?_
    by_cases hac : a = c
    · exact Submonoid.subset_closure (Or.inr (by simp [hac]))
    · exact Submonoid.subset_closure
        (Or.inl (Submonoid.subset_closure (Finset.mem_erase.mpr ⟨hac, ha⟩)))
```

(LATITUDE note for the implementer: in `hex`, the exact shape `hall` takes after `push Not` may need `Finset.mem_coe.mp` inserted in `fun a ha => hall a ha` — the probe accepted the coercion directly, but the binder form of `∃ c ∈ A, ¬ IsUnit c` under `push Not` can shift; adjust locally, do not restate.)

- [ ] **Step 2: `LocalDivisor.lean` — the nonempty lemma**

Insert directly after `localDivisor_faithful`:

```lean
/-- Nonempty local states [blueprint `lem:localdiv-nonempty`]: any
`x·c` witnesses. Milestone 8's induction needs this to recurse into
the local divisor. -/
theorem localDivisor_X_nonempty (T : TransMon) (c : T.M)
    (hX : Nonempty T.X) : Nonempty (localDivisor T c).X :=
  hX.elim fun x => ⟨⟨T.act x c, x, rfl⟩⟩
```

(If the surrounding section carries variables that make `T`/`c` implicit or clash, place the lemma in its own `section`; the SIGNATURE as written is what Task 6 calls: `localDivisor_X_nonempty T c hX`.)

- [ ] **Step 3: Verify, commit**

```bash
lake build 2>&1 | tail -3
```

Expected: green, zero warnings (if the `omit` placement or an unused section variable warns, fix per the file's existing convention). Then:

```bash
git add KRTheory
git commit -m "Add KR induction prelims: units generation, submonoid card, generator split"
git push
```

---

### Task 4: `KrohnRhodes.lean` — the `KRPrime` datatype

**Files:**
- Create: `KRTheory/KrohnRhodes.lean`
- Modify: `KRTheory.lean` (append `import KRTheory.KrohnRhodes`)

**Interfaces:**
- Consumes: `BundledFinGroup` (M6, fields `carrier`/`group`/`finite`, instances via `attribute [instance]`), `flipFlop` (M4), `regular` (M1).
- Produces (Tasks 5–6 consume exactly these):
  - `KRPrime : Type 1` with constructors `KRPrime.flipflop`, `KRPrime.grp (G : BundledFinGroup)`
  - `KRPrime.toTransMon : KRPrime → TransMon`
  - simp lemmas `KRPrime.toTransMon_flipflop : KRPrime.flipflop.toTransMon = flipFlop` and `KRPrime.toTransMon_grp (G) : (KRPrime.grp G).toTransMon = regular G.carrier`

- [ ] **Step 1: Write the file**

```lean
import KRTheory.FiniteMonoid
import KRTheory.GroupCase
import KRTheory.Decomposition

/-!
# The Krohn–Rhodes theorem

The main induction and the two v1 main theorems [DKS Thm 4.1; spec
§3.9; blueprint `ch:krohnrhodes`]: every faithful finite transformation
monoid with nonempty states divides an iterated wreath product of
flip-flops and regular representations of finite simple groups dividing
its monoid — and the abstract finite-monoid corollary.

Factors are carried as `KRPrime`: canonical objects (THE flip-flop, a
`regular G`), not isomorphism classes, so the statements need no
TransMon-isomorphism API (spec §3.9).
-/

namespace KRTheory
namespace TransMon

/-- A Krohn–Rhodes prime factor [blueprint `def:krprime`]: the
flip-flop, or a bundled finite (simple, in the theorems' conclusions)
group. -/
inductive KRPrime : Type 1 where
  /-- The flip-flop factor `U₂`. -/
  | flipflop : KRPrime
  /-- A group factor. -/
  | grp (G : BundledFinGroup) : KRPrime

/-- The transformation monoid a prime stands for [blueprint
`def:krprime`]: the canonical flip-flop, or the regular representation
of the group. -/
def KRPrime.toTransMon : KRPrime → TransMon
  | .flipflop => flipFlop
  | .grp G => regular G.carrier

/-- Equation lemma (the match-compiled `toTransMon` does not
`rfl`-reduce under `rw`'s closing check). -/
@[simp] theorem KRPrime.toTransMon_flipflop :
    KRPrime.flipflop.toTransMon = flipFlop := rfl

/-- Equation lemma, group case. -/
@[simp] theorem KRPrime.toTransMon_grp (G : BundledFinGroup) :
    (KRPrime.grp G).toTransMon = regular G.carrier := rfl

-- Sanity (spec §6): the flip-flop prime is THE flip-flop — 2 states,
-- 3 monoid elements; a group prime's monoid is the group itself.
example : Nat.card KRPrime.flipflop.toTransMon.M = 3 := by
  rw [KRPrime.toTransMon_flipflop]
  show Nat.card (Resets Bool) = 3
  rw [Resets.natCard, Nat.card_eq_fintype_card]
  decide
example : Nat.card KRPrime.flipflop.toTransMon.X = 2 := by
  rw [KRPrime.toTransMon_flipflop]
  show Nat.card Bool = 2
  rw [Nat.card_eq_fintype_card]
  decide
example (G : BundledFinGroup) : (KRPrime.grp G).toTransMon.M = G.carrier := rfl

end TransMon
end KRTheory
```

(The two `Nat.card` example scripts mirror `Reset.lean`'s existing flip-flop example verbatim; if `show` needs a different reduced spelling, adjust the `show` line only.)

- [ ] **Step 2: Wire the root import**

Append to `KRTheory.lean`:

```lean
import KRTheory.KrohnRhodes
```

- [ ] **Step 3: Verify, commit**

```bash
lake build 2>&1 | tail -3
git add KRTheory KRTheory.lean
git commit -m "Add KRPrime factor datatype with sanity checks"
git push
```

Expected: green, zero warnings.

---

### Task 5: The group branch

**Files:**
- Modify: `KRTheory/KrohnRhodes.lean` (one theorem, before `end TransMon`, after the examples)

**Interfaces:**
- Consumes: `group_bar_div (T) (hg : ∀ m : T.M, IsUnit m) : T.bar ≺ resetMonoid T.X ≀ regular T.M` (M6); `reset_div_flipFlops (X) [Finite X] [Nonempty X] : ∃ n, resetMonoid X ≺ wreathList (List.replicate n flipFlop)` (M4); `transfGroup_div_wreath_simples (G) [Group G] [Finite G] : ∃ L : List BundledFinGroup, regular G ≺ wreathList (L.map fun H => regular H.carrier) ∧ ∀ H ∈ L, IsSimpleGroup H.carrier ∧ H.carrier ≺ₘ G` (M6); `groupOfIsUnit` (Mathlib); `StrongDivides.wreath`, `wreathList_append`, `StrongDivides.trans` (M3); Task 4's `KRPrime` API.
- Produces (Task 6 consumes): `krohnRhodes_bar_of_units (T : TransMon) (hX : Nonempty T.X) (hg : ∀ m : T.M, IsUnit m) : ∃ L : List KRPrime, T.bar ≺ wreathList (L.map KRPrime.toTransMon) ∧ ∀ p ∈ L, ∀ G, p = KRPrime.grp G → IsSimpleGroup G.carrier ∧ G.carrier ≺ₘ T.M`

- [ ] **Step 1: Write the theorem**

```lean
/-- The group branch of the induction [blueprint `lem:kr-group-branch`]:
if every element of `T.M` is a unit and states are nonempty, Q(T) holds
outright. Faithfulness is NOT needed — `group_bar_div` (M6,
strengthened) does not use it. The group structure is Mathlib's
`groupOfIsUnit`, which extends the bundled monoid instance in place, so
`regular T.M` is the same transformation monoid on both sides of the
glue (spec §8 risk row, resolved). -/
theorem krohnRhodes_bar_of_units (T : TransMon) (hX : Nonempty T.X)
    (hg : ∀ m : T.M, IsUnit m) :
    ∃ L : List KRPrime,
      T.bar ≺ wreathList (L.map KRPrime.toTransMon) ∧
      ∀ p ∈ L, ∀ G, p = KRPrime.grp G →
        IsSimpleGroup G.carrier ∧ G.carrier ≺ₘ T.M := by
  have := hX
  let _ : Group T.M := groupOfIsUnit hg
  obtain ⟨n, hff⟩ := reset_div_flipFlops T.X
  obtain ⟨Gs, hGs, hfac⟩ := transfGroup_div_wreath_simples T.M
  refine ⟨List.replicate n .flipflop ++ Gs.map .grp, ?_, ?_⟩
  · calc T.bar
        ≺ resetMonoid T.X ≀ regular T.M := group_bar_div T hg
      _ ≺ wreathList (List.replicate n flipFlop) ≀
            wreathList (Gs.map fun H => regular H.carrier) :=
          StrongDivides.wreath hff hGs
      _ ≺ wreathList ((List.replicate n KRPrime.flipflop
            ++ Gs.map KRPrime.grp).map KRPrime.toTransMon) := by
          rw [List.map_append, List.map_replicate,
            KRPrime.toTransMon_flipflop, List.map_map]
          exact wreathList_append _ _
  · intro p hp G hpG
    rcases List.mem_append.mp hp with hp | hp
    · exact absurd ((List.eq_of_mem_replicate hp).symm.trans hpG) (by simp)
    · obtain ⟨H, hH, rfl⟩ := List.mem_map.mp hp
      obtain rfl : H = G := by injection hpG
      exact hfac H hH
```

Known wrinkles, in order of likelihood (GREEN latitude, statement fixed):
  1. The `List.map_map` step must reconcile `(Gs.map KRPrime.grp).map KRPrime.toTransMon` with `Gs.map fun H => regular H.carrier`: after `List.map_map` the function is `KRPrime.toTransMon ∘ KRPrime.grp`, which is pointwise-`rfl` equal to `fun H => regular H.carrier`. If the `calc` step's final `exact` does not unify them, insert `simp only [Function.comp_def, KRPrime.toTransMon_grp]` (or `List.map_congr_left` with a `rfl` argument) before the `exact`.
  2. `absurd … (by simp)`: the contradiction target is `KRPrime.flipflop = KRPrime.grp G → False`-shaped; if `simp` doesn't close constructor discrimination, use `nofun` or `fun h => KRPrime.noConfusion h`.
  3. If the style linter objects to `have := hX` (introducing the instance for `reset_div_flipFlops`), spell it `have _ : Nonempty T.X := hX`.

- [ ] **Step 2: Verify, commit**

```bash
lake build 2>&1 | tail -3
git add KRTheory/KrohnRhodes.lean
git commit -m "Prove the group branch of the KR induction"
git push
```

Expected: green, zero warnings.

---

### Task 6: The induction and the main theorems

**Files:**
- Modify: `KRTheory/KrohnRhodes.lean` (three theorems + one closing example, after `krohnRhodes_bar_of_units`)

**Interfaces:**
- Consumes: Task 3's four prelims; Task 5's `krohnRhodes_bar_of_units`; `decomposition (T) (hT) (N) (c) (hc) (hgen) : T.bar ≺ (localDivisor T c).bar ≀ (rightFactor T N).bar` (M7); `localDivisor_faithful (hT) (c)`, `localDivisor_card_lt (hc) : Nat.card (LocalDivisor c) < Nat.card M`, `localDivisor_divides (c) : LocalDivisor c ≺ₘ M` (M5); `rightFactor_faithful (T) (N)` (M7); `MonoidDivides.of_submonoid`, `MonoidDivides.trans`, `StrongDivides.monoidDivides`, `bar_divides`, `regular_faithful` (M1–M4).
- Produces: `krohnRhodes_bar`, `krohnRhodes`, `krohnRhodes_monoid` — the spec §3.9 signatures.

- [ ] **Step 1: The master induction `krohnRhodes_bar`**

```lean
/-- The main induction [blueprint `thm:kr-bar`] — predicate Q of spec
§3.9: the barred `T` divides a wreath of primes whose group factors are
simple and divide `T.M`. Plain strong induction on `Nat.card T.M`
(blueprint `rem:kr-measure`: both recursive calls strictly shrink the
monoid; the spec's lex second component is never exercised). -/
theorem krohnRhodes_bar (T : TransMon) (hT : T.Faithful)
    (hX : Nonempty T.X) :
    ∃ L : List KRPrime,
      T.bar ≺ wreathList (L.map KRPrime.toTransMon) ∧
      ∀ p ∈ L, ∀ G, p = KRPrime.grp G →
        IsSimpleGroup G.carrier ∧ G.carrier ≺ₘ T.M := by
  revert hT hX
  generalize hcard : Nat.card T.M = n
  induction n using Nat.strong_induction_on generalizing T with
  | _ n ih =>
    intro hT hX
    by_cases hg : ∀ m : T.M, IsUnit m
    · exact krohnRhodes_bar_of_units T hX hg
    · obtain ⟨N, c, hc, hNtop, hgen⟩ := exists_gen_nonunit hg
      obtain ⟨L₁, hdiv₁, hfac₁⟩ :=
        ih (Nat.card (localDivisor T c).M)
          (hcard ▸ localDivisor_card_lt hc) (localDivisor T c) rfl
          (localDivisor_faithful hT c) (localDivisor_X_nonempty T c hX)
      obtain ⟨L₂, hdiv₂, hfac₂⟩ :=
        ih (Nat.card (rightFactor T N).M)
          (hcard ▸ card_submonoid_lt_of_ne_top N hNtop) (rightFactor T N)
          rfl (rightFactor_faithful T N) ⟨Sum.inr 1⟩
      refine ⟨L₁ ++ L₂, ?_, ?_⟩
      · calc T.bar
            ≺ (localDivisor T c).bar ≀ (rightFactor T N).bar :=
              decomposition T hT N c hc hgen
          _ ≺ wreathList (L₁.map KRPrime.toTransMon) ≀
                wreathList (L₂.map KRPrime.toTransMon) :=
              StrongDivides.wreath hdiv₁ hdiv₂
          _ ≺ wreathList ((L₁ ++ L₂).map KRPrime.toTransMon) := by
              rw [List.map_append]
              exact wreathList_append _ _
      · intro p hp G hpG
        rcases List.mem_append.mp hp with hp | hp
        · obtain ⟨hsimple, hdivM⟩ := hfac₁ p hp G hpG
          exact ⟨hsimple, hdivM.trans (localDivisor_divides c)⟩
        · obtain ⟨hsimple, hdivM⟩ := hfac₂ p hp G hpG
          exact ⟨hsimple, hdivM.trans (MonoidDivides.of_submonoid N)⟩
```

Known wrinkles (GREEN latitude, statement fixed):
  1. Case-entry mechanics (probe-verified in full): `generalizing T` reverts `T`+`hcard` for the motive but RE-INTRODUCES both under their original names on case entry, so the case opens with exactly `intro hT hX` (two intros) and `T`, `hcard : Nat.card T.M = n` already in scope. `revert hT hX` before the `generalize` is what puts them in the goal. The sharpened probe also confirmed both IH calls verbatim — including `hcard ▸ localDivisor_card_lt hc` unifying at `Nat.card (localDivisor T c).M < n` across the projection defeq — and the `decomposition T hT N c hc hgen` application.
  2. The measure arguments: `localDivisor_card_lt hc : Nat.card (LocalDivisor c) < Nat.card T.M` must land where `Nat.card (localDivisor T c).M < n` is wanted — defeq through the semireducible projection; if `hcard ▸ …` does not elaborate, bridge: `have hlt : Nat.card (localDivisor T c).M < n := by rw [← hcard]; exact localDivisor_card_lt hc` (and analogously with `show Nat.card ↥N < Nat.card T.M` for the right factor).
  3. The trans steps in the factor condition cross the same defeqs (`(localDivisor T c).M ≡ LocalDivisor c`, `(rightFactor T N).M ≡ ↥N`); same bridge discipline if needed.
  4. `by_cases` on a `∀`-Prop is classical — fine (file-wide `Classical.choice` is already in the certificate's allowed set).

- [ ] **Step 2: The two main theorems**

**Carve-out candidate (user):** `krohnRhodes` is a 3-line assembly (`obtain` from `krohnRhodes_bar`, glue `bar_divides` by transitivity) — the line where the project's main theorem lands. If the user opted in, pause here and let them write it from the fixed statement.

```lean
/-- **The Krohn–Rhodes theorem**, transformation form, strong version
[DKS Thm 4.1; spec §3.9; blueprint `thm:krohnrhodes`]: a faithful
finite transformation monoid with nonempty states strongly divides an
iterated wreath product of flip-flops and simple-group regulars, every
group factor dividing `T.M`. `[Nonempty T.X]` is necessary: an
empty-state transformation monoid strongly divides no wreath of primes
(their state spaces are nonempty). -/
theorem krohnRhodes (T : TransMon) (hT : T.Faithful) [Nonempty T.X] :
    ∃ L : List KRPrime,
      T ≺ wreathList (L.map KRPrime.toTransMon) ∧
      ∀ p ∈ L, ∀ G, p = KRPrime.grp G →
        IsSimpleGroup G.carrier ∧ G.carrier ≺ₘ T.M := by
  obtain ⟨L, hdiv, hfac⟩ := krohnRhodes_bar T hT ‹Nonempty T.X›
  exact ⟨L, (bar_divides T).trans hdiv, hfac⟩

/-- **The Krohn–Rhodes theorem**, abstract finite-monoid form [spec
§3.9; blueprint `thm:krohnrhodes-monoid`]: via the regular
representation. -/
theorem krohnRhodes_monoid (M : Type) [Monoid M] [Finite M] :
    ∃ L : List KRPrime,
      M ≺ₘ (wreathList (L.map KRPrime.toTransMon)).M ∧
      ∀ p ∈ L, ∀ G, p = KRPrime.grp G →
        IsSimpleGroup G.carrier ∧ G.carrier ≺ₘ M := by
  have : Nonempty (regular M).X := ⟨(1 : M)⟩
  obtain ⟨L, hdiv, hfac⟩ := krohnRhodes (regular M) (regular_faithful M)
  exact ⟨L, hdiv.monoidDivides, hfac⟩
```

Notes pinned by probes: the `have : Nonempty (regular M).X := ⟨(1 : M)⟩` line is REQUIRED (instance search will not unfold the projection); `hdiv.monoidDivides : (regular M).M ≺ₘ …` is accepted at `M ≺ₘ …` (defeq, probe-verified); the factor condition transports for the same reason.

- [ ] **Step 3: Closing sanity example**

Append after `krohnRhodes_monoid`:

```lean
-- Sanity (spec §6): the main theorem instantiates on a concrete monoid
-- (instances resolve; the `Nonempty` bridge works as documented).
example : ∃ L : List KRPrime,
    regular (ZMod 2) ≺ wreathList (L.map KRPrime.toTransMon) ∧
    ∀ p ∈ L, ∀ G, p = KRPrime.grp G →
      IsSimpleGroup G.carrier ∧ G.carrier ≺ₘ (regular (ZMod 2)).M := by
  have : Nonempty (regular (ZMod 2)).X := ⟨(1 : ZMod 2)⟩
  exact krohnRhodes (regular (ZMod 2)) (regular_faithful _)
```

- [ ] **Step 4: Verify, commit**

```bash
lake build 2>&1 | tail -3
grep -rn "sorry" KRTheory/ KRTheory.lean
git add KRTheory/KrohnRhodes.lean
git commit -m "Prove the Krohn-Rhodes theorem"
git push
```

Expected: green, zero warnings, empty grep.

---

### Task 7: Milestone close

**Files:**
- Modify: `scripts/AxiomCertificate.lean`, `.github/workflows/ci.yml`, `blueprint/src/chapters/krohnrhodes.tex`, `blueprint/src/chapters/finitemonoid.tex`, `blueprint/src/chapters/localdivisor.tex`

**Interfaces:** consumes everything; produces the acceptance state (spec §7 row 8).

- [ ] **Step 1: Certificate + count**

Append to `scripts/AxiomCertificate.lean`:

```lean
#print axioms krohnRhodes
#print axioms krohnRhodes_monoid
```

Update ci.yml's count `-eq 16` → `-eq 18` (same comment convention: "18 = current certificate entries"). Run `lake env lean scripts/AxiomCertificate.lean` — 18 lines, all within `{propext, Classical.choice, Quot.sound}`.

- [ ] **Step 2: Blueprint stamps**

Add `\leanok` after every `\lean{...}` added in Task 2: `krohnrhodes.tex` (FIVE macros — `def:krprime`, `lem:kr-group-branch`, `thm:kr-bar`, `thm:krohnrhodes`, `thm:krohnrhodes-monoid`; `rem:kr-measure` has no `\lean{}` and gets nothing), `finitemonoid.tex` (THREE — `lem:units-generated`, `lem:submonoid-card`, `lem:gen-split`), `localdivisor.tex` (ONE — `lem:localdiv-nonempty`).

- [ ] **Step 3: Sweep, commit, CI**

```bash
lake build 2>&1 | tail -5
grep -rn "sorry" KRTheory/ KRTheory.lean
git add -A
git commit -m "Close milestone 8: extend axiom certificate, stamp blueprint leanok"
git push
gh pr checks 7 --watch
```

Expected: green, zero warnings, empty grep, all CI jobs green.

- [ ] **Step 4 (controller): final review, memory, handoff**

SDD final whole-branch review serves as the milestone review. After it: update `kr-theory-project.md` (M8 done — `krohnRhodes` + `krohnRhodes_monoid` proved; next M9 — `SemigroupVersion.lean`: `≺ₛ`, `WithOne` transfer, `krohnRhodes_semigroup`, plus the M9-parked items from M7 triage: blueprint `\uses` nits, Lemma 9.4 typography, `tag_mul` consolidation, stale plan-doc phrase — and blueprint completion/axiom certificate per spec §1). PR handling stays the user's.

---

## Self-review (performed at planning time)

- **Spec coverage:** §3.9 induction → Task 6 Step 1; `krohnRhodes`/`krohnRhodes_monoid` signatures → Task 6 Step 2 (verbatim, probe-elaborated); `KRPrime` → Task 4; group branch (§3.7 consumption) → Task 5; prelims carried from M7's ledger (§3.6/§4.3) → Task 3; §7 row 8 acceptance → Task 7. `krohnRhodes_semigroup` is M9 (spec §7 row 9) — out of scope here by design.
- **Placeholder scan:** every Lean step carries full code; the three LATITUDE notes are bounded alternatives (named tactics/lemmas), not deferrals.
- **Type consistency:** `krohnRhodes_bar_of_units T hX hg` (Task 5 signature = Task 6 call); `exists_gen_nonunit hg` returns `⟨N, c, hc, hNtop, hgen⟩` in the order Task 6 destructures; `localDivisor_X_nonempty T c hX` (Task 3 signature = Task 6 call); `card_submonoid_lt_of_ne_top N hNtop` (Task 3 = Task 6); simp-lemma names `toTransMon_flipflop`/`toTransMon_grp` (Task 4 = Task 5's `rw`).
