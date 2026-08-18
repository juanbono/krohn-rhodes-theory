# Krohn–Rhodes Milestone 6 (Group Case) Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Prove the group case of Krohn–Rhodes: every finite group's regular representation divides an iterated wreath of simple-group regulars (`transfGroup_div_wreath_simples`), and DKS 2.11 (`group_bar_div`) — via Kaloujnine–Krasner and a fused composition-series induction.

**Architecture:** One new file `KRTheory/GroupCase.lean` built in three slices on branch `milestone-6` (stacked on `milestone-5`): (1) `BundledFinGroup` + group-theory prelims (maximal normal subgroup, simple quotient, division feeders, card drop); (2) the Kaloujnine–Krasner covering `regular G ≺ regular ↥N ≀ regular (G ⧸ N)` via a cocycle embedding and an explicit retraction; (3) the fused strong induction (no composition-series artifact) and DKS 2.11 with the `∀ m, IsUnit m` group-encoding. Blueprint chapter first; housekeeping and spec refinements up front; close-out extends the CI certificate.

**Tech Stack:** Lean 4 (`v4.34.0-rc1`), Mathlib pinned at `ac4c4bff`, GitHub Actions (existing jobs), LaTeX blueprint. Base: branch `milestone-5` at `b6c1a7d` + this plan's commit; implementation on new `milestone-6`.

**Spec:** `docs/superpowers/specs/2026-08-17-krohn-rhodes-formalization-design.md` — §3.7 (group case), §4.3 `GroupCase.lean` row, §7 row 6 acceptance ("`group_bar_div` + `transfGroup_div_wreath_simples`"), as refined by this plan's Task 1 (see Decisions 2–5).

## Global Constraints

- All Lean inside `namespace KRTheory`/`TransMon`; notation scoped; carriers in `Type`; `Finite` (never `Fintype`) in bundled positions; cardinality is `Nat.card`.
- Docstrings on every public declaration including instances, citing blueprint labels and [DKS]/spec sections; module docstring cites [DKS §2.4–2.5, spec §3.7].
- Formalization-TDD: RED = statements + `sorry` stubs + examples elaborate; GREEN = proofs in, `grep -rn "sorry" KRTheory/ KRTheory.lean` empty. Zero-warning builds; plain commit messages, no trailers.
- Statements and signatures below are FIXED; proof scripts have tactic latitude (statement-weakening is never latitude). Established repairs: `show`-the-unfolded-goal for semireducible-projection stalls; explicit type ascriptions for numerals at projected types.
- New `Classical.choice`-bearing definitions: `Quotient.out` (the KK section) is the only new choice source; it stays quarantined inside `GroupCase.lean`'s private defs (`kkCocycle`, `kkRetract`) — public statements never mention it.
- The guard-example discipline (spec §6) is RELAXED for the KK section only (Decision 6): `Quotient.out` is noncomputable, so `decide`-guards cannot evaluate it; the twisted monoid laws themselves pin the chirality (kernel-checked), exactly as M3's `Covering.wreath` shipped. Non-`out` definitions (Task 6's `barMap`/conditions) keep normal guards.

## Decisions this plan records

1. **Probe-verified against the pinned Mathlib (planning session, by statement shape):** `Finite (Subgroup G)` instance exists; `QuotientGroup.nontrivial_iff : Nontrivial (G ⧸ N) ↔ N ≠ ⊤` exists; `Subgroup.Normal.comap`, `QuotientGroup.ker_mk'`, `Subgroup.ker_le_comap`, `Subgroup.map_comap_eq_self_of_surjective`, `MonoidHom.range_eq_map`, `MonoidHom.range_eq_top`, `IsSimpleGroup.mk` (takes `[Nontrivial]` + `∀ H, Normal → ⊥ ∨ ⊤`), `QuotientGroup.mk'`/`mk'_surjective`, `QuotientGroup.out_eq' : ↑q.out = q`, `Subgroup.card_eq_card_quotient_mul_card_subgroup`, `Subgroup.subtype`, `alternatingGroup` (+ `Normal` instance for `Fin 3`), `IsUnit.unit`/`val_inv_mul`/`mul_val_inv` all exist. NOT found as single lemmas: finite-poset maximal-element-in-set (Task 3 derives via `wellFounded_gt`+`WellFounded.has_min`, spelling latitude), `Subgroup.map (mk' N) ⊤ = ⊤` (derive via `range_eq_map` + `range_eq_top`), the card drops (derived), `JordanHolderLattice (Subgroup G)` (absent entirely — motivates Decision 2).
2. **Fused induction (spec refinement, Task 1 records in §3.7/§4.3):** `compositionSeries_exists` is dropped as a standalone artifact. Mathlib has no group instantiation of Jordan–Hölder, the framework covers uniqueness (a §2 non-goal) not existence, and the only consumer is `transfGroup_div_wreath_simples` — whose strong induction peels one maximal normal subgroup per step instead (spec §8's contingency, upgraded to the design).
3. **`BundledFinGroup` moves early (spec refinement):** introduced in `GroupCase.lean` (not `KrohnRhodes.lean` as §4.3 placed it); the series theorem's factor list is exactly `List BundledFinGroup`, and M8's `KRPrime.grp` consumes it unchanged.
4. **Group-encoding (spec refinement):** transformation-group-ness on a `TransMon` is the Prop `∀ m : T.M, IsUnit m` — a `[Group T.M]` instance would plant a second `Monoid T.M` beside the bundled `monoidM` (a diamond, and the action laws are stated against the bundled one). This Prop is also exactly M8's branch predicate (vs `¬IsUnit c` feeding `localDivisor_card_lt`). Abstract-group statements (`kaloujnine_krasner_div`, the series theorem) quantify `(G : Type) [Group G] [Finite G]` — single instance path, no diamond.
5. **DKS 2.11 without faithfulness (spec refinement):** the construction (Task 6) never uses `T.Faithful`; the statement is `group_bar_div (T : TransMon) (hg : ∀ m : T.M, IsUnit m) : T.bar ≺ resetMonoid T.X ≀ regular T.M` — strictly stronger than [DKS]'s (they carry a standing faithfulness assumption their proof doesn't need here). No `Nonempty T.X` either: with empty states both sides have empty state spaces and the empty covering works.
6. **KK monoid map via explicit retraction, not `MonoidHom.ofInjective`:** for `w` in the image of the KK embedding, `g` is recovered by the closed formula `s(1̄)⁻¹ · ↑(w.left 1̄) · s(w.right)` — so the covering's `monoidMap` is this retraction restricted to `mrange kkEmbed`, with the hom laws proved by `rintro ⟨g, rfl⟩` + the retraction identity. No injectivity lemma, no `MulEquiv`, simpler surjectivity.
7. Cardinality drops derived, not hunted: `Nat.card ↥N < Nat.card G` for `N ≠ ⊤` via the card product formula + `Finite.one_lt_card_iff_nontrivial` + `QuotientGroup.nontrivial_iff` (probe: no ready lemma).

---

### Task 1: Housekeeping (M5 parks) + spec refinements

**Files:**
- Modify: `docs/superpowers/specs/2026-08-17-krohn-rhodes-formalization-design.md` (§3.7, §4.3)
- Modify: `KRTheory/TransMon/LocalDivisor.lean` (import audit), `blueprint/src/chapters/finitemonoid.tex`, `KRTheory/TransMon/Reset.lean`

**Interfaces:** none produced; keep every edit byte-small.

- [ ] **Step 1: Spec §3.7 rewrite**

Replace §3.7's first bullet (`compositionSeries_exists`) with:

```markdown
- Composition-series existence is FUSED into the induction (amended 2026-08-18 during M6 planning): Mathlib has no `JordanHolderLattice (Subgroup G)` instantiation, its framework covers uniqueness (a §2 non-goal) rather than existence, and the only consumer is the induction below — which instead peels one maximal proper normal subgroup per step (prelims: `exists_maximal_normal_subgroup`, `isSimpleGroup_quotient`). No standalone series artifact.
```

Append to §3.7 (after the `group_bar_div` bullet):

```markdown
- **Encoding (amended 2026-08-18):** a "transformation group" is a `TransMon` `T` with the Prop `∀ m : T.M, IsUnit m` — a `[Group T.M]` instance would diamond with the bundled `monoidM`. This Prop is exactly the M8 branch predicate (group case vs `¬IsUnit c`). Abstract-group statements quantify `[Group G] [Finite G]` and use `regular G`.
- **`group_bar_div` needs neither faithfulness nor nonempty states** (amended 2026-08-18): the covering construction uses only `∀ m, IsUnit m`; statement `T.bar ≺ resetMonoid T.X ≀ regular T.M`.
- Factors are carried as `BundledFinGroup` (carrier + `[Group]` + `[Finite]`), introduced in `GroupCase.lean` (moved early from `KrohnRhodes.lean`; M8's `KRPrime.grp` reuses it).
```

- [ ] **Step 2: Spec §4.3 rows**

`GroupCase.lean` row becomes:

```markdown
| `GroupCase.lean` | `BundledFinGroup`, `exists_maximal_normal_subgroup`, `isSimpleGroup_quotient`, `subgroup_monoidDivides`, `quotient_monoidDivides`, `card_subgroup_lt_of_ne_top`, `regular_div_trivialTM_of_subsingleton`, `kaloujnine_krasner_div`, `transfGroup_div_wreath_simples`, `group_bar_div` (2.11) |
```

`KrohnRhodes.lean` row: change "`BundledFinGroup`, `KRPrime`, …" to "`KRPrime` (consuming `GroupCase.BundledFinGroup`), …".

- [ ] **Step 3: M5 parked cosmetics**

  1. `KRTheory/TransMon/LocalDivisor.lean:1` — audit `import KRTheory.FiniteMonoid`: run `grep -n "exists_pow_idempotent\|IsIdempotentElem" KRTheory/TransMon/LocalDivisor.lean`. If empty (expected), delete the import line, then verify with `lake build KRTheory.TransMon.LocalDivisor` (its other needs come through `Division.lean`). If the standalone build fails, restore the import and add a comment naming what needs it.
  2. `blueprint/src/chapters/finitemonoid.tex` — `lem:card-subtype-lt`'s proof block: replace the sentence `Transport of the corresponding \texttt{Fintype} fact along a classically chosen enumeration.` with `Supplied by Mathlib.`
  3. `KRTheory/TransMon/Reset.lean` (~line 245, the long `map_mul'` comment): rewrite the single ~190-char comment as (wrapped at ~78 cols, replacing the whole comment):

```lean
      -- The left factor's membership conditions are discarded: the
      -- product's value only reads `w.left true` and `w.right`, and it
      -- is the conditions of `w'` that decide which `splitMap` branch
      -- fires.
```

- [ ] **Step 0: Create the branch**

```bash
git checkout milestone-5
git checkout -b milestone-6
```

(All milestone-6 work lands here; the plan file itself was committed at the `milestone-5` tip per repo convention.)

- [ ] **Step 4: Build, commit, open the stacked draft PR**

```bash
lake build 2>&1 | tail -3
git add -A
git commit -m "Record M6 spec refinements; clear M5 parked cosmetics"
git push -u origin milestone-6
gh pr create --draft --base milestone-5 --title "Milestone 6: the group case" \
  --body "Tracking PR so CI runs per push. Merge policy stays manual."
```

Expected: green build, zero warnings; PR #5 open (base `milestone-5`) — Tasks 2–7 watch its checks.

---

### Task 2: Blueprint chapter `groupcase.tex`

**Files:**
- Create: `blueprint/src/chapters/groupcase.tex`
- Modify: `blueprint/src/content.tex` (add `\input{chapters/groupcase}` after `chapters/localdivisor`)

**Interfaces:**
- Produces labels Tasks 3–6 cite: `ch:groupcase`, `def:bundledfingroup`, `lem:max-normal`, `lem:simple-quotient`, `lem:subgroup-mdiv`, `lem:kaloujnine-krasner`, `lem:group-series`, `lem:group-bar`. Task 7 stamps `\leanok`.

- [ ] **Step 1: Write the chapter**

```latex
\chapter{The group case}\label{ch:groupcase}

\begin{definition}[Bundled finite group]\label{def:bundledfingroup}
  \lean{KRTheory.TransMon.BundledFinGroup}
  A carrier type together with group and finiteness structure --- the
  factor datatype for group decompositions.
\end{definition}

\begin{lemma}[Maximal normal subgroup]\label{lem:max-normal}
  \lean{KRTheory.TransMon.exists_maximal_normal_subgroup}
  Every nontrivial finite group has a proper normal subgroup maximal
  among proper normal subgroups.
\end{lemma}
\begin{proof}
  The set of proper normal subgroups contains $\bot$ and the subgroup
  lattice is finite; take a maximal element.
\end{proof}

\begin{lemma}[Simple quotient]\label{lem:simple-quotient}
  \lean{KRTheory.TransMon.isSimpleGroup_quotient}
  \uses{lem:max-normal}
  If $N \trianglelefteq G$ is maximal proper normal, $G/N$ is simple.
\end{lemma}
\begin{proof}
  A normal $\bar K \trianglelefteq G/N$ pulls back along the projection
  to a normal $K \supseteq N$; by maximality $K = N$ (so
  $\bar K = \bot$, since the projection kills $N$) or $K = \top$ (so
  $\bar K = \top$, the projection being onto). Nontriviality of $G/N$
  is $N \neq \top$.
\end{proof}

\begin{lemma}[Division feeders]\label{lem:subgroup-mdiv}
  \lean{KRTheory.TransMon.subgroup_monoidDivides,
        KRTheory.TransMon.quotient_monoidDivides}
  \uses{def:mdiv}
  $N \prec_m G$ for a subgroup, $G/N \prec_m G$ for a normal subgroup.
\end{lemma}
\begin{proof}
  The identity correspondence on the underlying submonoid; the
  canonical projection is a surjective homomorphism.
\end{proof}

\begin{lemma}[Kaloujnine--Krasner]\label{lem:kaloujnine-krasner}
  \lean{KRTheory.TransMon.kaloujnine_krasner_div}
  \uses{def:regular,def:wreath,def:sdiv,lem:subgroup-mdiv}
  For $N \trianglelefteq G$:
  $(G,G) \prec (N,N) \wr (G/N,\, G/N)$.
\end{lemma}
\begin{proof}
  Fix a set-section $s$ of $\pi : G \to G/N$ with $\pi(s(q)) = q$. The
  state map is $\varphi(n, q) := n\, s(q)$, surjective since
  $g = \big(g\, s(\pi g)^{-1}\big) s(\pi g)$ with the first factor in
  $N$. The monoid part embeds $G$ by
  $g \mapsto (f_g, \pi g)$, $f_g(q) := s(q)\, g\, s(q \cdot \pi g)^{-1}
  \in N$; the cocycle identity
  $f_{gh}(q) = f_g(q)\, f_h(q \cdot \pi g)$ makes this a homomorphism
  into the twisted product. The covering submonoid is its image, and
  the monoid map is the explicit retraction
  $w \mapsto s(\bar 1)^{-1}\, w_{\mathrm{left}}(\bar 1)\,
  s(w_{\mathrm{right}})$, which recovers $g$. Equivariance:
  $\varphi\big((n,q) \cdot (f_g, \pi g)\big)
  = n\, f_g(q)\, s(q \cdot \pi g)
  = n\, s(q)\, g = \varphi(n,q) \cdot g$.
\end{proof}

\begin{lemma}[Decomposition into simple factors]\label{lem:group-series}
  \lean{KRTheory.TransMon.transfGroup_div_wreath_simples}
  \uses{def:bundledfingroup,lem:max-normal,lem:simple-quotient,
        lem:subgroup-mdiv,lem:kaloujnine-krasner,lem:wreath-mono,
        lem:wreathList-append,def:wreathList}
  For every finite group $G$ there is a list $L$ of finite simple
  groups, each dividing $G$, with
  $(G,G) \prec \wr_{H \in L}\,(H,H)$.
\end{lemma}
\begin{proof}
  Strong induction on $|G|$. Trivial $G$: the empty list ($(G,G)$
  covers onto the trivial transformation monoid). Otherwise take a
  maximal proper normal $N$ (Lemma~\ref{lem:max-normal}); $G/N$ is
  simple (Lemma~\ref{lem:simple-quotient}) and divides $G$; the
  induction hypothesis decomposes $(N,N)$ (note $|N| < |G|$ since
  $G/N$ is nontrivial); Kaloujnine--Krasner, monotonicity, and the
  append lemma assemble $L := L_N \mathbin{+\!\!+} [G/N]$, and factors
  of $L_N$ divide $N \prec_m G$ by transitivity.
\end{proof}

\begin{lemma}[{[DKS] 2.11}]\label{lem:group-bar}
  \lean{KRTheory.TransMon.group_bar_div}
  \uses{def:bar,def:resets,def:regular,def:wreath,def:sdiv}
  If every element of $T$'s monoid is a unit, then
  $\bar T \prec (X, U(X)) \wr (M, M)$.
\end{lemma}
\begin{proof}
  States: $\varphi(x, g) := x \cdot g$; surjective via $g = 1$. The
  covering submonoid consists of the wreath elements whose front
  component is uniformly the identity (type A) or uniformly a reset
  (type B) with the invariant that $\sigma(g) \cdot (g\, r)$ is
  independent of $g$ (type-B condition). Type A covers $m$ (front
  $\equiv \mathrm{id}$, back $m$); type B covers the reset to $x_0$
  via $\sigma(g) := x_0 \cdot g^{-1}$, back $1$ --- this is where
  every element being a unit enters, along with the reindexings
  $g \mapsto g m$ in the closure proofs. The covering map reads the
  front at $g = 1$: type A $\mapsto m$, type B $\mapsto$ reset to
  $\sigma(1) \cdot r$. Faithfulness of $T$ is never used, and empty
  state sets degenerate consistently on both sides.
\end{proof}
```

- [ ] **Step 2: Wire, verify labels, commit, CI**

Append to `blueprint/src/content.tex` after `\input{chapters/localdivisor}`:

```latex
\input{chapters/groupcase}
```

Cross-check every `\uses` target resolves (house one-liner):

```bash
cd blueprint/src && grep -ho '\\label{[^}]*}' chapters/*.tex | sed 's/\\label{\(.*\)}/\1/' | sort > /tmp/labels.txt && grep -ho '\\uses{[^}]*}' chapters/groupcase.tex | sed 's/\\uses{//;s/}//' | tr ',' '\n' | sed 's/^[[:space:]]*//;s/[[:space:]]*$//' | sort -u | while read u; do grep -qx "$u" /tmp/labels.txt || echo "MISSING: $u"; done; cd ../..
```

Expected: no MISSING lines. Then:

```bash
git add blueprint/src
git commit -m "Add group-case blueprint chapter"
git push
gh pr checks 5 --watch
```

Expected: blueprint CI job green (the LaTeX test rig; no local TeX).

---

### Task 3: `GroupCase.lean` — `BundledFinGroup` + prelims

**Files:**
- Create: `KRTheory/GroupCase.lean`
- Modify: `KRTheory.lean` (append `import KRTheory.GroupCase` last)

**Interfaces:**
- Consumes: `MonoidDivides` (`≺ₘ`) and feeders (Division.lean); Mathlib names from Decision 1.
- Produces (Tasks 4–6 and M8 consume exactly these):
  - `structure BundledFinGroup : Type 1` — field `carrier : Type`, instance fields `[group : Group carrier]`, `[finite : Finite carrier]`, both `attribute [instance]`.
  - `exists_maximal_normal_subgroup (G) [Group G] [Finite G] [Nontrivial G] : ∃ N : Subgroup G, N.Normal ∧ N ≠ ⊤ ∧ ∀ K : Subgroup G, K.Normal → N < K → K = ⊤`
  - `isSimpleGroup_quotient (N : Subgroup G) [N.Normal] (hNtop : N ≠ ⊤) (hmax : ∀ K : Subgroup G, K.Normal → N < K → K = ⊤) : IsSimpleGroup (G ⧸ N)`
  - `subgroup_monoidDivides (N : Subgroup G) : ↥N ≺ₘ G`
  - `quotient_monoidDivides (N : Subgroup G) [N.Normal] : (G ⧸ N) ≺ₘ G`
  - `card_subgroup_lt_of_ne_top (N : Subgroup G) [N.Normal] (h : N ≠ ⊤) : Nat.card ↥N < Nat.card G`
  - `regular_div_trivialTM_of_subsingleton (G) [Group G] [Finite G] [Subsingleton G] : regular G ≺ trivialTM`

- [ ] **Step 1 (RED): file skeleton, statements + stubs, examples elaborate**

```lean
import KRTheory.TransMon.WreathDivision
import KRTheory.TransMon.Bar
import KRTheory.TransMon.Reset

/-!
# The group case

The base case of the Krohn–Rhodes induction [spec §3.7, blueprint
`ch:groupcase`]: every finite group's regular representation divides an
iterated wreath product of simple-group regulars
(`transfGroup_div_wreath_simples`, via Kaloujnine–Krasner and a fused
composition-series induction), and [DKS] 2.11 (`group_bar_div`): barred
transformation groups divide a reset-monoid/regular wreath.

Group-ness of a `TransMon` is the Prop `∀ m : T.M, IsUnit m` — a
`[Group T.M]` instance would diamond with the bundled `monoidM`
(spec §3.7 as amended 2026-08-18). The Kaloujnine–Krasner section uses
`Quotient.out` (classical choice) quarantined inside private defs.
-/

namespace KRTheory
namespace TransMon

/-- A bundled finite group [blueprint `def:bundledfingroup`]: the factor
datatype for group decompositions. Lives here rather than in
`KrohnRhodes.lean` (spec §4.3 as amended): the factor list of
`transfGroup_div_wreath_simples` is exactly a `List BundledFinGroup`,
and M8's `KRPrime.grp` consumes it unchanged. -/
structure BundledFinGroup : Type 1 where
  /-- The underlying type. -/
  carrier : Type
  /-- The group structure. -/
  [group : Group carrier]
  /-- Finiteness. -/
  [finite : Finite carrier]

attribute [instance] BundledFinGroup.group BundledFinGroup.finite

variable {G : Type} [Group G] [Finite G]

/-- Every nontrivial finite group has a maximal proper normal subgroup
[blueprint `lem:max-normal`]: the proper normal subgroups form a
nonempty (`⊥`) subset of the finite subgroup lattice. -/
theorem exists_maximal_normal_subgroup [Nontrivial G] :
    ∃ N : Subgroup G, N.Normal ∧ N ≠ ⊤ ∧
      ∀ K : Subgroup G, K.Normal → N < K → K = ⊤ := by
  sorry

/-- The quotient by a maximal proper normal subgroup is simple
[blueprint `lem:simple-quotient`]: normal subgroups of `G ⧸ N` pull
back along the projection to normal subgroups of `G` containing `N`. -/
theorem isSimpleGroup_quotient (N : Subgroup G) [N.Normal]
    (hNtop : N ≠ ⊤)
    (hmax : ∀ K : Subgroup G, K.Normal → N < K → K = ⊤) :
    IsSimpleGroup (G ⧸ N) := by
  sorry

/-- A subgroup's carrier divides the mother group as a monoid
[blueprint `lem:subgroup-mdiv`]: the identity correspondence on
`N.toSubmonoid`. -/
theorem subgroup_monoidDivides (N : Subgroup G) : ↥N ≺ₘ G := by
  sorry

/-- The quotient by a normal subgroup divides the mother group
[blueprint `lem:subgroup-mdiv`]: the projection is a surjective
homomorphism. -/
theorem quotient_monoidDivides (N : Subgroup G) [N.Normal] :
    (G ⧸ N) ≺ₘ G := by
  sorry

/-- Proper subgroups are strictly smaller — the measure of the fused
induction. Derived from the card product formula: the quotient is
nontrivial, so it contributes a factor `≥ 2`. -/
theorem card_subgroup_lt_of_ne_top (N : Subgroup G) [N.Normal]
    (h : N ≠ ⊤) : Nat.card ↥N < Nat.card G := by
  sorry

/-- A subsingleton group's regular representation divides the trivial
transformation monoid — the base of the fused induction. -/
theorem regular_div_trivialTM_of_subsingleton (G : Type) [Group G]
    [Finite G] [Subsingleton G] : regular G ≺ trivialTM := by
  sorry
```

Examples (end of what this task adds; elaborate at RED, pass at GREEN):

```lean
-- Sanity (spec §6): the smallest bundled groups; a concrete maximal
-- normal witness call; the division feeders on `Perm (Fin 3)` and its
-- alternating subgroup.
-- (`Multiplicative` because `ZMod 2`'s raw monoid is multiplicative and
-- not a group; the additive group made multiplicative is.)
example : (⟨Multiplicative (ZMod 2)⟩ : BundledFinGroup).carrier =
    Multiplicative (ZMod 2) := rfl
example : ∃ N : Subgroup (Equiv.Perm (Fin 3)), N.Normal ∧ N ≠ ⊤ ∧
    ∀ K : Subgroup (Equiv.Perm (Fin 3)), K.Normal → N < K → K = ⊤ :=
  exists_maximal_normal_subgroup
example : ↥(alternatingGroup (Fin 3)) ≺ₘ Equiv.Perm (Fin 3) :=
  subgroup_monoidDivides _
example : (Equiv.Perm (Fin 3) ⧸ alternatingGroup (Fin 3)) ≺ₘ
    Equiv.Perm (Fin 3) := quotient_monoidDivides _
```

Append `import KRTheory.GroupCase` as the last line of `KRTheory.lean`. Run `lake build` — elaborates with exactly the six `sorry` warnings.

- [ ] **Step 2 (GREEN): proofs**

`exists_maximal_normal_subgroup` (wf-recursion route; if `wellFounded_gt`/`WellFounded.has_min` spellings differ at this pin, find the exact ones with `exact?`/`#check` at the application point — the argument is fixed, the names have latitude):

```lean
  obtain ⟨N, ⟨hN, hNtop⟩, hmax⟩ :=
    (wellFounded_gt (α := Subgroup G)).has_min
      {K : Subgroup G | K.Normal ∧ K ≠ ⊤} ⟨⊥, inferInstance, bot_ne_top⟩
  refine ⟨N, hN, hNtop, fun K hK hNK => ?_⟩
  by_contra hKtop
  exact hmax K ⟨hK, hKtop⟩ hNK
```

(`Finite (Subgroup G)` powers the `WellFoundedGT` instance; `hmax K hKmem : ¬ K > N` contradicts `hNK : N < K`.)

`isSimpleGroup_quotient`:

```lean
  have : Nontrivial (G ⧸ N) := QuotientGroup.nontrivial_iff.mpr hNtop
  refine ⟨fun H hH => ?_⟩
  set K := Subgroup.comap (QuotientGroup.mk' N) H with hKdef
  have hKnormal : K.Normal := hH.comap _
  have hNK : N ≤ K := by
    simpa [← QuotientGroup.ker_mk' N] using
      Subgroup.ker_le_comap (QuotientGroup.mk' N) H
  have hHmap : H = Subgroup.map (QuotientGroup.mk' N) K :=
    (Subgroup.map_comap_eq_self_of_surjective
      (QuotientGroup.mk'_surjective N) H).symm
  rcases eq_or_lt_of_le hNK with heq | hlt
  · left
    have hmapN : Subgroup.map (QuotientGroup.mk' N) N = ⊥ := by
      rw [eq_bot_iff]
      rintro x ⟨g, hg, rfl⟩
      simpa using (QuotientGroup.eq_one_iff g).mpr hg
    rw [hHmap, ← heq, hmapN]
  · right
    rw [hHmap, hmax K hKnormal hlt, ← MonoidHom.range_eq_map]
    exact MonoidHom.range_eq_top.mpr (QuotientGroup.mk'_surjective N)
```

(`IsSimpleGroup.mk` wants the `Nontrivial` instance in scope — the opening `have`/`haveI` supplies it. `QuotientGroup.eq_one_iff g : QuotientGroup.mk g = 1 ↔ g ∈ N`; if the coercion between `mk` and `mk'` stalls a rewrite, `show` the `mk`-form first.)

`subgroup_monoidDivides`:

```lean
  exact ⟨N.toSubmonoid,
    { toFun := fun x => ⟨x.1, x.2⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl },
    fun x => ⟨⟨x.1, x.2⟩, rfl⟩⟩
```

(Membership in `N.toSubmonoid` is defeq to membership in `N`; if the anonymous-constructor forms stall, name the map first with an explicit `MonoidHom`.)

`quotient_monoidDivides`:

```lean
  exact .of_surjective (QuotientGroup.mk' N) (QuotientGroup.mk'_surjective N)
```

`card_subgroup_lt_of_ne_top`:

```lean
  have h2 : 1 < Nat.card (G ⧸ N) :=
    Finite.one_lt_card_iff_nontrivial.mpr
      (QuotientGroup.nontrivial_iff.mpr h)
  have hpos : 0 < Nat.card ↥N := Nat.card_pos
  calc Nat.card ↥N = 1 * Nat.card ↥N := (one_mul _).symm
    _ < Nat.card (G ⧸ N) * Nat.card ↥N := by
        exact Nat.mul_lt_mul_of_lt_of_le h2 le_rfl hpos
    _ = Nat.card G :=
        (Subgroup.card_eq_card_quotient_mul_card_subgroup N).symm
```

(The middle step's exact lemma name has latitude — any `Nat` strict-mono-mul spelling that closes `1 * a < b * a` from `1 < b`, `0 < a`.)

`regular_div_trivialTM_of_subsingleton`:

```lean
  exact ⟨{ toSubmonoid := ⊤
           stateMap := fun _ => 1
           monoidMap :=
             { toFun := fun _ => (1 : G)
               map_one' := rfl
               map_mul' := fun _ _ => (one_mul 1).symm }
           stateMap_surj := fun x => ⟨PUnit.unit, Subsingleton.elim _ _⟩
           monoidMap_surj := fun m => ⟨⟨PUnit.unit, trivial⟩,
             Subsingleton.elim _ _⟩
           equivariant := fun _ _ => Subsingleton.elim _ _ }⟩
```

- [ ] **Step 3: Verify, commit**

```bash
lake build 2>&1 | tail -3
grep -rn "sorry" KRTheory/ KRTheory.lean
git add KRTheory
git commit -m "Add bundled finite groups and group-case prelims"
git push
```

Expected: green, zero warnings, empty grep.

---

### Task 4: Kaloujnine–Krasner

**Files:**
- Modify: `KRTheory/GroupCase.lean` (append a `section KaloujnineKrasner`)

**Interfaces:**
- Consumes: `WreathMonoid`, `regular`, `≀`, `Covering`, `≺` (M0–3); `QuotientGroup.mk'`/`out_eq'`/`eq_one_iff`; Task 3's nothing (independent of prelims).
- Produces: `kaloujnine_krasner_div (G : Type) [Group G] [Finite G] (N : Subgroup G) [N.Normal] : regular G ≺ regular ↥N ≀ regular (G ⧸ N)` (Task 5 consumes).

- [ ] **Step 1 (RED): private defs + stubs + acceptance example**

```lean
section KaloujnineKrasner

variable (G : Type) [Group G] [Finite G] (N : Subgroup G) [N.Normal]

/-- The KK cocycle: front coordinate of the classical embedding at
section point `q`: `s(q) · g · s(q·ḡ)⁻¹ ∈ N`, with `s := Quotient.out`.
`Classical.choice` enters through `out` and stays inside this section's
private defs. -/
private def kkCocycle (g : G) (q : G ⧸ N) : ↥N :=
  ⟨q.out * g * ((q * QuotientGroup.mk g).out)⁻¹, by sorry⟩

/-- The KK embedding `G → ↥N ≀ (G ⧸ N)` (monoid part): cocycle front,
projection back. A `MonoidHom` via the cocycle identity. -/
private def kkEmbed : G →* WreathMonoid (regular ↥N) (regular (G ⧸ N)) where
  toFun g := ⟨fun q => kkCocycle G N g q, QuotientGroup.mk g⟩
  map_one' := by sorry
  map_mul' := by sorry

/-- The explicit retraction recovering `g` from `kkEmbed g`:
`s(1̄)⁻¹ · (front at 1̄) · s(back)`. -/
private def kkRetract
    (w : WreathMonoid (regular ↥N) (regular (G ⧸ N))) : G :=
  ((1 : G ⧸ N).out)⁻¹ * ↑(w.left 1) * (w.right).out

private theorem kkRetract_kkEmbed (g : G) :
    kkRetract G N (kkEmbed G N g) = g := by sorry

/-- Kaloujnine–Krasner as a strong division [spec §3.7, blueprint
`lem:kaloujnine-krasner`]: `(G,G) ≺ (N,N) ≀ (G⧸N, G⧸N)`. States map by
`(n, q) ↦ n · s(q)`; the covering submonoid is the embedding's range,
inverted by the explicit retraction. -/
theorem kaloujnine_krasner_div :
    regular G ≺ regular ↥N ≀ regular (G ⧸ N) := by sorry

end KaloujnineKrasner

-- Acceptance (spec §7 row 6 shape): the classic concrete instance.
-- `decide`-guards are not possible in this section (`Quotient.out` is
-- noncomputable); the twisted monoid laws pin the chirality instead
-- (Covering.wreath precedent, plan Decision 6).
example : regular (Equiv.Perm (Fin 3)) ≺
    regular ↥(alternatingGroup (Fin 3)) ≀
      regular (Equiv.Perm (Fin 3) ⧸ alternatingGroup (Fin 3)) :=
  kaloujnine_krasner_div _ _
```

Run `lake build KRTheory.GroupCase` — elaborates, sorries at the five stub sites.

- [ ] **Step 2 (GREEN): the five proofs**

Cocycle membership (`kkCocycle`'s field): show the projection kills it —

```lean
    have : QuotientGroup.mk
        (q.out * g * ((q * QuotientGroup.mk g).out)⁻¹) = (1 : G ⧸ N) := by
      rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv,
        QuotientGroup.out_eq', QuotientGroup.out_eq']
      group
    exact (QuotientGroup.eq_one_iff _).mp this
```

(`group` closes `q * mk g * (q * mk g)⁻¹ = 1`. Latitude on the exact `mk_mul`/`mk_inv` spellings — `map_mul (QuotientGroup.mk' N)` forms work too.)

`map_one'`: `WreathMonoid.ext` + `funext`; front: `kkCocycle G N 1 q = 1` by `Subtype.ext`; value `q.out * 1 * ((q * mk 1).out)⁻¹` — rewrite `mk_one`, `mul_one` (of the quotient), then `mul_inv_cancel`-shape via `group`. Back: `mk 1 = 1` is `map_one`.

`map_mul'` (the cocycle identity — the heart): after `WreathMonoid.ext`/`funext q`/`Subtype.ext`, the goal is

```
q.out * (g*h) * ((q * mk (g*h)).out)⁻¹
  = (q.out * g * ((q * mk g).out)⁻¹) * ((q * mk g).out * h * ((q * mk g * mk h).out)⁻¹)
```

— rewrite `mk_mul` so both sides mention the same `out`-atoms, then `group` (it cancels the adjacent `((q*mk g).out)⁻¹ * (q*mk g).out`). Note the wreath twist evaluates the second cocycle at `q ⊳ (mk g)` and the `regular (G ⧸ N)` action is right multiplication, so the point is literally `q * mk g` — if the goal displays the action form, `show` the multiplication form first (defeq).

`kkRetract_kkEmbed`:

```lean
  show ((1 : G ⧸ N).out)⁻¹ *
      ((1 : G ⧸ N).out * g * ((1 * QuotientGroup.mk g).out)⁻¹) *
      ((QuotientGroup.mk g : G ⧸ N)).out = g
  rw [one_mul]
  group
```

(after `one_mul` normalizes `1 * mk g`, everything cancels; latitude if `group` wants the atoms pre-aligned.)

`kaloujnine_krasner_div` — the covering:

```lean
  refine ⟨{ toSubmonoid := MonoidHom.mrange (kkEmbed G N)
            stateMap := fun p => (p.1 : G) * (p.2).out
            monoidMap :=
              { toFun := fun w => kkRetract G N w.1
                map_one' := by
                  simpa using kkRetract_kkEmbed G N 1
                map_mul' := by
                  rintro ⟨_, g, rfl⟩ ⟨_, h, rfl⟩
                  simp only [Submonoid.mk_mul_mk, ← map_mul,
                    kkRetract_kkEmbed] }
            stateMap_surj := ?_
            monoidMap_surj := fun g =>
              ⟨⟨kkEmbed G N g, g, rfl⟩, kkRetract_kkEmbed G N g⟩
            equivariant := ?_ }⟩
  · -- surjectivity of φ: g = (g * s(π g)⁻¹) * s(π g), first factor ∈ N
    intro g
    refine ⟨⟨⟨g * (((QuotientGroup.mk g : G ⧸ N)).out)⁻¹, ?_⟩,
      QuotientGroup.mk g⟩, ?_⟩
    · exact (QuotientGroup.eq_one_iff _).mp (by
        rw [QuotientGroup.mk_mul, QuotientGroup.mk_inv,
          QuotientGroup.out_eq']
        group)
    · show g * ((QuotientGroup.mk g : G ⧸ N).out)⁻¹ *
        ((QuotientGroup.mk g : G ⧸ N)).out = g
      group
  · -- equivariance: φ((n,q) ⊳ kkEmbed g) = φ(n,q) * g
    rintro ⟨n, q⟩ ⟨_, g, rfl⟩
    show (n : G) * (kkCocycle G N g q : G) * ((q * QuotientGroup.mk g).out)
        = ((n : G) * q.out) * kkRetract G N (kkEmbed G N g)
    rw [kkRetract_kkEmbed]
    show (n : G) * (q.out * g * ((q * QuotientGroup.mk g).out)⁻¹) *
        (q * QuotientGroup.mk g).out = (n : G) * q.out * g
    group
```

Latitude notes: the two `show` lines in equivariance unfold the wreath action / `regular` multiplication / `kkCocycle` value — the exact defeq forms may need adjustment (`Subtype` coercions especially: the front action multiplies in `↥N`, and the state's first coordinate is `↥N`-valued; the coercion to `G` is a monoid hom so `Subgroup.coe_mul` mediates). The structure — reindex, cancel `(…)⁻¹ * (…)`, `group` — is fixed.

- [ ] **Step 3: Verify, commit**

```bash
lake build 2>&1 | tail -3
grep -rn "sorry" KRTheory/ KRTheory.lean
git add KRTheory/GroupCase.lean
git commit -m "Prove Kaloujnine-Krasner division"
git push
```

---

### Task 5: The fused induction

**Files:**
- Modify: `KRTheory/GroupCase.lean` (append after the KK section)

**Interfaces:**
- Consumes: everything Task 3 produces; `kaloujnine_krasner_div` (Task 4); `StrongDivides.wreath`, `div_wreathList_singleton`, `wreathList_append`, `wreathList` (M3); `MonoidDivides.trans`.
- Produces: `transfGroup_div_wreath_simples (G : Type) [Group G] [Finite G] : ∃ L : List BundledFinGroup, regular G ≺ wreathList (L.map fun H => regular H.carrier) ∧ ∀ H ∈ L, IsSimpleGroup H.carrier ∧ H.carrier ≺ₘ G` (M8 consumes).

- [ ] **Step 1 (RED): statement + stub + examples**

```lean
/-- The group half of Krohn–Rhodes [spec §3.7, blueprint
`lem:group-series`]: every finite group's regular representation
strongly divides an iterated wreath of simple-group regulars, each
factor dividing `G`. Fused strong induction on `Nat.card G` — one
maximal proper normal subgroup is peeled per step (no composition-series
artifact; spec §3.7 as amended 2026-08-18). -/
theorem transfGroup_div_wreath_simples (G : Type) [Group G] [Finite G] :
    ∃ L : List BundledFinGroup,
      regular G ≺ wreathList (L.map fun H => regular H.carrier) ∧
      ∀ H ∈ L, IsSimpleGroup H.carrier ∧ H.carrier ≺ₘ G := by
  sorry

-- Acceptance sweep (spec §7 row 6): the theorem instantiates at the
-- smallest interesting groups; the factor conditions destructure.
example : ∃ L : List BundledFinGroup,
    regular (Equiv.Perm (Fin 3)) ≺
      wreathList (L.map fun H => regular H.carrier) ∧
    ∀ H ∈ L, IsSimpleGroup H.carrier ∧
      H.carrier ≺ₘ Equiv.Perm (Fin 3) :=
  transfGroup_div_wreath_simples _
-- `Multiplicative (ZMod 5)`: the cyclic group of order 5 (`ZMod 5`'s
-- raw monoid is multiplicative and not a group).
example : ∃ L : List BundledFinGroup,
    regular (Multiplicative (ZMod 5)) ≺
      wreathList (L.map fun H => regular H.carrier) ∧
    ∀ H ∈ L, IsSimpleGroup H.carrier ∧
      H.carrier ≺ₘ Multiplicative (ZMod 5) :=
  transfGroup_div_wreath_simples _
```

- [ ] **Step 2 (GREEN): the induction**

```lean
  generalize hcard : Nat.card G = n
  induction n using Nat.strong_induction_on generalizing G with
  | _ n ih =>
    rcases subsingleton_or_nontrivial G with hG | hG
    · -- trivial group: the empty decomposition
      exact ⟨[], by simpa using regular_div_trivialTM_of_subsingleton G,
        by simp⟩
    · obtain ⟨N, hNnorm, hNtop, hmax⟩ :=
        exists_maximal_normal_subgroup (G := G)
      haveI := hNnorm
      have hsimple := isSimpleGroup_quotient N hNtop hmax
      obtain ⟨L, hLdiv, hLcond⟩ := ih (Nat.card ↥N)
        (by have := card_subgroup_lt_of_ne_top N hNtop; omega)
        ↥N rfl
      refine ⟨L ++ [⟨G ⧸ N⟩], ?_, ?_⟩
      · calc regular G
            ≺ regular ↥N ≀ regular (G ⧸ N) :=
              kaloujnine_krasner_div G N
          _ ≺ wreathList (L.map fun H => regular H.carrier) ≀
                wreathList [regular (G ⧸ N)] :=
              hLdiv.wreath (div_wreathList_singleton _)
          _ ≺ wreathList ((L.map fun H => regular H.carrier) ++
                [regular (G ⧸ N)]) := wreathList_append _ _
          _ = wreathList ((L ++ [⟨G ⧸ N⟩]).map fun H =>
                regular H.carrier) := by simp
      · intro H hH
        rcases List.mem_append.mp hH with h | h
        · obtain ⟨hs, hd⟩ := hLcond H h
          exact ⟨hs, hd.trans (subgroup_monoidDivides N)⟩
        · simp only [List.mem_singleton] at h
          subst h
          exact ⟨hsimple, quotient_monoidDivides N⟩
```

Latitude notes: the base case's `simpa` bridges `wreathList ([].map _) = trivialTM` (`List.map_nil` + `wreathList_nil`, both defeq/simp); the final `=`-calc step is `List.map_append` (core `Trans r Eq r` handles `=` in a `≺` calc — M5-verified). The `ih` application instantiates at the type `↥N` with its instances found by search (`Subgroup.toGroup`, `Subtype.finite` route) — if instance search stalls at the projected instantiation, `haveI : Finite ↥N := inferInstance` before the `obtain`.

- [ ] **Step 3: Verify, commit**

```bash
lake build 2>&1 | tail -3
grep -rn "sorry" KRTheory/ KRTheory.lean
git add KRTheory/GroupCase.lean
git commit -m "Prove group decomposition into simple wreath factors"
git push
```

---

### Task 6: DKS 2.11 (`group_bar_div`)

**Files:**
- Modify: `KRTheory/GroupCase.lean` (append)

**Interfaces:**
- Consumes: `BarMonoid`/`bar` (M4), `Resets`/`resetMonoid` (M4), `WreathMonoid`, `regular`, `Covering`; `IsUnit.unit`/`val_inv_mul`/`mul_val_inv` (Mathlib).
- Produces: `group_bar_div (T : TransMon) (hg : ∀ m : T.M, IsUnit m) : T.bar ≺ resetMonoid T.X ≀ regular T.M` (M8 consumes for the group branch).

The construction (blueprint `lem:group-bar`): states map `φ(x, g) := T.act x g`. The covering submonoid holds wreath elements of two shapes — type A (front uniformly `Resets.id`, covering `of m` via back `m`) and type B (front uniformly a reset, with the invariant that the landing state `target(g) ⊳ (g * r)` is independent of `g`, covering `reset x₀` via `σ(g) := x₀ ⊳ g⁻¹`, back `1`). The unit hypothesis powers the reindexings `g ↦ g * m` in the closure proofs and the `g⁻¹` in the surjectivity witness. The covering map reads the front at `g = 1`.

- [ ] **Step 1 (RED): conditions, map, statement, guards**

```lean
section GroupBar

variable (T : TransMon)

/-- The type-A/type-B classification conditions for the 2.11 covering
(mirror of `splitSub`'s style in `Reset.lean`):
C1 — the front component has uniform shape;
C2 — for reset fronts, the landing state `x ⊳ (g * r)` is independent
of the sample point `g`. -/
private def groupBarSub : Submonoid (resetMonoid T.X ≀ regular T.M).M where
  carrier := {w | (∀ g g', (w.left g = Resets.id ↔ w.left g' = Resets.id)) ∧
    ∀ g g' x x', w.left g = Resets.to x → w.left g' = Resets.to x' →
      T.act x (g * w.right) = T.act x' (g' * w.right)}
  one_mem' := by sorry
  mul_mem' := by sorry

/-- The covering's value map: read the front at `1`. Type A (`id`)
covers the original element `w.right`; type B (`to x`) covers the reset
onto the landing state `x ⊳ w.right`. -/
private def groupBarMap (w : (resetMonoid T.X ≀ regular T.M).M) :
    BarMonoid T :=
  match w.left 1 with
  | Resets.id => .of w.right
  | Resets.to x => .reset (T.act x w.right)

/-- [DKS] 2.11 [blueprint `lem:group-bar`], strengthened: neither
faithfulness nor nonempty states are needed (spec §3.7 as amended
2026-08-18). If every element of `T.M` is a unit, the barred `T`
strongly divides `U(T.X) ≀ (T.M, T.M)`. The right factor is the
REGULAR representation of `T.M` even when `T.X ≠ T.M` [DKS §2.4]. -/
theorem group_bar_div (hg : ∀ m : T.M, IsUnit m) :
    T.bar ≺ resetMonoid T.X ≀ regular T.M := by
  sorry

end GroupBar
```

Examples/guards (computable section — normal §6 discipline applies):

```lean
-- Sanity (spec §6): 2.11 at the regular representation of `Perm (Fin 3)`
-- (every element a unit via `Group.isUnit`).
example : (regular (Equiv.Perm (Fin 3))).bar ≺
    resetMonoid (Equiv.Perm (Fin 3)) ≀ regular (Equiv.Perm (Fin 3)) :=
  group_bar_div _ fun g => Group.isUnit g
-- Guard: `groupBarMap` reads the front AT 1 and moves the target BY
-- `w.right` ON THE RIGHT: for `w = ⟨const (to x₀), m⟩` the value must
-- be `reset (x₀ ⊳ m)`; a transposed definition reading `x₀` alone (or
-- acting on the left) gives `reset x₀ ≠`. Over the noncommutative
-- `regular (Equiv.Perm (Fin 3))` with `x₀ := swap 0 1`, `m := swap 1 2`:
example : groupBarMap (regular (Equiv.Perm (Fin 3)))
    ⟨fun _ => Resets.to (Equiv.swap 0 1), Equiv.swap 1 2⟩ =
    BarMonoid.reset (Equiv.swap 0 1 * Equiv.swap 1 2) := rfl
example : (Equiv.swap 0 1 * Equiv.swap 1 2 : Equiv.Perm (Fin 3)) ≠
    Equiv.swap 0 1 := by decide
```

(`Group.isUnit` name latitude: `isUnit_of_invertible`/`IsUnit.mk` routes exist if the spelling differs; find with `exact?`. The guard needs `groupBarMap` non-private OR the examples inside the section — keep the examples INSIDE `section GroupBar` before `end GroupBar` so `private` visibility works.)

Run `lake build KRTheory.GroupCase` — sorries at the three stub sites.

- [ ] **Step 2 (GREEN): closure proofs**

`one_mem'`: front of `1` is `fun _ => Resets.id` (defeq): C1 both sides `Iff.rfl`-true; C2 vacuous (no `to` hypothesis survives `Resets.noConfusion`):

```lean
    refine ⟨fun _ _ => Iff.rfl, fun g g' x x' hx _ => ?_⟩
    exact absurd hx (by simp [wreath_one_left])
```

(latitude: the `show`-then-`simp` shape from `Reset.lean` if the projected-type forms stall; `(1 : WreathMonoid _ _).left g = Resets.id` is `rfl`-true so the `to`-hypothesis is refutable by `simp`/`noConfusion`.)

`mul_mem'` — `rintro w w' ⟨hC1, hC2⟩ ⟨hC1', hC2'⟩`, then case on the shape of `w`/`w'` fronts via C1 sampled at `1`. The product's front at `g` is `w.left g * w'.left (g * w.right)` (`Resets` mult: right factor wins unless it is `id`). Four cases:
  - A·A (both uniformly `id`): product front `id * id = id` — C1 ✓, C2 vacuous.
  - A·B: product front at `g` is `w'.left (g * w.right)`, a reset everywhere (C1 via `hC1'` and the reindex `g ↦ g * w.right`); C2: given samples at `g, g'`, apply `hC2'` at the points `g * w.right, g' * w.right` — the landing exponent matches: `(g * w.right) * w'.right = g * (w.right * w'.right)` by `mul_assoc`.
  - B·A: product front = `w.left g` (right factor `id` is neutral); C2: `T.act x (g * (w.right * w'.right)) = T.act (T.act x (g * w.right)) w'.right` via `T.act_mul` + `mul_assoc`, then `hC2` and congruence.
  - B·B: product front = `w'.left (g * w.right)`; C2 like A·B.
  The unit hypothesis is NOT needed in `mul_mem'` as stated (the reindex `g ↦ g * w.right` is used only to TRANSPORT C1/C2 between sample points, which the ∀-quantified conditions allow directly — spell each case by instantiating the ∀s at the shifted points; no bijectivity needed). If a case genuinely needs surjectivity of the reindex, `hg` is available — take it as a hypothesis on the submonoid's section variable instead (`variable (hg : …)` inside the section) and thread it; note which in the report.

`group_bar_div` — the covering:

```lean
  refine ⟨{ toSubmonoid := groupBarSub T
            stateMap := fun p => T.act p.1 p.2
            monoidMap :=
              { toFun := fun w => groupBarMap T w.1
                map_one' := rfl
                map_mul' := ?_ }
            stateMap_surj := fun x => ⟨(x, 1), by simp⟩
            monoidMap_surj := ?_
            equivariant := ?_ }⟩
```

  - `map_mul'`: `rintro ⟨w, hC1, hC2⟩ ⟨w', hC1', hC2'⟩`; unfold `groupBarMap` on the product (front at `1` is `w.left 1 * w'.left (1 * w.right) = w.left 1 * w'.left w.right` after `one_mul`); case on `w.left 1` and `w'.left w.right` shapes, transporting shape info with C1 where the sample point differs (`w'.left w.right` vs `w'.left 1`); the four cases mirror `BarMonoid`'s multiplication table:
    - A·A: `of (w.right * w'.right) = of w.right * of w'.right` ✓ `rfl`-ish.
    - A·B: product is type B with landing `x' ⊳ (product.right)`… goal `reset (…) = of w.right * reset (…)` — `of * reset = reset` and the landings agree by `hC2'` between sample points `w.right` and `1` (exponents `w.right * w'.right` vs `1 * (w.right * w'.right)` — `one_mul`).
    - B·A: `reset (x ⊳ (w.right * w'.right)) = reset (x ⊳ w.right) * of w'.right = reset ((x ⊳ w.right) ⊳ w'.right)` ✓ `T.act_mul`.
    - B·B: both sides the reset with `w'`-landing; `hC2'` aligns sample points as in A·B.
  - `monoidMap_surj`: `rintro (m | x₀)`:
    - `of m`: witness `⟨⟨fun _ => Resets.id, m⟩, C1 := fun _ _ => Iff.rfl, C2 := vacuous⟩`; `groupBarMap` value `of m` — `rfl`.
    - `reset x₀`: witness `⟨⟨fun g => Resets.to (T.act x₀ ↑(hg g).unit⁻¹), 1⟩, …⟩`; C1: both sides always-`to` (`to_ne_id`-style refutations); C2: `T.act (T.act x₀ ↑(hg g).unit⁻¹) (g * 1) = x₀` for every `g` — `mul_one`, `← T.act_mul`, `IsUnit.val_inv_mul` gives exponent `↑(hg g).unit⁻¹ * g = 1`, then `T.act_one`; both samples equal `x₀`. Value: `groupBarMap` reads front at `1`: `to (x₀ ⊳ ↑(hg 1).unit⁻¹)`, landing `(x₀ ⊳ ↑(hg 1).unit⁻¹) ⊳ (1 : T.M)`… simplify with the same identities to `reset x₀`. (If `(hg 1).unit⁻¹` resists `simp`, note `↑(hg 1).unit⁻¹ * 1 = ↑(hg 1).unit⁻¹` and `x₀ ⊳ (↑(hg 1).unit⁻¹ * 1) = x₀ ⊳ ↑(hg 1).unit⁻¹`, then a separate `have : (↑(hg 1).unit⁻¹ : T.M) = 1`? — CAREFUL: that is only true because `(hg 1).unit` has value `1` and unit-inverses of `1` are `1`; prove via `Units.ext`-style or avoid by instead using C2 at samples `1` and `g` to rewrite the landing to the constant `x₀ ⊳ (… * 1)` computed at any convenient sample. Latitude; the target value `reset x₀` is fixed.)
  - `equivariant`: `rintro ⟨x, g⟩ ⟨w, hC1, hC2⟩`; show `T.bar.act (T.act x g) (groupBarMap T w) = T.act (…wreath act…)`. Case on `w.left 1`'s shape, transporting to sample `g` by C1:
    - type A: both sides `(x ⊳ g) ⊳ w.right = x ⊳ (g * w.right)` — `T.act_mul`.
    - type B: LHS `= landing-of-groupBarMap = x₁ ⊳ w.right` with `x₁ := target at 1`; RHS `= (target at g) ⊳ (g * w.right)`-shaped after the wreath action unfolds; equal by `hC2` between samples `1` and `g` (`one_mul` aligns exponents).

Follow `Reset.lean`'s established `show`-then-rewrite discipline throughout — every goal in this section sits at projected types.

- [ ] **Step 3: Verify, commit**

```bash
lake build 2>&1 | tail -3
grep -rn "sorry" KRTheory/ KRTheory.lean
git add KRTheory/GroupCase.lean
git commit -m "Prove DKS 2.11 group bar division"
git push
```

---

### Task 7: Milestone close

**Files:**
- Modify: `scripts/AxiomCertificate.lean`, `.github/workflows/ci.yml` (count), `blueprint/src/chapters/groupcase.tex` (`\leanok`)

**Interfaces:** consumes everything; produces the acceptance state.

- [ ] **Step 1: Extend the certificate and its CI count**

Append to `scripts/AxiomCertificate.lean`:

```lean
#print axioms kaloujnine_krasner_div
#print axioms transfGroup_div_wreath_simples
#print axioms group_bar_div
```

In `.github/workflows/ci.yml`, update the count assertion from `-eq 12` to `-eq 15` (same line, same comment convention). Run `lake env lean scripts/AxiomCertificate.lean` — 15 lines, every axiom list within `{propext, Classical.choice, Quot.sound}`.

- [ ] **Step 2: Stamp the blueprint**

Add `\leanok` after each `\lean{...}` in `blueprint/src/chapters/groupcase.tex` (all seven entries — the chapter has no `\notready`).

- [ ] **Step 3: Full sweep, commit, CI**

```bash
lake build 2>&1 | tail -5
grep -rn "sorry" KRTheory/ KRTheory.lean
git add -A
git commit -m "Close milestone 6: extend axiom certificate, stamp blueprint leanok"
git push
gh pr checks 5 --watch
```

Expected: green, zero warnings, empty grep, both CI jobs green.

- [ ] **Step 4 (controller): final review, memory, handoff**

The SDD final whole-branch review serves as the milestone review (M5 ruling precedent). After it: update `kr-theory-project.md` process state (M6 done; next M7 — Theorem 3.1, whose FIRST task is the lemma-level blueprint chapter of [DKS] §3 per spec §3.8/§8; note `exists_pow_idempotent` finally gets its consumer in M7). PR handling stays the user's.
