# The Krohn–Rhodes Theorem in Lean 4

[![CI](https://github.com/juanbono/krohn-rhodes-theory/actions/workflows/ci.yml/badge.svg)](https://github.com/juanbono/krohn-rhodes-theory/actions/workflows/ci.yml)

A complete, machine-checked, `sorry`-free proof of the **Krohn–Rhodes prime
decomposition theorem** — the statement that every finite semigroup divides an
iterated wreath product of finite simple groups and copies of the three-element
flip-flop monoid.

The formalization follows Diekert, Kufleitner and Steinberg's *local divisor*
proof ([arXiv:1111.1585](https://arxiv.org/abs/1111.1585), cited throughout as
**[DKS]**), and is built on [Mathlib](https://github.com/leanprover-community/mathlib4).

| | |
|---|---|
| **Lean** | ~3,600 lines across 12 modules |
| **Sorries** | none |
| **Axioms** | `propext`, `Classical.choice`, `Quot.sound` only — checked in CI for 19 theorems |
| **Blueprint** | complete; dependency graph verified fully green in CI |

---

## Motivation

### The mathematics

Finite groups have a prime decomposition: the Jordan–Hölder theorem breaks any
finite group into simple groups, stacked by extensions. For twenty years after
that theory matured it was unclear whether finite *semigroups* — the algebraic
shadow of finite automata — admitted anything comparable. Semigroups are far
wilder than groups: no inverses, no cosets, no normal subgroups to quotient by.

Krohn and Rhodes answered this in 1965. Their theorem says that if you replace
"extension" with the **wreath product** (a cascade: one machine feeding another,
feedback-free) and "subgroup/quotient" with **division**, then finite semigroups
do decompose into primes, and the primes are exactly:

- **finite simple groups**, and
- the **flip-flop** — a two-state, three-element reset monoid, the minimal unit
  of memory.

This is the structural foundation of algebraic automata theory. It is what makes
"a finite automaton is a cascade of permutations and resets" a theorem rather
than a slogan, and it underlies the Krohn–Rhodes complexity hierarchy, the
group-free/aperiodic characterization of star-free languages, and the whole
Eilenberg variety programme.

### Why formalize it, and why now

Krohn–Rhodes has a reputation for being hard to check. The original proof runs
long, later treatments diverge in their conventions, and the standard textbook
routes (holonomy decomposition; the Zeiger construction) carry substantial
combinatorial bookkeeping. It is a classical, important, and genuinely
non-trivial theorem — precisely the profile where a machine-checked proof adds
something real.

As far as we could determine when this project started (August 2026), the
theorem had not been formalized in any proof assistant.

What made the attempt tractable is the **local divisor technique**. [DKS] give a
proof that is short enough to formalize in full: instead of the holonomy
machinery, the induction descends into the *local divisor* `Mc = cM ∩ Mc` at a
non-unit `c`, which is strictly smaller than `M` and — crucially — still
*divides* `M`. That last fact is what lets the strong form of the theorem
(every group factor divides the original monoid) survive the recursion, and it
is why this repo can state the strong form rather than a weakened one.

### As a learning project

This repository was written to learn finite semigroup theory and Lean
formalization at the same time, and its structure reflects that:

- **Blueprint first.** Every chapter of the informal mathematics
  ([`blueprint/`](blueprint/)) is written *before* the corresponding Lean, with
  `\lean{}` / `\leanok` annotations. The dependency graph is the progress
  dashboard, and CI refuses to go green until every node is filled.
- **Definitions validated on examples.** Every definitional file ends with
  concrete sanity checks — `flipFlop` really has 3 elements; `x ⊳ reset x₀` really
  equals `x₀`; the wreath of two flip-flops really has 27 monoid elements. A
  wrong-but-internally-consistent definition is the classic way a formalization
  loses months, and examples catch it at birth.
- **Design decisions recorded.** The full design document, including every
  amendment made mid-implementation and why, lives at
  [`docs/superpowers/specs/2026-08-17-krohn-rhodes-formalization-design.md`](docs/superpowers/specs/2026-08-17-krohn-rhodes-formalization-design.md).

If you are reading this to learn the material, the [Reading and references](#reading-and-references)
section below is meant as your syllabus.

---

## What is proved

Three theorems, in increasing generality of statement (decreasing structure of
the input). The first two live in the `KRTheory.TransMon` namespace; the
semigroup form is `KRTheory.krohnRhodes_semigroup`, alongside `SemigroupDivides`
and the `≺ₛ` notation. All three are `sorry`-free.

**1. Transformation form, strong version** ([`KRTheory/KrohnRhodes.lean`](KRTheory/KrohnRhodes.lean)):

```lean
theorem krohnRhodes (T : TransMon) (hT : T.Faithful) [Nonempty T.X] :
    ∃ L : List KRPrime,
      T ≺ wreathList (L.map KRPrime.toTransMon) ∧
      ∀ p ∈ L, ∀ G, p = KRPrime.grp G →
        IsSimpleGroup G.carrier ∧ G.carrier ≺ₘ T.M
```

A faithful finite transformation monoid strongly divides an iterated wreath
product of primes, and **every group factor divides the original monoid** — this
is the strong form, not merely "some simple groups exist".

**2. Abstract finite-monoid form** ([`KRTheory/KrohnRhodes.lean`](KRTheory/KrohnRhodes.lean)):

```lean
theorem krohnRhodes_monoid (M : Type) [Monoid M] [Finite M] :
    ∃ L : List KRPrime,
      M ≺ₘ (wreathList (L.map KRPrime.toTransMon)).M ∧
      ∀ p ∈ L, ∀ G, p = KRPrime.grp G →
        IsSimpleGroup G.carrier ∧ G.carrier ≺ₘ M
```

**3. Classical 1965 semigroup form** ([`KRTheory/SemigroupVersion.lean`](KRTheory/SemigroupVersion.lean)):

```lean
theorem krohnRhodes_semigroup (S : Type) [Semigroup S] [Finite S] :
    ∃ L : List KRPrime,
      S ≺ₛ (wreathList (L.map KRPrime.toTransMon)).M ∧
      ∀ p ∈ L, ∀ G, p = KRPrime.grp G →
        IsSimpleGroup G.carrier ∧ G.carrier ≺ₛ S
```

Notation: `≺` is strong division of transformation monoids, `≺ₘ` monoid
division, `≺ₛ` semigroup division, `≀` the wreath product. `KRPrime` is the
two-constructor inductive `flipflop | grp G` carrying *canonical* factor objects
(the flip-flop itself, `regular G`) rather than isomorphism classes — which is
why none of these statements needs a transformation-monoid isomorphism API.

### Scope

Deliberately **out** of scope for this version, and recorded as such in the
design document §2 and §9:

- Green's relations, Rees matrix theory, 0-simple semigroups
- The bound on the number of wreath factors ([DKS] Cor. 4.3)
- Holonomy decomposition; the automata/cascade formulation; Krohn–Rhodes
  complexity
- Uniqueness or minimality of the prime decomposition
- Universe polymorphism (everything is finite and lives in `Type`)

---

## Building

### Requirements

[`elan`](https://github.com/leanprover/elan) is the only prerequisite for the
Lean side; it reads [`lean-toolchain`](lean-toolchain) and installs the right
compiler automatically (currently `leanprover/lean4:v4.33.0`). Mathlib is pinned
to the `v4.33.0` release in [`lakefile.toml`](lakefile.toml), and every
dependency's exact revision is locked in
[`lake-manifest.json`](lake-manifest.json), so the build is reproducible.
Bump `lakefile.toml` and `lean-toolchain` together — a Mathlib release requires
its matching toolchain.

### The proof

```sh
git clone https://github.com/juanbono/krohn-rhodes-theory
cd krohn-rhodes-theory
lake exe cache get     # download prebuilt Mathlib oleans — do not skip
lake build
```

`lake exe cache get` is not optional in practice: building Mathlib from source
takes hours, and downloading it takes minutes.

### The axiom certificate

The strongest single check on the result. It prints the axiom dependencies of
all 19 milestone-terminal theorems, including the three main ones:

```sh
lake env lean scripts/AxiomCertificate.lean
```

Every line must report at most `propext`, `Classical.choice`, `Quot.sound` — the
three standard axioms of Lean's classical foundation. CI parses this output and
fails the build on anything else, which is what rules out an accidental `axiom`
or a `native_decide` slipping in. (One theorem, `regular_faithful`, depends on no
axioms at all.)

### The blueprint

Two independent build paths, both exercised in CI.

**PDF** — needs a TeX installation with `latexmk`:

```sh
cd blueprint/src
latexmk -pdf print.tex
```

**Web version with the dependency graph** — needs Python, TeX, and Graphviz:

```sh
pip install -r blueprint/requirements.txt
leanblueprint web          # from the repo root
```

> **Gotcha.** plasTeX resolves `\input` through `kpsewhich`, so **without a TeX
> installation every chapter silently fails to load** and you get an empty
> blueprint with no error. If your output looks suspiciously short, that is why.
> On Debian/Ubuntu: `apt-get install texlive-latex-base texlive-latex-extra
> graphviz libgraphviz-dev`.

To verify that every `\lean{...}` annotation names a declaration that actually
exists (requires a completed `lake build` and a prior `leanblueprint web`):

```sh
leanblueprint checkdecls
```

Publishing the web blueprint to GitHub Pages is deliberately not wired up — CI
builds it and uploads it as an artifact instead.

---

## Repository tour

The dependency order below is also a reasonable reading order.

| File | Mathematics | [DKS] |
|---|---|---|
| [`FiniteMonoid.lean`](KRTheory/FiniteMonoid.lean) | Finite-monoid preliminaries: idempotent powers, one-sided inverses are units, submonoid counting, the minimal-generating-set split that produces a non-unit generator | §2 prelims |
| [`TransMon/Basic.lean`](KRTheory/TransMon/Basic.lean) | `TransMon` — a finite state set with a right action of a finite monoid; faithfulness; the regular representation | §2.1 |
| [`TransMon/Division.lean`](KRTheory/TransMon/Division.lean) | Monoid division `≺ₘ` and strong division `≺` of transformation monoids, both preorders; the glue lemma extracting `≺ₘ` from `≺` | §2.3 |
| [`TransMon/Wreath.lean`](KRTheory/TransMon/Wreath.lean) | The wreath product `≀` and its monoid structure; `wreathList` as a fold | §2.2 |
| [`TransMon/WreathDivision.lean`](KRTheory/TransMon/WreathDivision.lean) | The division calculus of `≀`: monotonicity, one-directional associativity, trivial-factor absorption, `wreathList_append` — the gluing lemmas of the main induction | §2.2–2.3 |
| [`TransMon/Bar.lean`](KRTheory/TransMon/Bar.lean) | The bar operation `T.bar`, adjoining all constant maps ("resets"), so cascade decompositions can overwrite state | §2.4 |
| [`TransMon/Reset.lean`](KRTheory/TransMon/Reset.lean) | Reset monoids `U(X)`, the flip-flop `U(Bool)`, and the induction showing every reset monoid divides a wreath of flip-flops | §2.5, Lem. 2.12 |
| [`TransMon/LocalDivisor.lean`](KRTheory/TransMon/LocalDivisor.lean) | The local divisor `Mc = cM ∩ Mc`: faithfulness is inherited, cardinality strictly drops at a non-unit, and `Mc ≺ₘ M` | §2.5, Lem. 2.13 |
| [`GroupCase.lean`](KRTheory/GroupCase.lean) | The base case: Kaloujnine–Krasner, decomposition into simple factors by peeling maximal normal subgroups, and [DKS] 2.11 for barred transformation groups | §2.4, Lem. 2.11 |
| [`Decomposition.lean`](KRTheory/Decomposition.lean) | **The engine.** [DKS] Theorem 3.1: `T.bar ≺ (localDivisor T c).bar ≀ (rightFactor T N).bar` | Thm 3.1 |
| [`KrohnRhodes.lean`](KRTheory/KrohnRhodes.lean) | `KRPrime`, the main induction on `Nat.card T.M`, and the two monoid-level theorems | Thm 4.1 |
| [`SemigroupVersion.lean`](KRTheory/SemigroupVersion.lean) | Semigroup division `≺ₛ`; the classical statement, via adjoining an identity (`WithOne`) | — |

### Formalization notes worth knowing

A few decisions recur throughout and are worth understanding before reading the
Lean:

- **Right actions, spelled out.** `x ⊳ m`, with `x ⊳ (m * n) = (x ⊳ m) ⊳ n` —
  `m` acts *first*. This is the automata-theoretic convention, matches [DKS]
  symbol for symbol, and avoids `op`/`unop` noise throughout. Mathlib's own
  `DFA.step : σ → α → σ` is the design precedent.
- **Fresh structures everywhere, to dodge instance diamonds.** `WreathMonoid`,
  `BarMonoid`, `Resets`, and `LocalDivisor` are each defined as a *new* type
  rather than as `Prod`, `Sum`, `Option`, or a subtype — because in every case
  the intended multiplication is not the one Mathlib would infer for the reused
  type. Reusing them would plant a competing instance and produce a diamond.
- **`Finite`, not `Fintype`.** Finiteness is bundled as a `Prop`. Carrying
  `Fintype` data forced `DecidablePred` side conditions through subtype-heavy
  constructions (the local divisor's carriers are subtypes twice over) and made
  the wreath product `noncomputable`. Cardinality is uniformly `Nat.card`.
- **Classical choice is quarantined.** The places that genuinely need it — the
  local divisor's well-definedness, sections of surjections in
  `StrongDivides.wreath`, the Kaloujnine–Krasner section — isolate it behind
  specification lemmas, so no downstream statement mentions a choice.

---

## Reading and references

This section is the syllabus. Items marked **[required]** are the ones you
genuinely need to follow the proof in this repository; **[recommended]** items
give context, alternative routes, or depth.

### Start here

If you read three things, read these.

1. **Oded Maler, "On the Krohn–Rhodes Cascaded Decomposition Theorem"** (2010),
   in *Time for Verification: Essays in Memory of Amir Pnueli*, LNCS 6200,
   pp. 260–278. [Free PDF](http://www-verimag.imag.fr/~maler/Papers/kr-new.pdf) ·
   [DOI](https://doi.org/10.1007/978-3-642-13754-9_12)
   **[recommended, but read it first]** — By some distance the most approachable
   modern exposition. Written for a verification audience, in automata language,
   with the geometric intuition made explicit. Read this before anything else;
   it tells you what the theorem *means* before you meet the machinery.

2. **V. Diekert, M. Kufleitner, B. Steinberg, "The Krohn–Rhodes Theorem and
   Local Divisors"**, Fundamenta Informaticae 116 (2012).
   [arXiv:1111.1585](https://arxiv.org/abs/1111.1585)
   **[required]** — *This is the text this repository formalizes.* Twelve pages.
   Every definition, lemma number, and proof strategy in `KRTheory/` traces back
   to it; the module docstrings cite it by section. If you read one thing
   alongside the Lean, read this.

3. **Jean-Éric Pin, "Mathematical Foundations of Automata Theory"** (lecture
   notes, continuously revised).
   [Free PDF](https://www.irif.fr/~jep/PDF/MPRI/MPRI.pdf)
   **[required for background]** — The standard free reference for the algebraic
   side of automata theory: transition monoids, syntactic monoids, varieties,
   Green's relations. Use it as the dictionary when [DKS] assumes a notion you
   do not have. Chapters on transition and syntactic monoids are the relevant
   prerequisite.

### Prerequisites — algebra

**Group theory** is used heavily in the base case of the induction
([`GroupCase.lean`](KRTheory/GroupCase.lean)). You need: normal subgroups and
quotients, simple groups, the existence half of Jordan–Hölder, wreath products,
and the Kaloujnine–Krasner embedding theorem.

- **J. J. Rotman, *An Introduction to the Theory of Groups***, 4th ed., Springer
  GTM 148, 1995. **[recommended]** — Standard graduate text; covers wreath
  products and the Krasner–Kaloujnine embedding theorem (`G/N`-by-`N` extensions
  embed in `N ≀ G/N`), which is `kaloujnine_krasner_div` in this repo. Any
  comparable algebra text (Dummit & Foote, Isaacs) will do for the rest.
- **J. D. P. Meldrum, *Wreath Products of Groups and Semigroups***, Pitman
  Monographs and Surveys in Pure and Applied Mathematics 74, Longman, 1995.
  **[recommended]** — The dedicated monograph. Part 1 is wreath products of
  groups; Part 2 covers semigroups *including a treatment of Krohn–Rhodes*. Go
  here if the wreath product is the part that feels slippery.

**Semigroup and monoid theory** is the ambient setting. You need: monoids,
submonoids, quotients by congruences, ideals, units versus non-units in a finite
monoid, and the notion of *division*.

- **J. M. Howie, *Fundamentals of Semigroup Theory***, LMS Monographs New Series
  12, Clarendon Press, Oxford, 1995. **[required as a reference]** — The
  standard modern introduction. You do not need all of it: Chapters 1–2 (basic
  notions, Green's equivalences) plus the material on finite semigroups is
  enough for this project. Green's relations are *not* used anywhere in this
  formalization, but every other text assumes you know them.
- **A. H. Clifford, G. B. Preston, *The Algebraic Theory of Semigroups***,
  Vols. I & II, AMS Mathematical Surveys 7, 1961/1967. **[recommended]** — The
  classical reference. Encyclopaedic and still useful, but dated in outlook;
  reach for it to look things up, not to learn from.
- **J. Rhodes, B. Steinberg, *The q-theory of Finite Semigroups***, Springer
  Monographs in Mathematics, 2009.
  [DOI](https://doi.org/10.1007/b104443) · [errata](https://bsteinberg.ccny.cuny.edu/Webpage/book2.html)
  **[recommended, advanced]** — 666 pages, and the modern reference for
  everything Krohn–Rhodes-adjacent: complexity, pseudovarieties, the profinite
  approach. This is where to go *after* the theorem, not before it. Note that
  Steinberg is a co-author of [DKS], so the vocabulary matches.
- **J.-É. Pin, *Varieties of Formal Languages***, Plenum, 1986.
  **[recommended]** — The bridge from finite semigroups to language theory; the
  reason anyone in computer science cares about this algebra.

### Prerequisites — Lean 4 and Mathlib

- **[Mathematics in Lean](https://leanprover-community.github.io/mathematics_in_lean/)**
  **[required if you are new to Lean]** — The practical, hands-on route.
  Structures, type classes, and algebraic hierarchies are the chapters that
  matter for this codebase.
- **[Theorem Proving in Lean 4](https://leanprover.github.io/theorem_proving_in_lean4/)**
  **[recommended]** — The systematic treatment of the language and its logic.
  Read it when *Mathematics in Lean* leaves you unsure why something elaborates
  the way it does.
- **[Mathlib4 API documentation](https://leanprover-community.github.io/mathlib4_docs/)**
  **[required as a reference]** — Especially `Mathlib.GroupTheory.RegularWreathProduct`
  (the group-only wreath product, notation `≀ᵣ`), `Mathlib.Computability.DFA`
  (design precedent for raw actions), `WithOne`, `Submonoid`, and `Con`.
- **[leanblueprint](https://github.com/PatrickMassot/leanblueprint)**
  **[recommended]** — The blueprint tool used here. Its README explains the
  workflow (informal mathematics first, dependency graph as dashboard) that this
  repository is organized around.
- **[Lean Zulip](https://leanprover.zulipchat.com/)** — where formalization
  questions actually get answered.

### The classical route, and alternatives to the proof used here

Worth reading to understand *why* the local-divisor proof was chosen, and what
the alternatives cost.

- **K. Krohn, J. Rhodes, "Algebraic theory of machines. I. Prime decomposition
  theorem for finite semigroups and machines"**, Trans. Amer. Math. Soc. 116
  (1965), 450–464. **[recommended]** — The original. Read it for the history and
  the framing; it is not the proof anyone formalizes today.
- **M. A. Arbib (ed.), *Algebraic Theory of Machines, Languages, and
  Semigroups***, Academic Press, 1968. **[recommended]** — The first
  book-length treatment, with chapters by Krohn and Rhodes themselves.
- **S. Eilenberg, *Automata, Languages, and Machines*, Vol. B**, Academic Press,
  1976. **[recommended]** — The holonomy route, and the most influential
  treatment of the theorem. Eilenberg's decomposition is sharper than the one
  formalized here (it gives structural information about the factors), at the
  cost of substantially more machinery — which is exactly why this project did
  not take that path. Vol. A is the prerequisite.
- **A. Ginzburg, *Algebraic Theory of Automata***, Academic Press, 1968, and
  **W. M. L. Holcombe, *Algebraic Automata Theory***, Cambridge University
  Press, 1982. **[recommended]** — Two accessible textbook treatments from the
  automata side. Holcombe in particular is a gentler introduction than Eilenberg.
- **H. Straubing, *Finite Automata, Formal Logic, and Circuit Complexity***,
  Birkhäuser, 1994. **[recommended]** — Where the algebra pays off: Krohn–Rhodes
  and the variety theory in service of logic and circuit lower bounds.
- **J. Sakarovitch, *Elements of Automata Theory***, Cambridge University Press,
  2009. **[recommended]** — Comprehensive modern reference for automata theory
  generally; useful surrounding context.
- **P. Dömösi, C. L. Nehaniv, *Algebraic Theory of Automata Networks: An
  Introduction***, SIAM Monographs on Discrete Mathematics and Applications 11,
  2005. [DOI](https://doi.org/10.1137/1.9780898718492) **[recommended]** —
  Chapter 3 is a full treatment of Krohn–Rhodes theory and complete classes,
  from the automata-networks perspective.
- **J.-É. Pin (ed.), *Handbook of Automata Theory***, Vols. I & II, EMS Press,
  2021. [Publisher](https://ems.press/books/standalone/172) **[recommended]** —
  The current survey of record. Use it to find the modern state of any
  neighbouring topic.

### Going further

Directions this formalization deliberately stops short of, with the entry point
for each. These correspond to the future-work ledger in the design document §9.

- **The local divisor technique in general.** V. Diekert, M. Kufleitner, *A
  Survey on the Local Divisor Technique*,
  [arXiv:1410.6026](https://arxiv.org/abs/1410.6026). The natural sequel to
  [DKS]: the same technique applied well beyond Krohn–Rhodes.
- **Aperiodic monoids and star-free languages.** The Schützenberger theorem, and
  the corollary that a monoid is aperiodic exactly when it divides a wreath of
  flip-flops — the group-free half of this theorem. Pin's *Mathematical
  Foundations* and Straubing both cover it. This is the most natural next
  formalization target.
- **Krohn–Rhodes complexity.** The minimal number of group levels in a
  decomposition; decidability of complexity is a famous open problem. Rhodes &
  Steinberg, *q-theory*, is the reference.
- **Holonomy decomposition, computationally.** H. P. Zeiger's construction, and
  its implementation: **SgpDec**, a GAP package for cascade
  (de)compositions of transformation semigroups by A. Egri-Nagy and
  C. L. Nehaniv. [Package](https://gap-packages.github.io/sgpdec/) ·
  [arXiv:1501.03217](https://arxiv.org/abs/1501.03217). The best way to *play*
  with decompositions of concrete semigroups.
- **Applications outside mathematics.** J. Rhodes, C. L. Nehaniv, *Applications
  of Automata Theory and Algebra: Via the Mathematical Theory of Complexity to
  Biology, Physics, Psychology, Philosophy, and Games*, World Scientific, 2010 —
  the long-unpublished "Wild Book". Idiosyncratic and worth knowing about.

---

## Project documents

- [Design document](docs/superpowers/specs/2026-08-17-krohn-rhodes-formalization-design.md) —
  the mathematical blueprint, the Lean architecture and every decision behind it,
  the milestone roadmap, the risk register, and the future-work ledger. Amendments
  made during implementation are recorded inline with dates.
- [Implementation plans](docs/superpowers/plans/) — covering milestones 0 through 9.
- [Blueprint](blueprint/) — the informal mathematics, chapter by chapter.

---

## License

Apache License 2.0 — see [`LICENSE`](LICENSE). This matches Mathlib's own
license, so the infrastructure earmarked for upstreaming (the finite-monoid
lemmas, the monoid-level wreath product) can be contributed without a licensing
obstacle.
