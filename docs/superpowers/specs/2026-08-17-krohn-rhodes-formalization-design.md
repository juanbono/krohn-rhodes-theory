# Krohn–Rhodes Theory in Lean 4 — Design Document

**Date:** 2026-08-17
**Status:** Approved design, pre-implementation
**Blueprint text:** V. Diekert, M. Kufleitner, B. Steinberg, *The Krohn-Rhodes Theorem and Local Divisors*, Fund. Inform. 116 (2012), arXiv:1111.1585 — cited below as **[DKS]**.

---

## 1. Goal and success criteria

Produce a **sorry-free, machine-checked proof of the Krohn–Rhodes theorem** in Lean 4, as a standalone project depending on Mathlib, written in Mathlib style so infrastructure can be upstreamed later. As far as we could determine (2026-08), no formalization of this theorem exists in any proof assistant.

The project deliberately serves a second purpose: **learning finite semigroup theory and Lean formalization together**. Consequences: the informal mathematics is written down first (leanblueprint), definitions are validated on concrete examples before proofs depend on them, and milestones are sequenced from gentle to hard.

**Definition of done (v1):**

1. `krohnRhodes` — transformation-monoid form (strong form: group factors divide the original monoid) — proved without `sorry`.
2. `krohnRhodes_monoid` — abstract finite-monoid corollary.
3. `krohnRhodes_semigroup` — classical 1965 finite-semigroup statement.
4. `#print axioms` on all three shows at most `Classical.choice`, `propext`, `Quot.sound`.
5. CI builds the project and the blueprint; blueprint dependency graph fully green.

## 2. Non-goals (v1)

- Green's relations, Rees matrix theory, 0-simple semigroups.
- The size bound on the number of wreath factors ([DKS] Cor. 4.3).
- Holonomy decomposition; automata/cascade formulation; Krohn–Rhodes complexity.
- Uniqueness/minimality of the prime decomposition.
- Universe polymorphism (all carriers live in `Type`; everything is finite).

These are recorded in §9 (future ledger), not forgotten.

## 3. Mathematical blueprint

This section fixes the mathematics we commit to formalize, following [DKS] with all bookkeeping made explicit. Section numbers like (2.11) refer to [DKS].

### 3.1 Transformation monoids

A **finite transformation monoid** T = (X, M) is a finite set X, a finite monoid M, and a **right action** `x · m` satisfying `x·1 = x` and `x·(mn) = (x·m)·n`. Right actions are the native convention of automata theory: `x·(mn)` means "from state x, first do m, then n".

T is **faithful** if `(∀ x, x·m = x·n) → m = n`. Faithfulness is a predicate, not part of the structure. Any (X, M) has a faithful quotient, but v1 only needs:

- **Regular representation**: `regular M := (M, M)` with right multiplication. Always faithful (evaluate at 1).

### 3.2 Division

- **Monoid division** `M ≺ₘ N`: there is a submonoid N′ ≤ N and a surjective monoid hom N′ ↠ M. Preorder (refl, trans). Basic feeders: submonoids divide, quotients (surjective hom images) divide.
- **Strong division of transformation monoids** `(X,M) ≺ (Y,N)` ([DKS] §2.3): there exist a submonoid N′ ≤ N, a **surjective function** φ : Y ↠ X, and a surjective monoid hom ψ : N′ ↠ M with equivariance `φ(y) · ψ(n) = φ(y·n)` for all y ∈ Y, n ∈ N′.
- **Glue lemma**: `(X,M) ≺ (Y,N) → M ≺ₘ N` (read ψ off the definition). This is how all abstract corollaries are extracted.
- Strong division is a preorder. Transitivity composes the φ's and pulls back submonoids along the ψ's.
- **Semigroup division** `S ≺ₛ T` (only in `SemigroupVersion.lean`): subsemigroup + surjective semigroup hom. Feeder: `M ≺ₘ N → M ≺ₛ N`.

### 3.3 Wreath product

For T₁ = (X, M) and T₂ = (Y, N) ([DKS] §2.2):

```
T₁ ≀ T₂ := ( X × Y ,  (Y → M) × N )
(f, n) * (g, k)  :=  (fun y => f y * g (y·n),  n*k)
(x, y) · (f, n)  :=  (x · f y,  y · n)
```

Intuition: a cascade of two machines; the back machine N sees the input directly, the front machine M sees the input *and* the back machine's current state (that is what `Y → M` encodes).

**Iterated wreath products** are a fold over a list:

```
wreathList : List TransMon → TransMon := List.foldr (· ≀ ·) trivialTM
```

where `trivialTM` is the one-point, one-element transformation monoid. Fixing the association via a fold avoids carrying an associativity isomorphism through every statement. We still need associativity **once**, in one direction, as a division (§3.3 lemmas below).

Lemmas required:

- `Monoid ((Y → M) × N)` with the multiplication above (associativity is a direct computation).
- `wreath_div_wreath` (monotonicity): `S₁ ≺ T₁ → S₂ ≺ T₂ → S₁ ≀ S₂ ≺ T₁ ≀ T₂`. Proof note: the front component needs functions constant on φ₂-fibers and a choice of section of φ₂; this is the standard proof, mildly fiddly.
- `wreath_assoc_div`: `(P ≀ Q) ≀ R ≺ P ≀ (Q ≀ R)`. The underlying map is currying; expected to be an isomorphism, but only the division direction is needed.
- `trivial_wreath_div` / `wreath_trivial_div`: absorption of `trivialTM` up to division.
- `wreathList_append`: `wreathList L₁ ≀ wreathList L₂ ≺ wreathList (L₁ ++ L₂)` (induction on L₁ using the two lemmas above). This is the lemma that glues recursive decompositions.

### 3.4 The bar operation (adjoining resets)

`T̄ = (X, M̄)` where `M̄` adjoins to M all **constant maps** on X. Cascade decompositions need the ability to overwrite the front coordinate, so the induction runs through barred monoids ([DKS] §2.4).

Carrier: `M ⊕ X` (`inl m` = m acting as before, `inr x₀` = reset to x₀). Multiplication (remember: left factor acts first):

```
inl m * inl n  = inl (m*n)
inl m * inr x₀ = inr x₀            -- doing m then resetting = resetting
inr x₀ * inl m = inr (x₀ · m)      -- resetting then doing m = resetting to x₀·m
inr x₀ * inr x₁ = inr x₁
```

Lemmas: monoid instance (case bash), action instance, `bar_divides : T ≺ T̄`, and monotonicity `S ≺ T → S̄ ≺ T̄` if the induction turns out to need it (flagged, not assumed).

Degenerate-case audit (implementation task): `|X| ≤ 1` makes resets collide with the identity; faithfulness claims about T̄ must be checked there. All main-line uses keep bars on the *left* of ≺, where this is harmless.

### 3.5 Reset monoids and the flip-flop

`U(X) := (X, resets + identity)`. Implementation: monoid carrier `Option X` — `none` = identity, `some x` = reset to x, multiplication `a * b = if b = none then a else b`.

The **flip-flop** is `flipFlop := U(Bool)`: 2 states, 3 elements — identity plus two resets. This is the unique non-group prime of the theory.

- ([DKS] 2.12) `reset_div_flipFlops`: for finite X, `U(X)` divides an iterated wreath product of flip-flops. Proof: induction on |X| (split X into two blocks; one flip-flop selects the block, smaller reset monoids act inside).
- Note `U(X)` is reset-closed: `U(X)̄` adds nothing new (up to division), so no bars are needed on flip-flop factors.

### 3.6 Local divisors

For c ∈ M ([DKS] §2.5): carrier `Mc := cM ∩ Mc`, multiplication `mc ∘ cn := mcn`, identity c. Well-definedness: if `u = mc = m′c` and `v = cn`, then `u ∘ v = m*v = m′*v`; in Lean, define `u ∘ v := Classical.choose (u ∈ Mc) * v` and prove independence of the choice.

The local divisor acts on `Xc := { x·c | x ∈ X }` by `ξ ∘ (cm) := ξ · m` (well-defined, lands in Xc).

Three lemmas, all load-bearing:

1. `localDivisor_faithful` ([DKS] 2.13): (X, M) faithful → (Xc, Mc) faithful.
2. `localDivisor_card_lt`: c **not a unit** → `|Mc| < |M|`. Proof: `Mc ⊆ cM ⊆ M`; if equality held then `1 ∈ cM`, making c right-invertible, hence (finite monoid, §3.0 prelims) a unit.
3. `localDivisor_divides : Mc ≺ₘ M`. Proof: `N := {m | c*m ∈ Mc}` is a submonoid of M and `m ↦ c*m` is a surjective monoid hom N ↠ Mc. **This is what makes the strong form survive recursion** — simple groups produced inside Mc divide Mc, hence divide M by transitivity.

Prelims needed (`FiniteMonoid.lean`): in a finite monoid, an element with a one-sided inverse is a unit; every element has an idempotent power (pigeonhole).

### 3.7 The group case

Base case of the induction: M = G a finite group.

- `compositionSeries_exists`: every finite group has a chain 1 = G₀ ⊴ G₁ ⊴ … ⊴ Gₙ = G with simple quotients. (Survey Mathlib's Jordan–Hölder framework first; existence-only is a short direct induction via a maximal proper normal subgroup if the framework doesn't fit.)
- `kaloujnine_krasner_div`: for N ⊴ G, `regular G ≺ regular N ≀ regular (G ⧸ N)`. Uses a classical section of the quotient map; equivariance is the classical Kaloujnine–Krasner computation.
- `transfGroup_div_wreath_simples`: chaining the above along a composition series (induction on its length, glued by `wreath_div_wreath` and `wreathList_append`): `regular G ≺ wreathList` of `regular Gᵢ` with each Gᵢ simple and `Gᵢ ≺ₘ G` (each Gᵢ is a quotient of a subgroup of G).
- ([DKS] 2.11) `group_bar_div`: `(X, G)̄ ≺ (X, U(X)) ≀ (G, G)` for a faithful transformation group (X, G). Note the right factor is the *regular* (G, G) even when X ≠ G.

Combined group case: `(X,G)̄ ≺ flip-flops ≀ simple group factors`, all groups dividing G.

### 3.8 The main decomposition ([DKS] Thm 3.1)

If (X, M) is faithful, M is generated by N ∪ {c} where N ≤ M is a submonoid and c is **not a unit**, then

```
(X, M)̄  ≺  (X·c, Mc)̄  ≀  (X ⊔ N, N)̄
```

The right factor's state space is X ⊔ N with N acting on X by restriction and on N by right multiplication; the disjoint union with the regular part is exactly what keeps the right factor **faithful**, so the induction hypothesis applies to it.

The covering construction (the φ and ψ of the division) is the technical heart of the paper and of this project. **Open point:** its lemma-level structure is transcribed from [DKS] §3 into the blueprint as the *first task of milestone 7*, before any Lean is written for it.

### 3.9 The induction and the main theorems

**Induction predicate**, for faithful finite T = (X, M):

> Q(T): there is a list L of factors, each either `flipFlop` or `regular G` with G a nontrivial finite simple group and `G ≺ₘ M`, such that `T̄ ≺ wreathList L`.

**Claim: Q holds for all faithful finite T**, by strong induction on (|M|, |X|) lexicographically.

- **M a group**: §3.7 gives Q directly (groups produced are subquotients of G, dividing G; flip-flops from §3.5).
- **M not a group**: pick a minimal generating set A of M; some c ∈ A is not a unit (otherwise the units form a submonoid containing A, forcing M to be a group — prelim lemma). Let N := ⟨A ∖ {c}⟩; minimality gives c ∉ N, so N is proper: |N| < |M|. Apply Thm 3.1:
  `T̄ ≺ (X·c, Mc)̄ ≀ (X ⊔ N, N)̄`.
  - (X·c, Mc) is faithful (3.6.1) and |Mc| < |M| (3.6.2) → IH gives Q(X·c, Mc); its groups divide Mc ≺ₘ M (3.6.3), hence divide M.
  - (X ⊔ N, N) is faithful (regular part) and |N| < |M| (state space grew — this is why the measure is lex with |M| first) → IH gives Q(X ⊔ N, N); its groups divide N ≤ M, hence divide M.
  - Glue with `wreath_div_wreath`, `wreathList_append`, transitivity.

**Main theorems** (target signatures, provisional syntax):

```lean
/-- Krohn–Rhodes, transformation form, strong version. -/
theorem krohnRhodes (T : TransMon) (hT : T.Faithful) :
    ∃ L : List KRPrime,
      T ≺ wreathList (L.map KRPrime.toTransMon) ∧
      ∀ p ∈ L, ∀ G, p = .grp G → IsSimpleGroup G.carrier ∧ G.carrier ≺ₘ T.M

/-- Abstract finite monoid form (via the regular representation). -/
theorem krohnRhodes_monoid (M : Type) [Monoid M] [Fintype M] :
    ∃ L : List KRPrime, M ≺ₘ (wreathList (L.map KRPrime.toTransMon)).M ∧
      ∀ p ∈ L, ∀ G, p = .grp G → IsSimpleGroup G.carrier ∧ G.carrier ≺ₘ M

/-- Classical 1965 semigroup form (via WithOne S = S¹). -/
theorem krohnRhodes_semigroup (S : Type) [Semigroup S] [Fintype S] :
    ∃ L : List KRPrime, S ≺ₛ (wreathList (L.map KRPrime.toTransMon)).M ∧
      ∀ p ∈ L, ∀ G, p = .grp G → IsSimpleGroup G.carrier ∧ G.carrier ≺ₛ S
```

(The factor condition is the same in all three; in the semigroup form the group divisors are semigroup divisors of S — the exact phrasing of that last conjunct is settled at milestone 9, since `G ≺ₛ S` vs `G ≺ₘ WithOne S` are interderivable there.)

Here `KRPrime` is a small inductive — `flipflop | grp (G : BundledFinGroup)` — with `toTransMon` sending `flipflop` to the canonical flip-flop and `grp G` to `regular G`. Making the list contain *canonical objects* (rather than "some F isomorphic to a flip-flop") keeps the statement tight without needing a TransMon-isomorphism API in v1. `T ≺ T̄` (3.4) removes the bar from the final statements.

For `krohnRhodes_semigroup`: S ≺ₛ S¹ = `WithOne S` (Mathlib), apply the monoid form, transfer along `M ≺ₘ N → M ≺ₛ N` and transitivity of ≺ₛ.

## 4. Lean architecture

### 4.1 The core structure (approved)

```lean
structure TransMon : Type 1 where
  X : Type
  M : Type
  [fintypeX : Fintype X]
  [monoidM : Monoid M]
  [fintypeM : Fintype M]
  act : X → M → X
  act_one : ∀ x, act x 1 = x
  act_mul : ∀ x m n, act x (m * n) = act (act x m) n
```

**Decision record — why this shape:**

- **Bundled**, because the theorem quantifies over a `List` of transformation monoids and constructions (`≀`, bar, local divisor) are functions `TransMon → … → TransMon`. Unbundled carriers cannot form lists.
- **Raw right action** (not `MulAction Mᵐᵒᵖ X`, not a left action): formulas match [DKS] symbol-for-symbol, proof states stay free of `op/unop` noise, and this matches Mathlib's own `DFA.step : σ → α → σ` design. Cost accepted: a self-written ~30-line action lemma kit. Adapters to Mathlib's `MulAction` can be derived later if ever needed; the reverse retrofit would not be possible.
- Carriers in `Type` (no universe polymorphism): everything is finite; `Type 1` structure, `List TransMon` works.
- `Fintype` fields registered as instances via `attribute [instance]`. `DecidableEq` is **not** bundled; proofs use classical decidability locally (`open scoped Classical` or `Classical.dec`), while concrete examples (`Bool`, `Fin n`, `Option _`) remain computable through their native instances.
- `Faithful` is a `Prop`-valued predicate (likely a class) on `TransMon`, not a field: the bar and wreath constructions do not preserve it uniformly, and non-faithful objects appear naturally mid-proof.

### 4.2 Conventions

- Right-action notation: scoped infix, provisionally `x ⊳ m`; division `S ≺ T` (strong), `M ≺ₘ N` (monoid), `S ≺ₛ T` (semigroup); wreath `S ≀ T`. Check for notation clashes with Mathlib at implementation time (Mathlib uses `≀ᵣ` for `RegularWreathProduct`; plain `≀` believed free). All notations scoped to a `KRTheory` namespace.
- Naming follows Mathlib conventions (`camelCase` defs, `snake_case` theorems, `Div`/`div` spelled out as `divides` to avoid clash with `Div` the typeclass).
- Every definitional file ends with `example`-based sanity checks on concrete instances (see §6).
- File-level docstrings state the [DKS] reference for each result.

### 4.3 API map (file → key declarations)

| File | Declarations |
|---|---|
| `FiniteMonoid.lean` | `exists_pow_idempotent`, `isUnit_of_mul_eq_one_right/left` (finite), `isUnit_of_generators_units` (units-only generating set ⇒ group) |
| `TransMon/Basic.lean` | `TransMon`, action notation + lemma kit, `Faithful`, `trivialTM`, `regular`, `regular_faithful`, examples |
| `TransMon/Division.lean` | `MonoidDivides` (`≺ₘ`), `StrongDivides` (`≺`), both preorders, `strongDivides.monoidDivides` (glue), submonoid/quotient feeders |
| `TransMon/Wreath.lean` | `wreath` (`≀`) + monoid & action instances, `wreath_div_wreath`, `wreath_assoc_div`, `trivialTM` absorption, `wreathList`, `wreathList_append` |
| `TransMon/Bar.lean` | `bar`, monoid/action instances, `bar_divides : T ≺ T.bar`, (optional) `bar_mono` |
| `TransMon/Reset.lean` | `resetMonoid` (= `U(X)` via `Option X`), `flipFlop`, `reset_div_flipFlops` ([DKS] 2.12) |
| `TransMon/LocalDivisor.lean` | `localDivisor`, monoid/action instances, `localDivisor_faithful` (2.13), `localDivisor_card_lt`, `localDivisor_divides` |
| `GroupCase.lean` | `compositionSeries_exists` (or Mathlib reuse), `kaloujnine_krasner_div`, `transfGroup_div_wreath_simples`, `group_bar_div` (2.11) |
| `Decomposition.lean` | [DKS] Thm 3.1 `decomposition` and its covering construction |
| `KrohnRhodes.lean` | `BundledFinGroup`, `KRPrime`, `KRPrime.toTransMon`, the induction, `krohnRhodes`, `krohnRhodes_monoid` |
| `SemigroupVersion.lean` | `SemigroupDivides` (`≺ₛ`), `monoidDivides.semigroupDivides`, `withOne` transfer, `krohnRhodes_semigroup` |

## 5. Project layout

```
kr-theory/
├── lakefile.toml, lean-toolchain        # pinned to Mathlib's toolchain
├── KRTheory.lean                        # root import
├── KRTheory/                            # files as in §4.3
│   ├── FiniteMonoid.lean
│   ├── TransMon/{Basic,Division,Wreath,Bar,Reset,LocalDivisor}.lean
│   ├── GroupCase.lean
│   ├── Decomposition.lean
│   ├── KrohnRhodes.lean
│   └── SemigroupVersion.lean
├── blueprint/                           # leanblueprint sources
├── docs/superpowers/specs/              # this document; the implementation plan
└── .github/workflows/ci.yml             # lean-action build; blueprint build/deploy
```

## 6. Process and infrastructure

- **Scaffold**: `lake` project depending on Mathlib (current stable), toolchain pinned to Mathlib's choice (elan auto-switches), `lake exe cache get` for prebuilt oleans. Git from day one; the repo can be pushed to GitHub whenever the user wants (CI activates then).
- **Blueprint-driven development** (`leanblueprint`): for each milestone, the LaTeX chapter (definitions, statements, informal proofs, `\lean{}` / `\leanok` annotations) is written *before* the Lean. The dependency graph is the progress dashboard. This is the learning loop: informal proof through your hands first, then formalize.
- **Sanity-check discipline** (the formalization analogue of TDD): a definition is not "done" until concrete examples witness it behaving correctly — e.g. `flipFlop` has exactly 3 elements; `x ⊳ (reset x₀) = x₀`; the wreath of two flip-flops has 36 monoid elements (`decide`/`rfl`/`Fintype.card` computations); `regular (ZMod 3)` is faithful. Wrong-but-consistent definitions are the main way formalizations lose months; examples catch them at birth.
- **CI**: GitHub Actions with `lean-action` (build + Mathlib cache). A final job checks the axiom certificate: `#print axioms` of the three main theorems must contain at most `Classical.choice`, `propext`, `Quot.sound`. Sorries allowed on feature branches, never on `main` past their milestone.
- **Workflow**: milestone-by-milestone; each milestone = blueprint chapter → Lean skeleton with `sorry`-stubs and examples → proofs → review → commit. Superpowers process skills (TDD-analogue above, verification-before-completion, code review) apply.

## 7. Roadmap (v1 milestones)

| # | Milestone | Contents | Acceptance |
|---|---|---|---|
| 0 | Scaffold | lake + Mathlib + git + CI + blueprint skeleton | `lake build` green; blueprint compiles |
| 1 | TransMon core | `Basic.lean` | examples pass; `regular_faithful` proved |
| 2 | Division | `Division.lean` | preorders + glue lemma proved |
| 3 | Wreath | `Wreath.lean` | monoid instance, monotonicity, `wreath_assoc_div`, `wreathList_append` |
| 4 | Bar + resets | `Bar.lean`, `Reset.lean` | [DKS] 2.12 proved |
| 5 | Local divisor | `FiniteMonoid.lean`, `LocalDivisor.lean` | 2.13 + card-lt + divides proved |
| 6 | Group case | `GroupCase.lean` | `group_bar_div` + `transfGroup_div_wreath_simples` |
| 7 | **Theorem 3.1** | `Decomposition.lean` (blueprint chapter first) | `decomposition` proved |
| 8 | Main induction | `KrohnRhodes.lean` | `krohnRhodes`, `krohnRhodes_monoid` |
| 9 | Semigroup + polish | `SemigroupVersion.lean`, blueprint completion | all of §1 done; axiom certificate |

Milestones 4, 5, 6 are mutually independent and may be reordered. Estimated total: 4–6k lines of Lean, a few months of steady part-time work. Milestone 7 is the concentrated difficulty; everything before it is shaping the terrain so that fight is fair.

## 8. Risks and open points

| Risk / open point | Mitigation |
|---|---|
| [DKS] Thm 3.1 proof internals not yet transcribed (only the statement is pinned) | First task of milestone 7 is a lemma-level blueprint chapter of [DKS] §3; no Lean for it before that exists |
| Mathlib Jordan–Hölder framework may not fit our composition-series existence need | Survey first; fallback is a ~50-line direct induction (existence only, no uniqueness) |
| Degenerate cases (`|X| ≤ 1`, trivial M) may break faithfulness side conditions | Dedicated audit task in milestone 4; keep bars on the left of ≺ |
| Notation clashes (`≀`, `≺`) with Mathlib | All notation scoped; checked at milestone 1 |
| Well-definedness plumbing in `localDivisor` (`Classical.choose`) may be brittle | Isolate in dedicated `choose`-independence lemmas; API never exposes the choice |
| `wreath_div_wreath` needs sections of surjections (choice) | Fine classically; noted so nobody expects computability there |
| Bundled-structure instance friction (`attribute [instance]` fields) | Standard Mathlib pattern (`Bundled`); milestone 1 validates early |

## 9. Future ideas ledger (post-v1)

- **Aperiodic corollary** (v2 candidate): M aperiodic ↔ M divides an iterated wreath of flip-flops. Needs: aperiodicity, closure under division and wreath products. Bridge toward Schützenberger/star-free languages.
- **Automata cascade version**: bridge to `Mathlib.Computability.DFA`; cascade product of automata; "every DFA is covered by a cascade of permutation-reset automata".
- **Holonomy decomposition** (Eilenberg/Zeiger); computational flavor à la SgpDec.
- **Size bounds**: [DKS] Cor. 4.3.
- **Green's relations** as standalone Mathlib-grade infrastructure.
- **Upstreaming plan**: `FiniteMonoid.lean` lemmas and a monoid-level wreath product are natural first Mathlib PRs; `TransMon` itself could follow Mathlib's automata section conventions.
- **Paper**: an ITP/CPP experience report if v1 completes (apparently first-ever formalization).

## 10. References

- [DKS] Diekert, Kufleitner, Steinberg, *The Krohn-Rhodes Theorem and Local Divisors*, Fund. Inform. 116 (2012). arXiv:1111.1585 — the blueprint text.
- Diekert, Kufleitner, *A Survey on the Local Divisor Technique*, arXiv:1410.6026 — secondary exposition.
- Krohn, Rhodes, *Algebraic theory of machines I*, Trans. AMS 116 (1965) — historical statement.
- Eilenberg, *Automata, Languages, and Machines*, Vol. B — holonomy route (future).
- Mathlib: `Mathlib.GroupTheory.RegularWreathProduct` (`≀ᵣ`, groups only), `Mathlib.Computability.DFA` (design precedent for raw actions), `WithOne`, `Submonoid`, `Con`.
