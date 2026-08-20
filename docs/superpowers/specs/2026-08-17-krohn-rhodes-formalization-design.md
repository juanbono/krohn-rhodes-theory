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
5. CI builds the project and the blueprint — including the `leanblueprint` web build — and the dependency graph is fully green. (Publishing that site to GitHub Pages is deliberately out of v1 scope: it is a publication decision, not a correctness one.)

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
- **Semigroup division** `S ≺ₛ T` (only in `SemigroupVersion.lean`): subsemigroup + surjective semigroup hom. Feeder: `M ≺ₘ N → M ≺ₛ N`. (2026-08-19: transitivity must prove `MulHom`-level comap surjectivity inline — Mathlib has `submonoidComap_surjective_of_surjective` but no `Subsemigroup` analogue; upstreaming candidate, §9.)

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

- `WreathMonoid` (fresh structure; see §4.3) with the multiplication above (associativity is a direct computation).
- `StrongDivides.wreath` (monotonicity): `S₁ ≺ T₁ → S₂ ≺ T₂ → S₁ ≀ S₂ ≺ T₁ ≀ T₂`. Proof note: the front component needs functions constant on φ₂-fibers and a choice of section of φ₂; this is the standard proof, mildly fiddly.
- `wreath_assoc_div`: `(P ≀ Q) ≀ R ≺ P ≀ (Q ≀ R)`. The underlying map is currying; expected to be an isomorphism, but only the division direction is needed.
- `trivial_wreath_div` / `div_wreath_trivial`: absorption of `trivialTM` up to division.
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

**Implementation note (M4):** the Lean carrier is a fresh inductive `BarMonoid T` (constructors `of`/`reset`), not raw `M ⊕ X` — same diamond-avoidance rationale as the wreath monoid's fresh structure (§4.3).

Lemmas: monoid instance (case bash), action instance, `bar_divides : T ≺ T̄`, and monotonicity `S ≺ T → S̄ ≺ T̄` if the induction turns out to need it (flagged, not assumed).

**Implementation note (M4):** `bar_mono` is confirmed *not* needed — the Krohn–Rhodes induction's bars ride on the induction hypothesis's own output (`Q(T)` already delivers `T̄ ≺ …` directly), so it is recorded here but not built (YAGNI).

Degenerate-case audit (implementation task): `|X| ≤ 1` makes resets collide with the identity; faithfulness claims about T̄ must be checked there. All main-line uses keep bars on the *left* of ≺, where this is harmless.

### 3.5 Reset monoids and the flip-flop

`U(X) := (X, resets + identity)`. Implementation: monoid carrier `Option X` — `none` = identity, `some x` = reset to x, multiplication `a * b = if b = none then a else b`.

**Implementation note (M4):** the Lean carrier is a fresh inductive `Resets X` (constructors `id`/`to`), not raw `Option X` — avoids planting a global `Monoid (Option _)` instance on a ubiquitous type.

The **flip-flop** is `flipFlop := U(Bool)`: 2 states, 3 elements — identity plus two resets. This is the unique non-group prime of the theory.

- ([DKS] 2.12) `reset_div_flipFlops`: for finite X, `U(X)` divides an iterated wreath product of flip-flops. Proof: induction on |X| (split X into two blocks; one flip-flop selects the block, smaller reset monoids act inside).
- **Implementation note (M4):** the formal statement requires **`[Nonempty X]`** — an empty-state transformation monoid strongly divides only empty-state ones (no function into `∅`), so `U(∅)` divides no flip-flop wreath; [DKS] assume nonempty state sets implicitly. The statement is also existential in the factor count: `∃ n, resetMonoid X ≺ wreathList (List.replicate n flipFlop)` (Krohn–Rhodes only needs existence).
- Note `U(X)` is reset-closed: `U(X)̄` adds nothing new (up to division), so no bars are needed on flip-flop factors.

### 3.6 Local divisors

For c ∈ M ([DKS] §2.5): carrier `Mc := cM ∩ Mc`, multiplication `mc ∘ cn := mcn`, identity c. Well-definedness: if `u = mc = m′c` and `v = cn`, then `u ∘ v = m*v = m′*v`; in Lean, define `u ∘ v := Classical.choose (u ∈ Mc) * v` and prove independence of the choice.

The local divisor acts on `Xc := { x·c | x ∈ X }` by `ξ ∘ (cm) := ξ · m` (well-defined, lands in Xc).

Three lemmas, all load-bearing:

1. `localDivisor_faithful` ([DKS] 2.13): (X, M) faithful → (Xc, Mc) faithful.
2. `localDivisor_card_lt`: c **not a unit** → `|Mc| < |M|`. Proof: `Mc ⊆ cM ⊆ M`; if equality held then `1 ∈ cM`, making c right-invertible, hence (finite monoid, §3.0 prelims) a unit.
3. `localDivisor_divides : Mc ≺ₘ M`. Proof: `N := {m | c*m ∈ Mc}` is a submonoid of M and `m ↦ c*m` is a surjective monoid hom N ↠ Mc. **This is what makes the strong form survive recursion** — simple groups produced inside Mc divide Mc, hence divide M by transitivity.

Prelims needed (`FiniteMonoid.lean`): in a finite monoid, an element with a one-sided inverse is a unit; every element has an idempotent power (pigeonhole). (2026-08-18: the idempotent-power lemma turned out unused by [DKS] §3's proof — its consumer is the v2 aperiodic corollary (§9); M8 planning confirmed the induction has no use for it.)

### 3.7 The group case

Base case of the induction: M = G a finite group.

- Composition-series existence is FUSED into the induction (amended 2026-08-18 during M6 planning): Mathlib has no `JordanHolderLattice (Subgroup G)` instantiation, its framework covers uniqueness (a §2 non-goal) rather than existence, and the only consumer is the induction below — which instead peels one maximal proper normal subgroup per step (prelims: `exists_maximal_normal_subgroup`, `isSimpleGroup_quotient`). No standalone series artifact.
- `kaloujnine_krasner_div`: for N ⊴ G, `regular G ≺ regular N ≀ regular (G ⧸ N)`. Uses a classical section of the quotient map; equivariance is the classical Kaloujnine–Krasner computation.
- `transfGroup_div_wreath_simples`: chaining Kaloujnine–Krasner along the fused strong induction on |G| (glued by `StrongDivides.wreath` and `wreathList_append`): `regular G ≺ wreathList` of `regular Gᵢ` with each Gᵢ simple and `Gᵢ ≺ₘ G` (each Gᵢ is a quotient of a subgroup of G).
- ([DKS] 2.11) `group_bar_div`: `(X, G)̄ ≺ (X, U(X)) ≀ (G, G)` for a transformation group (X, G) — faithfulness is NOT required (amended 2026-08-18; see the strengthened bullet below — [DKS] carry a standing faithfulness assumption their construction does not use here). Note the right factor is the *regular* (G, G) even when X ≠ G.
- **Encoding (amended 2026-08-18):** a "transformation group" is a `TransMon` `T` with the Prop `∀ m : T.M, IsUnit m` — a `[Group T.M]` instance would diamond with the bundled `monoidM`. This Prop is exactly the M8 branch predicate (group case vs `¬IsUnit c`). Abstract-group statements quantify `[Group G] [Finite G]` and use `regular G`.
- **`group_bar_div` needs neither faithfulness nor nonempty states** (amended 2026-08-18): the covering construction uses only `∀ m, IsUnit m`; statement `T.bar ≺ resetMonoid T.X ≀ regular T.M`.
- Factors are carried as `BundledFinGroup` (carrier + `[Group]` + `[Finite]`), introduced in `GroupCase.lean` (moved early from `KrohnRhodes.lean`; M8's `KRPrime.grp` reuses it).

Combined group case: `(X,G)̄ ≺ flip-flops ≀ simple group factors`, all groups dividing G.

### 3.8 The main decomposition ([DKS] Thm 3.1)

If (X, M) is faithful, M is generated by N ∪ {c} where N ≤ M is a submonoid and c is **not a unit**, then

```
(X, M)̄  ≺  (X·c, Mc)̄  ≀  (X ⊔ N, N)̄
```

The right factor's state space is X ⊔ N with N acting on X by restriction and on N by right multiplication; the disjoint union with the regular part is exactly what keeps the right factor **faithful**, so the induction hypothesis applies to it.

**Resolved 2026-08-18 (M7 planning; transcribed from [DKS] §3 with one strengthening).** The Lean statement:

```lean
theorem decomposition (T : TransMon) (hT : T.Faithful) (N : Submonoid T.M)
    (c : T.M) (hc : ¬ IsUnit c)
    (hgen : Submonoid.closure (↑N ∪ {c}) = ⊤) :
    T.bar ≺ (localDivisor T c).bar ≀ (rightFactor T N).bar
```

with `rightFactor T N` the transformation monoid on states `T.X ⊕ ↥N`, monoid `↥N` (restriction on the left summand, right multiplication on the right — the regular part makes it faithful). `Nonempty T.X` is derived from `hT` + `hc`, not assumed. State map: `(p, inl x) ↦ x`, `(p, inr n) ↦ p·n`. Generator covers, verbatim from [DKS] §3 except the marked choice: `of n ↦ (const 1, of n)`; `of c ↦ (f_c, reset (inr 1))` with `f_c (inl x) = reset ⟨x·c⟩` and `f_c (inr n) = of ⟨c·n·c⟩`; `reset x ↦ (const (reset ⟨x·c⟩), reset (inl x))` — **[DKS] leave this front arbitrary; we choose a reset**. That choice matters because our syntactic bar (M4) is unfaithful whenever `M` has constant-acting elements (`of m` vs `reset x₀` act equally), so [DKS]'s Prop 2.3.2 (hom-from-covers via faithfulness of the covered object) does not apply. Repair: "front is `of`-shaped at `inr 1`" is a multiplicative tag separating reset-containing products from `a`/`c`-only products; the covered element is unique within each tag class ((X,M)-faithfulness for `of`s, target-determination for resets), and ψ selects the tag-matching covered element (classical choice, quarantined). The covering submonoid is the closure of the three cover families; the invariants (`ShapeOK`) and the uniqueness lemma are recorded in blueprint `ch:decomposition`.

### 3.9 The induction and the main theorems

**Induction predicate**, for faithful finite T = (X, M):

> Q(T): there is a list L of factors, each either `flipFlop` or `regular G` with G a nontrivial finite simple group and `G ≺ₘ M`, such that `T̄ ≺ wreathList L`.

**Claim: Q holds for all faithful finite T with nonempty states**, by strong induction on (|M|, |X|) lexicographically. (Nonemptiness is preserved by the recursion — X·c is nonempty when X is, and X ⊔ N always is — and is exactly what M8 needs: `krohnRhodes` carries `[Nonempty T.X]` per the note below; the empty-state faithful T has a trivial monoid and is excluded.)

**Note (2026-08-18, M8 planning):** the formal induction is plain strong induction on |M| — both recursive calls strictly shrink |M| (3.6.2 for Mc; proper-submonoid counting for N) and the group case recurses no further (its induction was fused into §3.7's `transfGroup_div_wreath_simples` at M6), so the lex second component is never exercised. The state-set growth X ⊔ N remains the reason no |X|-leading measure could work.

- **M a group**: §3.7 gives Q directly (groups produced are subquotients of G, dividing G; flip-flops from §3.5).
- **M not a group**: pick a minimal generating set A of M; some c ∈ A is not a unit (otherwise the units form a submonoid containing A, forcing M to be a group — prelim lemma). Let N := ⟨A ∖ {c}⟩; minimality gives c ∉ N, so N is proper: |N| < |M|. Apply Thm 3.1:
  `T̄ ≺ (X·c, Mc)̄ ≀ (X ⊔ N, N)̄`.
  - (X·c, Mc) is faithful (3.6.1) and |Mc| < |M| (3.6.2) → IH gives Q(X·c, Mc); its groups divide Mc ≺ₘ M (3.6.3), hence divide M.
  - (X ⊔ N, N) is faithful (regular part) and |N| < |M| (state space grew — this is why the measure is lex with |M| first) → IH gives Q(X ⊔ N, N); its groups divide N ≤ M, hence divide M.
  - Glue with `StrongDivides.wreath`, `wreathList_append`, transitivity.

**Main theorems** (target signatures, provisional syntax):

```lean
/-- Krohn–Rhodes, transformation form, strong version. -/
theorem krohnRhodes (T : TransMon) (hT : T.Faithful) [Nonempty T.X] :
    ∃ L : List KRPrime,
      T ≺ wreathList (L.map KRPrime.toTransMon) ∧
      ∀ p ∈ L, ∀ G, p = .grp G → IsSimpleGroup G.carrier ∧ G.carrier ≺ₘ T.M

/-- Abstract finite monoid form (via the regular representation). -/
theorem krohnRhodes_monoid (M : Type) [Monoid M] [Finite M] :
    ∃ L : List KRPrime, M ≺ₘ (wreathList (L.map KRPrime.toTransMon)).M ∧
      ∀ p ∈ L, ∀ G, p = .grp G → IsSimpleGroup G.carrier ∧ G.carrier ≺ₘ M

/-- Classical 1965 semigroup form (via WithOne S = S¹). -/
theorem krohnRhodes_semigroup (S : Type) [Semigroup S] [Finite S] :
    ∃ L : List KRPrime, S ≺ₛ (wreathList (L.map KRPrime.toTransMon)).M ∧
      ∀ p ∈ L, ∀ G, p = .grp G → IsSimpleGroup G.carrier ∧ G.carrier ≺ₛ S
```

**Note (2026-08-18, from the M6 final review):** `[Nonempty T.X]` is necessary — the empty-state faithful transformation monoid divides no `wreathList` of KRPrime factors (their state spaces are all nonempty); `krohnRhodes_monoid` is unaffected (regular states contain 1).

(The factor condition is the same in all three. **Resolved 2026-08-19 (M9):** the strong phrasing `G ≺ₛ S` is what we prove — the signature above stands unweakened. From `G ≺ₘ S¹` the `S`-elements of the covering submonoid form a subsemigroup that covers every `g ≠ 1`, and `1 = h · h⁻¹` for any `h ≠ 1`; nontriviality of the factor is load-bearing and comes free from `IsSimpleGroup`.)

Here `KRPrime` is a small inductive — `flipflop | grp (G : BundledFinGroup)` — with `toTransMon` sending `flipflop` to the canonical flip-flop and `grp G` to `regular G`. Making the list contain *canonical objects* (rather than "some F isomorphic to a flip-flop") keeps the statement tight without needing a TransMon-isomorphism API in v1. `T ≺ T̄` (3.4) removes the bar from the final statements.

For `krohnRhodes_semigroup`: S ≺ₛ S¹ = `WithOne S` (Mathlib), apply the monoid form, transfer along `M ≺ₘ N → M ≺ₛ N` and transitivity of ≺ₛ.

## 4. Lean architecture

### 4.1 The core structure (approved)

```lean
structure TransMon : Type 1 where
  X : Type
  M : Type
  [finiteX : Finite X]
  [monoidM : Monoid M]
  [finiteM : Finite M]
  act : X → M → X
  act_one : ∀ x, act x 1 = x
  act_mul : ∀ x m n, act x (m * n) = act (act x m) n
```

**Decision record — why this shape:**

- **Bundled**, because the theorem quantifies over a `List` of transformation monoids and constructions (`≀`, bar, local divisor) are functions `TransMon → … → TransMon`. Unbundled carriers cannot form lists.
- **Raw right action** (not `MulAction Mᵐᵒᵖ X`, not a left action): formulas match [DKS] symbol-for-symbol, proof states stay free of `op/unop` noise, and this matches Mathlib's own `DFA.step : σ → α → σ` design. Cost accepted: a self-written ~30-line action lemma kit. Adapters to Mathlib's `MulAction` can be derived later if ever needed; the reverse retrofit would not be possible.
- Carriers in `Type` (no universe polymorphism): everything is finite; `Type 1` structure, `List TransMon` works.
- **Finiteness is bundled as `Finite` (Prop), not `Fintype` (data).** *Amended 2026-08-17 during M5 planning, superseding the original `Fintype`-field choice, on milestone-4 evidence:* `Fintype {x // P x}` demands `DecidablePred P`, which forced `reset_split` into a classically-decorated statement repaired at each call site by `convert` + `Subsingleton (Fintype _)`, and the local divisor's carriers (`cM ∩ Mc`, `X·c`) are subtypes twice over. `Finite` fields cost nothing classically (`Subtype.finite` needs no decidability), proof irrelevance makes instance mismatch impossible, and `wreath` stops being `noncomputable` (its only obstruction was filling a `Fintype` field for a function type). Cardinality is uniformly `Nat.card`. Fields registered as instances via `attribute [instance]` as before.
- `DecidableEq` is **not** bundled; proofs use classical decidability locally (`open scoped Classical` or `Classical.dec`), while concrete examples (`Bool`, `Fin n`, `Option _`) remain computable through their native instances. Note (post-amendment): examples stated at projected types such as `(regular (ZMod 3)).X` use `Nat.card`, since instance search will not unfold the semireducible projection to reach native `Fintype` data.
- `Faithful` is a `Prop`-valued predicate (likely a class) on `TransMon`, not a field: the bar and wreath constructions do not preserve it uniformly, and non-faithful objects appear naturally mid-proof.

### 4.2 Conventions

- Right-action notation: scoped infix, provisionally `x ⊳ m`; division `S ≺ T` (strong), `M ≺ₘ N` (monoid), `S ≺ₛ T` (semigroup); wreath `S ≀ T`. Check for notation clashes with Mathlib at implementation time (Mathlib uses `≀ᵣ` for `RegularWreathProduct`; plain `≀` believed free). All notations scoped to a `KRTheory` namespace.
- Naming follows Mathlib conventions (`camelCase` defs, `snake_case` theorems, `Div`/`div` spelled out as `divides` to avoid clash with `Div` the typeclass).
- Every definitional file ends with `example`-based sanity checks on concrete instances (see §6).
- File-level docstrings state the [DKS] reference for each result.

### 4.3 API map (file → key declarations)

| File | Declarations |
|---|---|
| `FiniteMonoid.lean` | `exists_pow_idempotent`, `isUnit_of_mul_eq_one_right/left` (finite), `isUnit_of_generators_units` (units-only generating set ⇒ group), `card_submonoid_lt_of_ne_top`, `exists_gen_nonunit` (minimal-generating-set split) |
| `TransMon/Basic.lean` | `TransMon`, action notation + lemma kit, `Faithful`, `trivialTM`, `regular`, `regular_faithful`, examples |
| `TransMon/Division.lean` | `MonoidDivides` (`≺ₘ`), `StrongDivides` (`≺`), both preorders, `strongDivides.monoidDivides` (glue), submonoid/quotient feeders, `Covering.extMap` kit (added in M3) |
| `TransMon/Wreath.lean` | `WreathMonoid` + monoid instance & simp kit, `wreath` (`≀`) + action, `WreathMonoid.natCard`, `wreathList` |
| `TransMon/WreathDivision.lean` | `trivialTM` absorption (`trivial_wreath_div`, `div_wreath_trivial`), `Covering.wreath` / `StrongDivides.wreath` (monotonicity), `wreath_assoc_div`, `wreathList_append` |
| `TransMon/Bar.lean` | `BarMonoid` (fresh inductive; `of`/`reset`), `bar`, `BarMonoid.ofHom`, `bar_divides : T ≺ T.bar` (`bar_mono` confirmed unneeded, not built) |
| `TransMon/Reset.lean` | `Resets` (fresh inductive; `id`/`to`), `resetMonoid` (= `U(X)`), `flipFlop`, `reset_split`, `reset_div_flipFlops` ([DKS] 2.12) |
| `TransMon/LocalDivisor.lean` | `localDivisor`, monoid/action instances, `localDivisor_faithful` (2.13), `localDivisor_card_lt`, `localDivisor_divides`, `localDivisor_X_nonempty` |
| `GroupCase.lean` | `BundledFinGroup`, `exists_maximal_normal_subgroup`, `isSimpleGroup_quotient`, `subgroup_monoidDivides`, `quotient_monoidDivides`, `card_subgroup_lt_of_ne_top`, `regular_div_trivialTM_of_subsingleton`, `kaloujnine_krasner_div`, `transfGroup_div_wreath_simples`, `group_bar_div` (2.11) |
| `Decomposition.lean` | `rightFactor` + faithfulness, `nonempty_of_not_isUnit`, `barMonoid_closure`, `decompState`, `coverN`/`coverC`/`coverReset` (+ `cnc`), `CoversAt` kit, `decompSub`, `decompMap`, `coversAt_unique`, `decomposition` ([DKS] Thm 3.1) |
| `KrohnRhodes.lean` | `KRPrime` (consuming `GroupCase.BundledFinGroup`), `KRPrime.toTransMon` (+ simp equation lemmas), `krohnRhodes_bar_of_units` (group branch), `krohnRhodes_bar` (the induction), `krohnRhodes`, `krohnRhodes_monoid` |
| `SemigroupVersion.lean` | `SemigroupDivides` (`≺ₛ`) + `refl`/`of_subsemigroup`/`trans`, `monoidDivides_semigroupDivides` (feeder), `withOne_transfer`, `semigroupDivides_of_monoidDivides_withOne` (factor transport), `krohnRhodes_semigroup` |

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

- **Scaffold**: `lake` project depending on Mathlib (current stable), toolchain pinned to Mathlib's choice (elan auto-switches), `lake exe cache get` for prebuilt oleans. Git from day one; remote `github.com/juanbono/krohn-rhodes-theory` added 2026-08-17 — publishing (push, fast-forward `main`, CI activation, axiom-certificate and blueprint jobs) is a milestone-5 task.
- **Blueprint-driven development** (`leanblueprint`): for each milestone, the LaTeX chapter (definitions, statements, informal proofs, `\lean{}` / `\leanok` annotations) is written *before* the Lean. The dependency graph is the progress dashboard. This is the learning loop: informal proof through your hands first, then formalize.
- **Sanity-check discipline** (the formalization analogue of TDD): a definition is not "done" until concrete examples witness it behaving correctly — e.g. `flipFlop` has exactly 3 elements; `x ⊳ (reset x₀) = x₀`; the wreath of two flip-flops has 27 (3² · 3) monoid elements (`decide`/`rfl`/`Nat.card` computations bridged to native instances); `regular (ZMod 3)` is faithful. Wrong-but-consistent definitions are the main way formalizations lose months; examples catch them at birth.
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
| 5 | Local divisor | `Finite` bundling swap (§4.1 amendment); repo publish + CI certificate/blueprint jobs; `FiniteMonoid.lean`, `LocalDivisor.lean` | 2.13 + card-lt + divides proved; CI green on published repo |
| 6 | Group case | `GroupCase.lean` | `group_bar_div` + `transfGroup_div_wreath_simples` |
| 7 | **Theorem 3.1** | `Decomposition.lean` (blueprint chapter first) | `decomposition` proved |
| 8 | Main induction | `KrohnRhodes.lean` | `krohnRhodes`, `krohnRhodes_monoid` |
| 9 | Semigroup + polish | `SemigroupVersion.lean`, blueprint completion | all of §1 done; axiom certificate |

Milestones 4, 5, 6 are mutually independent and may be reordered. Estimated total: 4–6k lines of Lean, a few months of steady part-time work. Milestone 7 is the concentrated difficulty; everything before it is shaping the terrain so that fight is fair.

## 8. Risks and open points

| Risk / open point | Mitigation |
|---|---|
| Thm 3.1's ψ-selection over the syntactic bar (resolved 2026-08-18: tag-based selection; see §3.8) | The ShapeOK invariant list carries refinement latitude during M7 GREEN, controller-ruled |
| Mathlib Jordan–Hölder framework may not fit our composition-series existence need | Survey first; fallback is a ~50-line direct induction (existence only, no uniqueness) |
| Degenerate cases (`|X| ≤ 1`, trivial M) may break faithfulness side conditions | Dedicated audit task in milestone 4; keep bars on the left of ≺ |
| Notation clashes (`≀`, `≺`) with Mathlib | All notation scoped; checked at milestone 1 |
| M8's group branch needs `Group T.M` from `∀ m, IsUnit m` (RESOLVED 2026-08-18, M8 planning) | Mathlib's `groupOfIsUnit` already extends the ambient instance (`{ hM with … }`); `regular T.M` defeq-stability across it probe-verified |
| Well-definedness plumbing in `localDivisor` (`Classical.choose`) may be brittle | Isolate in dedicated `choose`-independence lemmas; API never exposes the choice |
| `StrongDivides.wreath` needs sections of surjections (choice) | Fine classically; noted so nobody expects computability there |
| The `Fintype`→`Finite` swap (§4.1 amendment) may surface semireducible-projection elaboration surprises | Dedicated early M5 task with known adjustment sites enumerated in the plan; acceptance = green build + unchanged axiom certificate before any local-divisor work builds on it |
| Bundled-structure instance friction (`attribute [instance]` fields) | Standard Mathlib pattern (`Bundled`); milestone 1 validates early |

## 9. Future ideas ledger (post-v1)

- **Aperiodic corollary** (v2 candidate): M aperiodic ↔ M divides an iterated wreath of flip-flops. Needs: aperiodicity, closure under division and wreath products. Bridge toward Schützenberger/star-free languages.
- **Automata cascade version**: bridge to `Mathlib.Computability.DFA`; cascade product of automata; "every DFA is covered by a cascade of permutation-reset automata".
- **Holonomy decomposition** (Eilenberg/Zeiger); computational flavor à la SgpDec.
- **Size bounds**: [DKS] Cor. 4.3.
- **Green's relations** as standalone Mathlib-grade infrastructure.
- **Upstreaming plan**: `FiniteMonoid.lean` lemmas and a monoid-level wreath product are natural first Mathlib PRs; `TransMon` itself could follow Mathlib's automata section conventions. Also: a `MulHom`/`Subsemigroup` analogue of `submonoidComap_surjective_of_surjective`, which M9 had to prove inline.
- **Paper**: an ITP/CPP experience report if v1 completes (apparently first-ever formalization).

## 10. References

- [DKS] Diekert, Kufleitner, Steinberg, *The Krohn-Rhodes Theorem and Local Divisors*, Fund. Inform. 116 (2012). arXiv:1111.1585 — the blueprint text.
- Diekert, Kufleitner, *A Survey on the Local Divisor Technique*, arXiv:1410.6026 — secondary exposition.
- Krohn, Rhodes, *Algebraic theory of machines I*, Trans. AMS 116 (1965) — historical statement.
- Eilenberg, *Automata, Languages, and Machines*, Vol. B — holonomy route (future).
- Mathlib: `Mathlib.GroupTheory.RegularWreathProduct` (`≀ᵣ`, groups only), `Mathlib.Computability.DFA` (design precedent for raw actions), `WithOne`, `Submonoid`, `Con`.
