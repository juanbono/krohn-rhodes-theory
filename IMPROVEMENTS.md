# Review: soundness audit and improvement backlog

**Date:** 2026-08-19 (P1, P2 applied 2026-08-20)
**Scope:** all 12 modules under `KRTheory/`, `scripts/AxiomCertificate.lean`,
`.github/workflows/ci.yml`, `lakefile.toml`.
**Build state at review:** `lake build` green (3,028 jobs), axiom certificate
green (19/19).

> **Status:** **P1 and P2 are DONE** — applied and verified; see the notes at
> the head of each. P3–P9 remain open. Certificate is now 22/22.

---

## Part 1 — Soundness audit

### Verdict

**No vacuous theorems. No axioms that should not be there.**

Every hypothesis tuple in the repository is satisfiable, every definition
matches [DKS], and the axiom certificate is clean. Details and the evidence
behind each claim follow.

### Axioms

`lake env lean scripts/AxiomCertificate.lean` — 19 lines, every one within
`{propext, Classical.choice, Quot.sound}`:

| Check | Result |
|---|---|
| Stray `axiom` declarations | none |
| `sorry` / `admit` / `sorryAx` | none |
| `native_decide` | none |
| `unsafe` / `partial` / `@[implemented_by]` / `@[extern]` | none |
| `opaque` declarations | none (the three grep hits are prose in comments) |
| Theorems depending on non-standard axioms | none |

`regular_faithful` depends on *no* axioms at all. `StrongDivides.trans` and
`localDivisor_divides` each use only two of the three, which is a mild positive
signal — a proof that had quietly routed through choice everywhere would show
all three uniformly.

### Vacuity

The failure mode worth worrying about in a formalization is not an unsound
proof — it is a *true but empty* one: a theorem whose hypotheses cannot be
satisfied, or whose conclusion is trivially satisfiable because a definition is
weaker than its name suggests. Both were checked.

**Hypotheses are satisfiable.** The two headline corollaries settle this
outright: `krohnRhodes_monoid` assumes only `[Monoid M] [Finite M]` and
`krohnRhodes_semigroup` only `[Semigroup S] [Finite S]`, so they apply to every
finite monoid and semigroup respectively. The repo instantiates both on concrete
carriers (`ZMod 2`, `ZMod 6`, and a genuine non-monoid `LeftZero`). For
`krohnRhodes` itself, `T.Faithful` and `Nonempty T.X` are jointly witnessed by
`regular M`. For `decomposition` — the theorem with the most restrictive
hypothesis tuple (`Faithful`, `¬IsUnit c`, `closure (↑N ∪ {c}) = ⊤`) —
`exists_gen_nonunit` produces exactly that tuple for any finite monoid that is
not a group, so it is satisfiable by construction.

**Definitions are not secretly trivial.** Each was read against [DKS]:

- `MonoidDivides` requires a *surjective* hom from a submonoid — not merely a
  hom. `Covering` requires *both* `stateMap_surj` and `monoidMap_surj` plus
  `equivariant`. Neither is accidentally always-satisfiable.
- `Faithful` is the real separation condition, not a tautology.
- The wreath multiplication is correctly twisted, and `Wreath.lean:98-101`
  carries an example that *kills both* the untwisted componentwise product and
  the wrong-sided twist. This is the single best-designed check in the repo.
- `BarMonoid`, `Resets`, `flipFlop`, and `localDivisor` all match [DKS]
  symbol-for-symbol, including the left-factor-acts-first convention.
- `IsSimpleGroup` extends `Nontrivial` in Mathlib, so the group factors cannot
  degenerate to the trivial group. The spec correctly identifies this as
  load-bearing.
- `BundledFinGroup` registers its fields with `attribute [instance]`, so
  `IsSimpleGroup G.carrier` and `regular G.carrier` resolve to the *bundled*
  instances — no silent instance mismatch.

**One trap correctly avoided.** `coversAt_unique` (`Decomposition.lean`) reasons
by "the two candidates act identically on all states". Had `T.X` been empty that
argument would be vacuous and the reset case unprovable — the proof instead
*derives* `Nonempty T.X` via `nonempty_of_not_isUnit` rather than assuming it.
This is exactly where a vacuity bug would have hidden, and it is handled.

### The one real gap: nothing proves `≺` can *fail*

Every division sanity check in the repository is **positive** — `refl`, `trans`,
`monoidDivides`, and applications of the main theorem. Nothing anywhere
demonstrates that `≺` or `≺ₘ` is *ever false*.

This is not a bug; the definitions are correct. It is a gap in the
*defence in depth*. Had a surjectivity field been dropped from `Covering` at some
point, `≺` would have become near-trivial, `krohnRhodes` would have become nearly
content-free — and **every single existing check would still pass**. The repo's
own stated discipline ("a definition is not done until concrete examples witness
it behaving correctly", spec §6) is applied only in the affirmative direction.

Closing this is cheap. See P1 below.

---

## Part 2 — Improvements

Ordered by value. Items marked **verified** were compiled against this
repository before being written down; items marked *proposed* were not.

### P1 — Add non-vacuity witnesses for division — ✅ **DONE**

> **Applied 2026-08-20.** `MonoidDivides.card_le` and `StrongDivides.card_le` /
> `card_X_le` are in `Division.lean`, with the two negative sanity checks at the
> foot of that file; `flipFlop_not_group` is in `Reset.lean`; the
> factor-list-non-empty check is in `KrohnRhodes.lean`. All three new named
> theorems are in `scripts/AxiomCertificate.lean` (now 22 entries, CI count
> bumped). `lake build` green, all changed files elaborate with zero warnings,
> and `flipFlop_not_group` turns out to need only `propext`.

*Why:* closes the gap above. Three short lemmas turn "the definitions look
right" into "the definitions are mechanically proved to be non-trivial", and
they are useful API in their own right.

Compiles against `KRTheory.TransMon.Division`'s existing imports with no
additions — verified by compilation:

```lean
theorem MonoidDivides.card_le {M N : Type} [Monoid M] [Monoid N] [Finite N]
    (h : M ≺ₘ N) : Nat.card M ≤ Nat.card N := by
  obtain ⟨N', ψ, hψ⟩ := h
  exact le_trans (Nat.card_le_card_of_surjective ψ hψ)
    (Nat.card_le_card_of_injective _ Subtype.val_injective)

theorem StrongDivides.card_le {S T : TransMon} (h : S ≺ T) :
    Nat.card S.M ≤ Nat.card T.M :=
  MonoidDivides.card_le h.monoidDivides

theorem StrongDivides.card_X_le {S T : TransMon} (h : S ≺ T) :
    Nat.card S.X ≤ Nat.card T.X := by
  obtain ⟨c⟩ := h
  exact Nat.card_le_card_of_surjective c.stateMap c.stateMap_surj
```

With those in place, the following negative sanity checks compile
(also verified):

```lean
-- `≺` is not the always-true relation
example : ¬ (regular (ZMod 3) ≺ trivialTM) := ...
-- `≺ₘ` is not the always-true relation
example : ¬ (ZMod 3 ≺ₘ PUnit) := ...
-- and the main theorem's factor list is not vacuously empty
example : ∀ (L : List KRPrime),
    regular (ZMod 3) ≺ wreathList (L.map KRPrime.toTransMon) → L ≠ [] := ...
```

The third is the one that matters most: it proves the existential in
`krohnRhodes` has real content for a nontrivial monoid, rather than being
satisfiable by `L = []`.

One further check in the same spirit, independent of the `card_le` lemmas and
also **verified** — that the flip-flop really is a *second* prime rather than
something the group branch could have absorbed:

```lean
/-- The flip-flop is genuinely NOT a group: `to true` has no inverse. -/
theorem flipFlop_not_group : ¬ (∀ m : Resets Bool, IsUnit m) := by
  intro h
  obtain ⟨u, hu⟩ := h (Resets.to true)
  have h1 : (u : Resets Bool) * (↑u⁻¹ : Resets Bool) = 1 := u.mul_inv
  rw [hu] at h1
  generalize (↑u⁻¹ : Resets Bool) = v at h1
  rcases v with _ | y
  · simp [Resets.one_def] at h1
  · simp [Resets.one_def] at h1
```

`Reset.lean` currently asserts in prose that the flip-flop is "the unique
non-group prime" but never proves the non-group half. This closes that, and it
is exactly the predicate (`∀ m, IsUnit m`) on which `krohnRhodes_bar` branches —
so it also documents that the induction's two branches are both reachable.

*Where:* the two `card_le` lemmas next to `StrongDivides.monoidDivides` in
`Division.lean`; the negative examples in the sanity-check block at the foot of
the same file, plus one in `KrohnRhodes.lean`.

*Follow-on:* add `MonoidDivides.card_le` and `StrongDivides.card_le` to
`scripts/AxiomCertificate.lean` so they are covered by the certificate too.

### P2 — Fix a latent inversion in the dependency-graph CI gate — ✅ **DONE**

> **Applied 2026-08-20.** `ci.yml` now materializes the offending fills into
> `$bad` and tests `-z "$bad"`, with the rationale recorded inline so the old
> form is not reintroduced. Verified in all three directions: all-green input
> passes (0), one bad fill fails (1), and the large all-bad input that the old
> gate wrongly *passed* now correctly fails (1).

*Severity: low today, but it silently disables a gate as the blueprint grows.*

`.github/workflows/ci.yml:73`:

```sh
set -o pipefail
...
! grep -oE 'fillcolor="#[0-9A-Fa-f]{6}"' "$DOT" | grep -qvE '"#(B0ECA3|1CAC78)"'
```

When a non-green fillcolor **is** present, `grep -q` exits immediately on the
first match. If the upstream `grep -oE` is still writing at that moment it dies
of `SIGPIPE` (status 141). Under `set -o pipefail` the pipeline status becomes
141, and the leading `!` turns that non-zero into **success** — so the gate
passes in exactly the case it exists to catch.

Reproduced directly:

```console
$ sh -c 'set -o pipefail; ! (printf "#BAD000\n" | grep -oE "#[0-9A-Fa-f]{6}" \
        | grep -qvE "#(B0ECA3|1CAC78)"); echo $?'
1        # small output: upstream finishes, gate correctly FAILS

$ sh -c 'set -o pipefail; ! (yes "#BAD000" | head -200000 | grep -oE "#[0-9A-Fa-f]{6}" \
        | grep -qvE "#(B0ECA3|1CAC78)"); echo $?'
0        # large output: SIGPIPE 141, "!" inverts it, gate PASSES despite bad fill
```

Dormant at today's size — the current graph has 64 nodes (~1.4 KB of matches),
which fits in the pipe buffer, so the upstream grep always completes first. It
flips once the match stream exceeds the pipe buffer (roughly a few thousand
nodes).

Fix — materialize the result instead of relying on pipeline status:

```sh
bad=$(grep -oE 'fillcolor="#[0-9A-Fa-f]{6}"' "$DOT" \
      | grep -vE '"#(B0ECA3|1CAC78)"' || true)
test -z "$bad"
```

*Credit: found by the `/code-review` pass; reproduced and confirmed here.*

### P3 — Pin Mathlib to a release, not `master` *[proposed]*

`lakefile.toml` currently says:

```toml
[[require]]
name = "mathlib"
rev = "master"
```

`lake-manifest.json` pins the concrete revision (`ac4c4bff`), so *today's*
builds are reproducible. But `rev = "master"` means any `lake update` silently
jumps to whatever Mathlib master happens to be, which will not generally match
the pinned `lean-toolchain` (`v4.34.0-rc1`) and will break the build at a moment
unrelated to any change you made.

For a repository whose value proposition is "this theorem is machine-checked",
reproducibility is part of the claim. Pin to a released Mathlib tag compatible
with the toolchain, and bump deliberately.

### P4 — Add a `LICENSE` file *[proposed]*

There is no `LICENSE`, `COPYING`, or license header anywhere. With no license,
default copyright applies and nobody may legally reuse the work — which
directly contradicts the stated §9 goal of upstreaming parts of it to Mathlib.
Mathlib is Apache 2.0; matching it removes any friction from a future
contribution. This is the cheapest item on the list and the one most likely to
matter.

### P5 — Dead code: essentially none **[verified]**

Recorded as a negative result, because the check is worth not repeating.

A mechanical scan initially flagged 17 declarations as textually unreferenced.
On direct verification, **16 of the 17 are genuinely consumed**:

- **12 carry `@[simp]`** and are part of the simp set without ever being named
  in a proof (`wreath_act`, `wreathList_nil`, `resetMonoid_act_to`, …).
- **2 are referenced by the blueprint**, not by Lean — `trivialTM_faithful` and
  `SemigroupDivides.of_subsemigroup` both appear in `\lean{...}\leanok`
  annotations, so deleting them would break `leanblueprint checkdecls`.
- **1 was a false positive of the scan itself** — `act_mul_mulTM'`
  (`GroupCase.lean:399`) *is* used at `GroupCase.lean:408`; the trailing
  apostrophe in the name defeated the regex word-boundary.

That leaves exactly one unreferenced declaration, `BarMonoid.ofHom_injective`
(`Bar.lean:85`), a two-line API-completeness lemma. Keeping it is fine.

**The transferable lesson:** in a blueprint-driven repository there are *three*
consumers of a declaration — Lean proofs, the simp set, and `\lean{}`
annotations in `blueprint/src/`. Any future dead-code analysis must check all
three, or it will recommend deleting declarations that CI depends on.

### P6 — Harden the axiom-certificate CI check *[proposed]*

The current check asserts `wc -l == 19` plus an allowlist scan. Two soft spots:

- The magic number `19` must be hand-bumped, and a change that *removes* one
  `#print axioms` while *adding* another leaves the count unchanged and passes.
- The Python scan only inspects lines matching `depends on axioms: [...]`; any
  line in another shape is skipped silently.

Stronger and barely longer: assert the exact *set* of declaration names present
in the output, so silently dropping a theorem from the certificate fails CI.
The certificate is the repository's central correctness claim; it is worth
making it tamper-evident rather than count-evident.

### P7 — Drop the `Faithful` hypothesis from `krohnRhodes` *[proposed, larger]*

`krohnRhodes` currently requires `T.Faithful`. Spec §3.1 notes that every
`(X, M)` has a faithful quotient but that v1 only needed the regular
representation. Building `faithfulQuotient : TransMon → TransMon` together with
`T.M ≺ₘ (faithfulQuotient T).M` would let the headline theorem apply to *every*
finite transformation monoid, not only faithful ones — a genuine strengthening
of the main statement rather than new infrastructure for its own sake.

Estimated at a modest amount of work (quotient by the kernel congruence of the
action, which Mathlib's `Con` supports directly).

### P8 — Upstream to Mathlib *[proposed]*

Already identified in spec §9 and worth restating as concrete, separable
deliverables:

1. **`Subsemigroup` comap surjectivity.** M9 had to prove the `MulHom`-level
   analogue of `submonoidComap_surjective_of_surjective` inline because Mathlib
   has no `Subsemigroup` version. This is a self-contained, obviously-correct
   PR and the clearest first candidate.
2. **`exists_pow_idempotent`** (`FiniteMonoid.lean`) — every element of a finite
   monoid has an idempotent power. Standard, general, currently unused by this
   project's main line (its consumer is the v2 aperiodic corollary), which makes
   it a clean donation.
3. **A monoid-level wreath product.** Mathlib has `RegularWreathProduct` for
   groups only. `WreathMonoid` generalizes it and is already written in
   Mathlib's own idiom.

### P9 — Consider splitting the two largest modules *[proposed, low priority]*

`Decomposition.lean` (651 lines) and `GroupCase.lean` (630) are the two biggest
files; the project's own design guidance treats file size as a signal of doing
too much. Both are internally cohesive — `GroupCase.lean` in particular splits
cleanly along its existing section headers (Kaloujnine–Krasner / the
composition-series induction / DKS 2.11). This is a readability nicety, not a
defect; weigh it against the churn.

---

## Part 3 — What is already good

Worth recording so it is not lost in a document about defects:

- **The twist guard** (`Wreath.lean:98-101`) is a model of what a formalization
  sanity check should be: it names the two plausible wrong definitions and
  exhibits a computation that distinguishes all three.
- **The chirality check** (`Basic.lean:117-122`) uses `Equiv.Perm (Fin 3)`
  precisely because the `ZMod n` examples are commutative and therefore blind to
  which side the action multiplies on. Recognizing that a passing test was
  *incapable of failing* is the hard part of testing, and it was caught.
- **The axiom certificate** is genuinely enforced in CI, not merely present.
- **The instance-diamond discipline** is applied uniformly and for a stated
  reason in each case.
- **Amendments are dated and justified** in the spec rather than silently
  applied, so the reasoning behind each mid-flight change survives.
