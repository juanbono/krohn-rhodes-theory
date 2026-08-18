# Krohn–Rhodes Milestone 4 (Bar + Resets) Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Build the bar operation (adjoin resets) with `bar_divides`, the reset monoids `U(X)` and the flip-flop, and prove DKS Lemma 2.12 (`reset_div_flipFlops`) — plus the housekeeping carried from the M3 final review (spec prose fixes including the 36→27 figure, `Trans`-instance relocation, section-helper promotion).

**Architecture:** Two new files: `KRTheory/TransMon/Bar.lean` (definitional + `bar_divides`) and `KRTheory/TransMon/Reset.lean` (definitional + the 2.12 induction). Both monoid carriers are fresh **inductives** (`BarMonoid T` with constructors `of`/`reset`; `Resets X` with `id`/`to`) — diamond-free like M3's `WreathMonoid`, and **computable** (Fintype via `Fintype.ofEquiv` from `Sum`/`Option`), so `decide`-based examples return. Housekeeping touches `Division.lean`, `WreathDivision.lean`, the spec, and the blueprint.

**Tech Stack:** Lean 4 / Mathlib as pinned. Base code: branch `milestone-3` at `5cc089b` (or wherever the M0–3 stack lives after any merge — executor branches from whichever holds the M3 code).

**Spec:** `docs/superpowers/specs/2026-08-17-krohn-rhodes-formalization-design.md` — §3.4 (bar), §3.5 (resets/flip-flop, DKS 2.12), §7 row 4 acceptance ("[DKS] 2.12 proved"). Task 1 amends the spec with this plan's refinements (see below).

## Global Constraints

- All Lean code inside `namespace KRTheory`/`TransMon`; notation scoped; carriers in `Type`.
- **Computability**: nothing in `Bar.lean`/`Reset.lean` is `noncomputable` except where a proof term forces it (none expected); `decide`/`rfl` examples preferred where types are concrete.
- Docstrings on every new public declaration including inductive constructors where meaningful; module docstrings cite [DKS §2.4] (bar) / [DKS §2.5→2.12] (resets).
- Guard-example discipline (spec §6): each twisted/asymmetric operation gets an example that a transposed definition would fail, with a comment naming the wrong definition it kills. Noncommutative guards use `Equiv.Perm (Fin 3)` (imports already present in `Basic.lean`).
- Zero-warning builds; no `sorry`/`admit`/`native_decide`; plain commit messages, no trailers.
- Standing rulings carried forward: narrow Mathlib imports allowed (document); name-drift/proof-script latitude with statements fixed; pair-literal simp stall → `rfl`/`show` (documented in Wreath.lean); `Nat.card` (not `Fintype.card`+`decide`) for wreath-monoid cardinalities.
- Formalization-TDD: RED = statements + sorries + examples elaborate; GREEN = proofs in, `grep -rn "sorry" KRTheory/ KRTheory.lean` empty.

## Spec refinements this plan introduces (Task 1 records them in the spec)

1. §3.4: bar's monoid carrier is a fresh inductive `BarMonoid T` (`of`/`reset` constructors), not raw `M ⊕ X` — same diamond-avoidance rationale as M3's `WreathMonoid`.
2. §3.5: `U(X)`'s carrier is a fresh inductive `Resets X` (`id`/`to`), not raw `Option X` — avoids planting a global `Monoid (Option _)` instance on a ubiquitous type.
3. §3.5: DKS 2.12 requires **`[Nonempty X]`** — an empty-state transformation monoid strongly divides only empty-state ones (no function into `∅`), so `U(∅)` divides no flip-flop wreath. DKS assume nonempty state sets implicitly.
4. §3.5: the formal 2.12 statement is existential in the number of factors: `∃ n, resetMonoid X ≺ wreathList (List.replicate n flipFlop)` (KR needs existence only).
5. §6: the example figure "wreath of two flip-flops has 36 monoid elements" is corrected to **27** (3² · 3).
6. `bar_mono` (spec §3.4's "flagged, not assumed") is confirmed NOT needed: the KR induction's bars ride on the IH outputs (Q(T) delivers `T̄ ≺ …` directly); recorded, not built (YAGNI).

## Mathematical target

**Bar** [DKS §2.4]: `T.bar = (T.X, BarMonoid T)`;
`of m * of n = of (m*n)`; `of m * reset x = reset x`; `reset x * of m = reset (x·m)`; `reset x * reset y = reset y`; `1 = of 1`.
Action: `x ⊳ of m = x ·_T m`; `x ⊳ reset x₀ = x₀`. Lemma: `T ≺ T.bar` (cover through the `of`-image submonoid).

**Resets** [DKS §2.5]: `Resets X` = identity + one reset per point; `a * to y = to y`, `a * id = a`, `1 = id`. `resetMonoid X = (X, Resets X)`; `flipFlop = resetMonoid Bool` (2 states, 3 elements).

**DKS 2.12** by strong induction on `|X|` (X nonempty):
- `|X| = 1`: `resetMonoid X ≺ flipFlop` (constant state map; `ψ : Resets Bool ↠ Resets X` collapsing both resets to the unique point) — then into `wreathList [flipFlop]`.
- `|X| ≥ 2`: pick x₀, set `Y := {x // x ≠ x₀}` (nonempty, `|Y| = |X| - 1`). **Split lemma**: `resetMonoid X ≺ resetMonoid Y ≀ flipFlop` — the flip-flop flag means "current state is x₀". State map `φ (y, b) = if b then x₀ else ↑y` (surjective since Y nonempty). Submonoid of the wreath monoid: elements `(f, r)` with **(C1)** `f` constant, **(C2)** `r = to false → f-value ≠ id`, **(C3)** `r = id → f-value = id`. (C2/C3 exclude elements with no `U(X)` counterpart: `(const id, to false)` moves x₀ into Y depending on hidden state; `(const (to y), id)` acts differently on x₀ and its complement.) Closure table (verified): products' right components decide the case; C1 is preserved componentwise; result `r = id` only from `1 * 1`; result `to false` forces the second factor's or (via C3-collapsed second factor) the first factor's C2. `ψ`: `1 ↦ id`; `(g, to true) ↦ to x₀`; `(to y, to false) ↦ to ↑y`. Hom by case on the second factor's `r`; surjective by the three witness families; equivariance by case on `r`.
- Glue: split + IH via `StrongDivides.wreath` (with `flipFlop ≺ wreathList [flipFlop]` = `div_wreathList_singleton`), then `wreathList_append`, then `List.replicate_succ'`-style `replicate n a ++ [a] = replicate (n+1) a`.

This induction consumes exactly M3's exports — it is the integration test of that layer.

---

### Task 1: Housekeeping, spec fixes, blueprint chapters

**Files:**
- Modify: `docs/superpowers/specs/2026-08-17-krohn-rhodes-formalization-design.md`
- Modify: `KRTheory/TransMon/Division.lean`, `KRTheory/TransMon/WreathDivision.lean` (Trans instance + sect promotion moves)
- Create: `blueprint/src/chapters/bar.tex`, `blueprint/src/chapters/reset.tex`
- Modify: `blueprint/src/content.tex`

**Interfaces:**
- Produces: relocated `instance : Trans StrongDivides StrongDivides StrongDivides` in `Division.lean` (immediately after `StrongDivides.trans`; docstring kept); public `Covering.sect {S T : TransMon} (c : Covering S T) : S.X → T.X` and `Covering.stateMap_sect (c) (x) : c.stateMap (c.sect x) = x` in `Division.lean` (immediately after the extMap kit; docstrings; the private copies in `WreathDivision.lean` deleted and use sites updated to the public names). Blueprint `\lean{}` contract for Tasks 2–6: `KRTheory.TransMon.BarMonoid`, `KRTheory.TransMon.bar`, `KRTheory.TransMon.bar_divides`, `KRTheory.TransMon.BarMonoid.ofHom`, `KRTheory.TransMon.Resets`, `KRTheory.TransMon.resetMonoid`, `KRTheory.TransMon.flipFlop`, `KRTheory.TransMon.reset_split`, `KRTheory.TransMon.reset_div_flipFlops`.

- [ ] **Step 1: Spec prose fixes** — in §3.3 lemma list and §3.9: replace `wreath_div_wreath` → `StrongDivides.wreath`, `wreath_trivial_div` → `div_wreath_trivial`, `Monoid ((Y → M) × N)` → "`WreathMonoid` (fresh structure; see §4.3)". In §6: "36" → "27 (3² · 3)". In §3.4/§3.5: add the six refinements from this plan's "Spec refinements" section as short notes (carrier inductives; `[Nonempty X]`; existential factor count; bar_mono confirmed unneeded). Update §4.3's Bar/Reset rows to the shipped declaration names above.

- [ ] **Step 2: Lean moves** — cut the `Trans` instance from `WreathDivision.lean` (top) and paste after `StrongDivides.trans` in `Division.lean`. In `WreathDivision.lean`, delete `private def Covering.sect` and `private theorem Covering.stateMap_sect`; add public equivalents in `Division.lean` after the extMap kit:

```lean
/-- A chosen section of the state surjection: `c.stateMap (c.sect x) = x`.
Noncomputable (choice); used by wreath monotonicity and, later, the
group case. -/
noncomputable def Covering.sect {S T : TransMon} (c : Covering S T) :
    S.X → T.X := Function.surjInv c.stateMap_surj

@[simp]
theorem Covering.stateMap_sect {S T : TransMon} (c : Covering S T)
    (x : S.X) : c.stateMap (c.sect x) = x :=
  Function.surjInv_eq c.stateMap_surj x
```

(If the private versions' statements differ cosmetically, adapt use sites in `WreathDivision.lean`, keeping `Covering.wreath`'s construction otherwise untouched. If `stateMap_sect` as `@[simp]` breaks any existing proof, drop the attribute and note it.)

- [ ] **Step 3: Blueprint chapters** — `bar.tex`:

```latex
\chapter{The bar operation}\label{ch:bar}

Cascade decompositions must be able to overwrite the front coordinate,
so the induction runs through monoids with all constant maps adjoined
[DKS §2.4].

\begin{definition}[Bar]\label{def:bar}
  \lean{KRTheory.TransMon.BarMonoid, KRTheory.TransMon.bar}
  \uses{def:transmon}
  For $T = (X, M)$, $\overline{T} := (X, \overline{M})$ where
  $\overline{M} = M \sqcup \{\mathrm{reset}_x : x \in X\}$ with
  $m \cdot \mathrm{reset}_x = \mathrm{reset}_x$,
  $\mathrm{reset}_x \cdot m = \mathrm{reset}_{x \cdot m}$,
  $\mathrm{reset}_x \cdot \mathrm{reset}_y = \mathrm{reset}_y$, and
  $\mathrm{reset}_x$ acting as the constant map $x$.
  (In Lean the carrier is a fresh inductive with embeddings
  \lean{KRTheory.TransMon.BarMonoid.ofHom}.)
\end{definition}

\begin{lemma}[Bar absorbs the original]\label{lem:bar-divides}
  \lean{KRTheory.TransMon.bar_divides}\uses{def:bar,def:sdiv}
  $T \prec \overline{T}$.
\end{lemma}
\begin{proof}
  Cover through the image of $M$ in $\overline{M}$; states unchanged.
\end{proof}

\begin{remark}[Degenerate states]\label{rem:bar-degenerate}
  For $|X| \le 1$ every reset acts as the identity, so
  $\overline{T}$'s action is not faithful. No lemma in the development
  claims faithfulness of $\overline{T}$; bars appear on the left of
  $\prec$ or as covering \emph{sources}, where this is harmless.
\end{remark}
```

`reset.tex`:

```latex
\chapter{Reset monoids and the flip-flop}\label{ch:reset}

\begin{definition}[Reset monoid]\label{def:resets}
  \lean{KRTheory.TransMon.Resets, KRTheory.TransMon.resetMonoid}
  \uses{def:transmon}
  $U(X) := (X, \{\mathrm{id}\} \cup \{\mathrm{to}_x : x \in X\})$ with
  $a \cdot \mathrm{to}_y = \mathrm{to}_y$ and $a \cdot \mathrm{id} = a$;
  $\mathrm{to}_x$ acts as the constant map $x$.
\end{definition}

\begin{definition}[Flip-flop]\label{def:flipflop}
  \lean{KRTheory.TransMon.flipFlop}\uses{def:resets}
  The flip-flop is $U(\mathbf{2})$: two states, three elements — the
  unique non-group prime of Krohn--Rhodes theory. The monoid part of
  the wreath product of two flip-flops has $3^2 \cdot 3 = 27$ elements.
\end{definition}

\begin{lemma}[Split]\label{lem:reset-split}
  \lean{KRTheory.TransMon.reset_split}
  \uses{def:resets,def:flipflop,def:wreath,def:sdiv}
  For finite $X$, $x_0 \in X$ with $Y := X \setminus \{x_0\}$ nonempty:
  $U(X) \prec U(Y) \wr U(\mathbf 2)$.
\end{lemma}
\begin{proof}
  The flag records ``the current state is $x_0$'':
  $\varphi(y, b) = x_0$ if $b$ else $y$. The covering submonoid consists
  of constant-front pairs $(f, r)$ with two side conditions —
  $r = \mathrm{to}_{\mathrm{false}}$ forces the front value to be a
  reset, and $r = \mathrm{id}$ forces it to be $\mathrm{id}$ — excluding
  exactly the wreath elements with no $U(X)$ counterpart. The covering
  map sends $(g, \mathrm{to}_{\mathrm{true}}) \mapsto \mathrm{to}_{x_0}$
  and $(\mathrm{to}_y, \mathrm{to}_{\mathrm{false}}) \mapsto
  \mathrm{to}_y$.
\end{proof}

\begin{lemma}[DKS 2.12]\label{lem:reset-div-flipflops}
  \lean{KRTheory.TransMon.reset_div_flipFlops}
  \uses{lem:reset-split,lem:wreath-mono,lem:wreathList-append,
        lem:wreath-trivial,def:wreathList}
  For finite nonempty $X$ there is $n$ with
  $U(X) \prec \underbrace{U(\mathbf 2) \wr \cdots \wr
  U(\mathbf 2)}_{n}$.
  Nonemptiness is necessary: an empty-state transformation monoid
  strongly divides only empty-state ones.
\end{lemma}
\begin{proof}
  Strong induction on $|X|$. Base $|X| = 1$: collapse the flip-flop onto
  the point. Step: Lemma~\ref{lem:reset-split}, the induction
  hypothesis, monotonicity, and the append lemma.
\end{proof}
```

Register both in `content.tex` after the wreath input:

```latex
\input{chapters/bar}
\input{chapters/reset}
```

- [ ] **Step 4: Build + conditional LaTeX check + commit**

```bash
lake build 2>&1 | tail -3
grep -rn "sorry" KRTheory/ KRTheory.lean; test $? -eq 1 && echo clean
command -v latexmk >/dev/null && (cd blueprint/src && latexmk -pdf -interaction=nonstopmode print.tex && latexmk -c) || echo "latexmk absent - skip ok"
git add -A && git commit -m "Housekeeping: spec fixes, Trans and section helpers relocated, bar and reset blueprint chapters"
```

Expected: build green zero warnings (the Lean moves must not break `Covering.wreath`).

---

### Task 2: BarMonoid + bar

**Files:**
- Create: `KRTheory/TransMon/Bar.lean`
- Modify: `KRTheory.lean` (add import)

**Interfaces:**
- Consumes: `TransMon` (Basic).
- Produces: `inductive KRTheory.TransMon.BarMonoid (T : TransMon) : Type | of (m : T.M) | reset (x : T.X)` (deriving `DecidableEq`); computable `Monoid (BarMonoid T)`; `@[simp]` `of_mul_of : (.of m * .of n : BarMonoid T) = .of (m * n)`, `of_mul_reset : (.of m * .reset x : BarMonoid T) = .reset x`, `reset_mul_of : (.reset x * .of m : BarMonoid T) = .reset (T.act x m)`, `reset_mul_reset : (.reset x * .reset y : BarMonoid T) = .reset y`, `one_def : (1 : BarMonoid T) = .of 1`; `BarMonoid.ofHom : T.M →* BarMonoid T` with `@[simp] ofHom_apply : ofHom m = .of m`; `ofHom_injective`; `BarMonoid.equivSum : BarMonoid T ≃ T.M ⊕ T.X`; computable `Fintype (BarMonoid T)` via `Fintype.ofEquiv`; `BarMonoid.natCard : Nat.card (BarMonoid T) = Nat.card T.M + Nat.card T.X`; `def TransMon.bar (T : TransMon) : TransMon` (computable; X := T.X, M := BarMonoid T); `@[simp]` `bar_act_of : T.bar.act x (.of m) = T.act x m`, `bar_act_reset : T.bar.act x (.reset x₀) = x₀`.

- [ ] **Step 1: Write the file (RED — monoid laws + natCard sorried, everything else complete)**

```lean
import KRTheory.TransMon.Basic

/-!
# The bar operation: adjoining resets

`T.bar` [DKS §2.4] adjoins all constant maps ("resets") to a
transformation monoid — cascade decompositions need to overwrite state.
The carrier is a fresh inductive (not `T.M ⊕ T.X`) for the same
diamond-avoidance reason as `WreathMonoid`; unlike the wreath, everything
here is computable.
-/

namespace KRTheory
namespace TransMon

/-- The monoid of `T.bar` [DKS §2.4]: the original elements (`of`)
together with one reset per state (`reset`). Multiplication remembers
that the LEFT factor acts first: a reset followed by `m` is a reset to
the moved point; anything followed by a reset is that reset. -/
inductive BarMonoid (T : TransMon) : Type
  /-- An original monoid element. -/
  | of (m : T.M)
  /-- The constant map onto `x`. -/
  | reset (x : T.X)
  deriving DecidableEq

namespace BarMonoid

variable {T : TransMon}

/-- The twisted multiplication; left factor acts first. -/
instance : Monoid (BarMonoid T) where
  mul w w' := match w, w' with
    | .of m, .of n => .of (m * n)
    | _, .reset x => .reset x
    | .reset x, .of m => .reset (T.act x m)
  one := .of 1
  mul_assoc := sorry
  one_mul := sorry
  mul_one := sorry

@[simp] theorem of_mul_of (m n : T.M) :
    (.of m * .of n : BarMonoid T) = .of (m * n) := rfl
@[simp] theorem of_mul_reset (m : T.M) (x : T.X) :
    (.of m * .reset x : BarMonoid T) = .reset x := rfl
@[simp] theorem reset_mul_of (x : T.X) (m : T.M) :
    (.reset x * .of m : BarMonoid T) = .reset (T.act x m) := rfl
@[simp] theorem reset_mul_reset (x y : T.X) :
    (.reset x * .reset y : BarMonoid T) = .reset y := rfl
@[simp] theorem one_def : (1 : BarMonoid T) = .of 1 := rfl

/-- Embedding of the original monoid. -/
def ofHom : T.M →* BarMonoid T where
  toFun := .of
  map_one' := rfl
  map_mul' _ _ := rfl

@[simp] theorem ofHom_apply (m : T.M) : (ofHom m : BarMonoid T) = .of m := rfl

theorem ofHom_injective : Function.Injective (ofHom (T := T)) :=
  fun _ _ h => by injection h

/-- As a type, `BarMonoid T` is the sum of the monoid and the states. -/
def equivSum : BarMonoid T ≃ T.M ⊕ T.X where
  toFun w := match w with | .of m => .inl m | .reset x => .inr x
  invFun s := match s with | .inl m => .of m | .inr x => .reset x
  left_inv w := by cases w <;> rfl
  right_inv s := by cases s <;> rfl

instance : Fintype (BarMonoid T) := Fintype.ofEquiv _ equivSum.symm

/-- `|BarMonoid T| = |M| + |X|`. -/
theorem natCard : Nat.card (BarMonoid T) = Nat.card T.M + Nat.card T.X := sorry

end BarMonoid

/-- The bar operation `T.bar` [DKS §2.4]: same states, resets adjoined.
Computable (contrast `wreath`). -/
def bar (T : TransMon) : TransMon where
  X := T.X
  M := BarMonoid T
  act x w := match w with | .of m => T.act x m | .reset x₀ => x₀
  act_one x := by simp
  act_mul := sorry

@[simp] theorem bar_act_of {T : TransMon} (x : T.X) (m : T.M) :
    T.bar.act x (.of m) = T.act x m := rfl
@[simp] theorem bar_act_reset {T : TransMon} (x x₀ : T.X) :
    T.bar.act x (.reset x₀) = x₀ := rfl

-- Sanity checks (spec §6). Chirality guard over a noncommutative monoid:
-- reset-then-act must move the reset point by m ON THE RIGHT.
-- With T = regular (Equiv.Perm (Fin 3)): (.reset (swap 0 1) * .of (swap 1 2))
-- must be .reset (swap 0 1 * swap 1 2); the transposed definition
-- .reset (m * x) would give .reset (swap 1 2 * swap 0 1) ≠.
example :
    ((.reset (Equiv.swap 0 1) * .of (Equiv.swap 1 2) :
      BarMonoid (regular (Equiv.Perm (Fin 3))))) =
      .reset (Equiv.swap 0 1 * Equiv.swap 1 2) := rfl
example :  -- and the two permutations genuinely differ at 0
    (Equiv.swap 0 1 * Equiv.swap 1 2 : Equiv.Perm (Fin 3)).toFun 0 ≠
      (Equiv.swap 1 2 * Equiv.swap 0 1 : Equiv.Perm (Fin 3)).toFun 0 := by
  decide
example : Nat.card (BarMonoid (regular (ZMod 3))) = 6 := by
  simp [BarMonoid.natCard, Nat.card_eq_fintype_card]  -- 3 + 3; adjust script freely
example (x : trivialTM.X) :
    trivialTM.bar.act x (.reset PUnit.unit) = PUnit.unit := rfl

end TransMon
end KRTheory
```

Add `import KRTheory.TransMon.Bar` to `KRTheory.lean`. Expected at RED: exactly four sorries (three laws + natCard + act_mul = five; count them in the build output). The guard examples must pass at RED (they are `rfl`/`decide` against complete definitions).

- [ ] **Step 2: Prove the laws (GREEN)**

`mul_assoc`: `intro a b c; cases a <;> cases b <;> cases c <;> simp [mul_assoc, TransMon.act_mul]` — the 8 cases from the plan's math-target table; if the instance's own `match` needs unfolding before the simp kit applies, insert the corresponding `show` per case (all reductions are `rfl`). `one_mul`/`mul_one`: `cases`, then `simp` (uses `T.act_one` for `reset * of 1`... note `mul_one` case `.reset x * .of 1 = .reset (T.act x 1) = .reset x` — `simp` with `act_one`). `bar.act_mul`: `intro x w w'; cases w <;> cases w' <;> simp [TransMon.act_mul]`. `natCard`: `rw [Nat.card_congr BarMonoid.equivSum, Nat.card_sum]` (name-drift latitude on `Nat.card_sum`).

- [ ] **Step 3: Build clean + no sorry + commit**

```bash
lake build 2>&1 | tail -5 && (grep -rn "sorry" KRTheory/ KRTheory.lean; test $? -eq 1 && echo clean)
git add KRTheory.lean KRTheory/TransMon/Bar.lean
git commit -m "Add bar monoid adjoining resets"
```

---

### Task 3: bar_divides

**Files:**
- Modify: `KRTheory/TransMon/Bar.lean` (append before the examples, or after — keep examples last)

**Interfaces:**
- Consumes: `BarMonoid.ofHom`, `ofHom_injective` (Task 2); `Covering`, `StrongDivides` (Division).
- Produces: `theorem KRTheory.TransMon.bar_divides (T : TransMon) : T ≺ T.bar`.

- [ ] **Step 1: Statement + sorry + example (RED), then prove (GREEN)**

RED skeleton (compiles with three sorries):

```lean
/-- The original divides its bar: cover through the `of`-image
[DKS §2.4]. Together with Q(T)'s barred conclusions this removes bars
from final statements. -/
theorem bar_divides (T : TransMon) : T ≺ T.bar :=
  ⟨{ toSubmonoid := BarMonoid.ofHom.mrange
     stateMap := id
     monoidMap := sorry
     stateMap_surj := Function.surjective_id
     monoidMap_surj := sorry
     equivariant := sorry }⟩
```

Route note (implementer latitude): the intended construction is the monoid iso `T.M ≃* BarMonoid.ofHom.mrange` from injectivity — Mathlib has `MulEquiv.ofInjective`-style API for `MonoidHom` (`MonoidHom.ofInjective`? find via loogle/`exact?`; it may be stated as `f.mrange ≃* M`-direction). Equivariance needs, for `n : mrange`, `T.act x (ψ n) = T.bar.act x ↑n`: destructure `n = ⟨.of m, ⟨m, rfl⟩⟩` via `rintro x ⟨_, m, rfl⟩` and reduce both sides to `T.act x m` (the `ψ (of m) = m` step may need the equiv's `symm_apply_apply`). **Fallback** (fully authorized if the iso API fights): build `monoidMap` directly with `MonoidHom.mk'` using the total extraction `fun w => match (w : BarMonoid T) with | .of m => m | .reset _ => 1` restricted to `mrange`, proving `map_mul`/surjectivity/equivariance by `rintro ⟨_, m, rfl⟩` case analysis — junk branch never fires on members.

Sanity examples (append at file bottom):

```lean
example : trivialTM ≺ trivialTM.bar := bar_divides _
example : (regular (ZMod 2)) ≺ (regular (ZMod 2)).bar := bar_divides _
```

- [ ] **Step 2: Build clean + no sorry + commit**

```bash
lake build 2>&1 | tail -5 && (grep -rn "sorry" KRTheory/ KRTheory.lean; test $? -eq 1 && echo clean)
git add KRTheory/TransMon/Bar.lean
git commit -m "Add bar absorption lemma"
```

---

### Task 4: Resets, resetMonoid, flipFlop

**Files:**
- Create: `KRTheory/TransMon/Reset.lean`
- Modify: `KRTheory.lean` (add import)

**Interfaces:**
- Consumes: `TransMon`, `Wreath.lean`'s `WreathMonoid.natCard` (for the 27 example).
- Produces: `inductive KRTheory.TransMon.Resets (X : Type) : Type | id | to (x : X)` deriving `DecidableEq`; computable `Monoid (Resets X)`; `@[simp]` `mul_to : (a * .to y : Resets X) = .to y`, `one_def : (1 : Resets X) = .id` (plus `mul_id : (a * .id : Resets X) = a` if not already covered by `mul_one` after `one_def`); `Resets.equivOption : Resets X ≃ Option X`; `[Fintype X] → Fintype (Resets X)` (computable, via `Fintype.ofEquiv`); `Resets.natCard [Fintype X] : Nat.card (Resets X) = Nat.card X + 1`; `def TransMon.resetMonoid (X : Type) [Fintype X] : TransMon` (computable; states X, monoid `Resets X`, `.to y` acts constantly); `@[simp]` `resetMonoid_act_id`, `resetMonoid_act_to`; `def TransMon.flipFlop : TransMon := resetMonoid Bool`.

- [ ] **Step 1: Write the file (RED — laws + natCard sorried)**

```lean
import KRTheory.TransMon.Wreath

/-!
# Reset monoids and the flip-flop

`U(X)` [DKS §2.5]: the identity plus one reset per point of `X`. The
flip-flop `U(Bool)` — two states, three elements — is the unique
non-group prime of Krohn–Rhodes theory. Fresh inductive carrier (not
`Option X`) to avoid planting a global `Monoid (Option _)` instance.
Everything here is computable.
-/

namespace KRTheory
namespace TransMon

/-- The reset monoid's carrier: `id` plus one reset per point. -/
inductive Resets (X : Type) : Type
  /-- The identity element. -/
  | id
  /-- The reset onto `x`. -/
  | to (x : X)
  deriving DecidableEq

namespace Resets

variable {X : Type}

/-- Right-selection multiplication: the LAST reset wins; `id` is
neutral. (Left factor acts first, and a later reset overwrites.) -/
instance : Monoid (Resets X) where
  mul a b := match b with | .id => a | .to y => .to y
  one := .id
  mul_assoc := sorry
  one_mul := sorry
  mul_one := sorry

@[simp] theorem mul_to (a : Resets X) (y : X) :
    (a * .to y : Resets X) = .to y := rfl
@[simp] theorem one_def : (1 : Resets X) = (.id : Resets X) := rfl
@[simp] theorem mul_id (a : Resets X) : (a * .id : Resets X) = a := rfl

/-- As a type, `Resets X` is `Option X`. -/
def equivOption : Resets X ≃ Option X where
  toFun a := match a with | .id => none | .to x => some x
  invFun o := match o with | none => .id | some x => .to x
  left_inv a := by cases a <;> rfl
  right_inv o := by cases o <;> rfl

instance [Fintype X] : Fintype (Resets X) := Fintype.ofEquiv _ equivOption.symm

/-- `|U(X)'s monoid| = |X| + 1`. -/
theorem natCard [Fintype X] : Nat.card (Resets X) = Nat.card X + 1 := sorry

end Resets

/-- The reset transformation monoid `U(X)` [DKS §2.5]: `Resets X`
acting on `X`, `to y` constantly. Computable. -/
def resetMonoid (X : Type) [Fintype X] : TransMon where
  X := X
  M := Resets X
  act x r := match r with | .id => x | .to y => y
  act_one _ := rfl
  act_mul := sorry

@[simp] theorem resetMonoid_act_id {X : Type} [Fintype X] (x : X) :
    (resetMonoid X).act x .id = x := rfl
@[simp] theorem resetMonoid_act_to {X : Type} [Fintype X] (x y : X) :
    (resetMonoid X).act x (.to y) = y := rfl

/-- The flip-flop: two states, three elements — the non-group prime.
[DKS §2.5] -/
def flipFlop : TransMon := resetMonoid Bool

-- Sanity checks (spec §6).
-- Selection-direction guard: the RIGHT (later) reset must win; a
-- left-wins definition would return .to false here.
example : ((.to false * .to true : Resets Bool)) = .to true := by decide
example : ((.to true * .id : Resets Bool)) = .to true := by decide
example : Nat.card flipFlop.M = 3 := by
  simp [flipFlop, Resets.natCard, Nat.card_eq_fintype_card]
example : flipFlop.act false (.to true) = true := rfl
example : flipFlop.act true (.id) = true := rfl
-- The spec-§6 figure, corrected (was wrongly 36): 3² · 3 = 27.
example : Nat.card (WreathMonoid flipFlop flipFlop) = 27 := by
  simp [WreathMonoid.natCard, flipFlop, Resets.natCard,
    Nat.card_eq_fintype_card]
```

Add the root import. RED: exactly four sorries; guard/`decide` examples pass. Script latitude on the `Nat.card` example proofs (they mix `Nat.card`/`Fintype.card` conversions — `Nat.card_eq_fintype_card` plus `rfl`-computation on the concrete `Bool` instances; `decide` also acceptable where it elaborates).

- [ ] **Step 2: Prove the laws (GREEN)** — `mul_assoc`: `intro a b c; cases c <;> cases b <;> rfl`-style (only the last factor matters; if `rfl` per case stalls on the instance match, `simp [...]` with the kit). `one_mul`: `cases b <;> rfl`. `mul_one`: `rfl` (match on `.id` returns `a`). `resetMonoid.act_mul`: `intro x a b; cases b <;> rfl` (b = .to y: both sides `y`; b = .id: both sides `x ⊳ a`... careful — `act x (a * .id) = act x a` and `act (act x a) .id = act x a` ✓).

- [ ] **Step 3: Build clean + no sorry + commit**

```bash
lake build 2>&1 | tail -5 && (grep -rn "sorry" KRTheory/ KRTheory.lean; test $? -eq 1 && echo clean)
git add KRTheory.lean KRTheory/TransMon/Reset.lean
git commit -m "Add reset monoids and the flip-flop"
```

---

### Task 5: reset_split (the boss)

**Files:**
- Modify: `KRTheory/TransMon/Reset.lean` (append after flipFlop, before the examples; move examples last)

**Interfaces:**
- Consumes: everything from Task 4; `wreath`/`≀`, `wreath_act`, mirror kit (`Wreath.lean`); `Covering`/`StrongDivides` (`Division.lean`, via Wreath's import chain — add `import KRTheory.TransMon.Division` explicitly if the chain doesn't already provide it).
- Produces: `theorem KRTheory.TransMon.reset_split (X : Type) [Fintype X] (x₀ : X) [Nonempty {x : X // x ≠ x₀}] : resetMonoid X ≺ resetMonoid {x : X // x ≠ x₀} ≀ flipFlop`.

The construction, fully derived (blueprint `lem:reset-split`); Y := `{x // x ≠ x₀}`:

- **stateMap** `φ : Y × Bool → X := fun p => if p.2 then x₀ else ↑p.1`. Surjective: `x = x₀` ← `(Classical.arbitrary Y, true)`; `x ≠ x₀` ← `(⟨x, h⟩, false)`.
- **toSubmonoid** carrier: `{w | (∀ b b', w.left b = w.left b') ∧ (w.right = .to false → w.left true ≠ .id) ∧ (w.right = .id → w.left true = .id)}` (C1 constancy, C2, C3).
  - `one_mem`: left = const `.id` ✓ C1; C2 vacuous (`1.right = .id ≠ .to false` — discriminate constructors); C3: `.id = .id` ✓.
  - `mul_mem` (case on `w'.right`, using `wreath_mul_left/right` or `show`-rfl):
    - `w'.right = .to y'`: result right `.to y'`; C3 vacuous; C2: result left-value `= w.left b * w'.left …` — by C1 rewrite to `w.left true * w'.left true`; if `y' = false`... careful: C2's hypothesis is about the RESULT's right being `.to false`, i.e. `y' = false`; then `w'` satisfies its own C2 (`w'.left true ≠ .id`), and `a * .to-value = .to-value ≠ .id` by `mul_to` + constructor discrimination. C1 for the result: both factors constant → product constant (needs `w'.left (flipFlop.act b w.right) = w'.left (flipFlop.act b' w.right)` — from `w'`'s C1 directly, any two arguments).
    - `w'.right = .id`: `w' = ` has C3 → `w'.left`-value `.id` (all b by C1); result right = `w.right * .id = w.right`; result left-value `= w.left b * .id = w.left b` (`mul_id`) — so result satisfies exactly `w`'s conditions ✓.
- **monoidMap** (total-with-junk, membership discharges): for `w` in the submonoid,
  `ψ w := match w.val.right with | .to true => .to x₀ | .to false => (match w.val.left true with | .to y => .to ↑y | .id => 1) | .id => 1`.
  - `map_one'`: right `.id` → `1` ✓.
  - `map_mul'` by case on `w'.val.right` (mirror the closure cases): `.to true` → both sides `.to x₀` (`mul_to`); `.to false` → LHS reads the product's left-value `= w.left true * w'.left true = w'.left true`-if-it-is-a-reset... spell out: `w'.left true = .to y` (C2), product left-value `= a * .to y = .to y` → LHS `.to ↑y`; RHS `ψ w * .to ↑y = .to ↑y` ✓; `.id` → `w' = 1`-like (C3 forces left `.id`): product = `w` up to the constancy rewrites → LHS `ψ w`; RHS `ψ w * 1` ✓ (this case needs `WreathMonoid.ext`-style equality `w * w' = w` first, or argue componentwise inside `ψ`'s match — implementer latitude; the pinned fact is `w'.left b = .id ∀ b` and `w'.right = .id`).
  - `monoidMap_surj`: `.id`-image ← `1`; `.to x₀` ← `⟨⟨fun _ => .id, .to true⟩, C1 ✓, C2 vacuous (right .to true ≠ .to false — constructor injectivity on the Bool payload), C3 vacuous⟩`; `.to x` (`x ≠ x₀`) ← `⟨⟨fun _ => .to ⟨x, h⟩, .to false⟩, C1 ✓, C2 (`.to _ ≠ .id` ctor), C3 vacuous⟩`. Payload-discrimination note: `.to true ≠ .to false` needs `Resets.to.injEq`/`simp` — `decide` also works on `Resets Bool` (DecidableEq derived).
  - **equivariant**: `∀ (p : Y × Bool) (n), φ p ⊳ ψ n = φ (p ⊳ n)` — case on `n.val.right` (3 cases), each reducing by `wreath_act`, the `resetMonoid` act simp lemmas, and `if`-splitting on `p.2`; the `.to false` case uses C2's extraction (`n.left (p.2-value)` rewritten to `n.left true` by C1). All value-level; expect `show`/`rfl` at pair literals (the documented stall) — the mirror kit + `wreath_act` fire on bound-variable forms.

- [ ] **Step 1: Skeleton with the submonoid COMPLETE (carrier + one_mem + mul_mem) and the other four fields sorried (RED).** Transcribe the construction above; the closure proof is the mathematical heart — write it first and get it green before touching the rest.

- [ ] **Step 2: Fill monoidMap + surjectivities + equivariance (GREEN).** All chains are pinned above; only tactic order is discovery. Hard gate: no sorry at task end. Escalation latitude: the ψ-match may be restructured (e.g. two-level match, or `if`-based on `Decidable` right-cases) provided the three-family mapping (`1↦id`, `(_, to true)↦to x₀`, `(to y, to false)↦to ↑y`) and the theorem statement are unchanged.

- [ ] **Step 3: Sanity example + build + commit**

```lean
example : resetMonoid Bool ≺ resetMonoid {b : Bool // b ≠ true} ≀ flipFlop :=
  reset_split Bool true
```

(Instance `Nonempty {b // b ≠ true}` should be found via `⟨⟨false, by decide⟩⟩` — if not automatic, provide it as a local `haveI`/instance in the example.)

```bash
lake build 2>&1 | tail -5 && (grep -rn "sorry" KRTheory/ KRTheory.lean; test $? -eq 1 && echo clean)
git add KRTheory/TransMon/Reset.lean
git commit -m "Add reset split lemma"
```

---

### Task 6: reset_div_flipFlops + acceptance

**Files:**
- Modify: `KRTheory/TransMon/Reset.lean` (append)
- Modify: `blueprint/src/chapters/bar.tex`, `reset.tex` (`\leanok` marks)

**Interfaces:**
- Consumes: `reset_split` (T5); `div_wreathList_singleton`, `StrongDivides.wreath`, `wreathList_append`, `StrongDivides.trans/refl` (M3); `List.replicate` lemmas.
- Produces: `theorem KRTheory.TransMon.resetMonoid_div_flipFlop_of_card_one (X : Type) [Fintype X] (h : Fintype.card X = 1) : resetMonoid X ≺ flipFlop`; `theorem KRTheory.TransMon.reset_div_flipFlops (X : Type) [Fintype X] [Nonempty X] : ∃ n : ℕ, resetMonoid X ≺ wreathList (List.replicate n flipFlop)`.

- [ ] **Step 1: The card-one base (RED→GREEN)**

```lean
/-- A one-point reset monoid divides the flip-flop: collapse both
resets onto the point. Base case of DKS 2.12. -/
theorem resetMonoid_div_flipFlop_of_card_one (X : Type) [Fintype X]
    (h : Fintype.card X = 1) : resetMonoid X ≺ flipFlop := by
  obtain ⟨x⋆, hx⟩ := Fintype.card_eq_one_iff.mp h
  exact ⟨{ toSubmonoid := ⊤
           stateMap := fun _ => x⋆
           monoidMap := { toFun := fun r => match (r : Resets Bool) with
                            | .id => .id | .to _ => .to x⋆
                          map_one' := rfl
                          map_mul' := fun a b => by
                            cases hb : (b : Resets Bool) <;>
                              cases ha : (a : Resets Bool) <;>
                              simp_all }   -- 4 tiny cases; latitude
           stateMap_surj := fun x => ⟨(default : Bool), (hx x).symm⟩
           monoidMap_surj := fun r => by
             cases r with
             | id => exact ⟨1, rfl⟩
             | to y => exact ⟨⟨.to true, trivial⟩, by simp [hx y]⟩
           equivariant := fun b n => by
             cases hn : (n : Resets Bool) <;> simp_all [hx] }⟩
```

(Every state equals `x⋆` via `hx`; scripts have latitude, statement fixed. `stateMap_surj` needs a `Bool` inhabitant — `true` works if `default` fights.)

- [ ] **Step 2: The induction (RED→GREEN)**

```lean
/-- DKS Lemma 2.12: every reset monoid on a nonempty finite state set
divides an iterated wreath product of flip-flops. Existential in the
factor count; nonemptiness is necessary (empty-state monoids divide
only empty-state ones). -/
theorem reset_div_flipFlops (X : Type) [Fintype X] [Nonempty X] :
    ∃ n : ℕ, resetMonoid X ≺ wreathList (List.replicate n flipFlop) := by
  generalize hcard : Fintype.card X = N
  induction N using Nat.strong_induction_on generalizing X with
  | _ N ih =>
    rcases Nat.lt_or_ge N 2 with hN | hN
    · -- N = 1 (N = 0 contradicts Nonempty: Fintype.card_pos gives card ≥ 1)
      have h1 : Fintype.card X = 1 := by
        have := Fintype.card_pos (α := X); omega
      -- List.replicate 1 flipFlop = [flipFlop] is definitional, so the
      -- singleton lemma's type matches the goal directly:
      exact ⟨1, (resetMonoid_div_flipFlop_of_card_one X h1).trans
        (div_wreathList_singleton flipFlop)⟩
    · obtain ⟨x₀⟩ := ‹Nonempty X›
      haveI : Nonempty {x : X // x ≠ x₀} := by
        -- card ≥ 2 gives a second element
        sorry -- REPLACE: Fintype.exists_ne / one_lt_card_iff route
      obtain ⟨n, hn⟩ := ih (Fintype.card {x : X // x ≠ x₀}) (by
        -- card {x // x ≠ x₀} = N - 1 < N
        sorry) {x : X // x ≠ x₀} rfl
      refine ⟨n + 1, ?_⟩
      -- Rewrite the GOAL first (no Trans instance exists for mixing `=`
      -- into a `≺` calc): replicate (n+1) a = replicate n a ++ [a].
      rw [List.replicate_succ']
      calc resetMonoid X
          ≺ resetMonoid {x : X // x ≠ x₀} ≀ flipFlop := reset_split X x₀
        _ ≺ wreathList (List.replicate n flipFlop) ≀
              wreathList [flipFlop] :=
            hn.wreath (div_wreathList_singleton flipFlop)
        _ ≺ wreathList (List.replicate n flipFlop ++ [flipFlop]) :=
            wreathList_append _ _
```

(If `List.replicate_succ'` is oriented the other way in this Mathlib rev, use `← List.replicate_succ'` or `show` the rewritten goal; the list identity `replicate (n+1) a = replicate n a ++ [a]` is the fixed content.)

The two inline discovery sorries (second-element existence; the card arithmetic `Fintype.card {x // x ≠ x₀} = N - 1 < N`) are standard Mathlib facts (`Fintype.one_lt_card_iff_nontrivial`/`exists_ne`, `Fintype.card_subtype_compl` or a `Fintype.card_congr` with `Equiv.subtypeEquiv`… resolve via `exact?`/loogle; `omega` closes the arithmetic). The base-case `by simp` closes `wreathList [flipFlop] = wreathList (replicate 1 flipFlop)` (`List.replicate_one`). `omega_or_interval` is a placeholder name — use `omega` with `Fintype.card_pos`. **Hard gate: no sorry at task end.** If `Nat.strong_induction_on ... generalizing X` fights (motive over types), restructure as a standalone auxiliary lemma `∀ N, ∀ (X : Type) [Fintype X] [Nonempty X], Fintype.card X = N → ∃ n, ...` proved by `Nat.strong_induction_on`, then apply — statement of the public theorem unchanged.

- [ ] **Step 3: Acceptance examples + blueprint marks**

```lean
example : ∃ n, resetMonoid (Fin 5) ≺ wreathList (List.replicate n flipFlop) :=
  reset_div_flipFlops (Fin 5)
example : ∃ n, flipFlop ≺ wreathList (List.replicate n flipFlop) :=
  reset_div_flipFlops Bool
-- The factor list is all-flip-flops by construction — the shape M8 needs:
example (n : ℕ) (F : TransMon) (hF : F ∈ List.replicate n flipFlop) :
    F = flipFlop := List.eq_of_mem_replicate hF
```

Blueprint: add `\leanok` to `def:bar`, `lem:bar-divides`, `def:resets`, `def:flipflop`, `lem:reset-split`, `lem:reset-div-flipflops` (and `rem:bar-degenerate` needs none — remarks carry no `\lean`).

- [ ] **Step 4: Acceptance sweep + commit**

```bash
lake build 2>&1 | tail -3
grep -rn "sorry\|admit\|native_decide" KRTheory/ KRTheory.lean; test $? -eq 1 && echo "no escape hatches"
```

Scratch axiom check (`KRTheory/Scratch.lean`, NOT committed, deleted after):

```lean
import KRTheory.TransMon.Reset
import KRTheory.TransMon.Bar
open KRTheory KRTheory.TransMon
#print axioms KRTheory.TransMon.bar_divides
#print axioms KRTheory.TransMon.reset_split
#print axioms KRTheory.TransMon.reset_div_flipFlops
```

Expected: each a subset of `Classical.choice, propext, Quot.sound`. Then:

```bash
lake env lean KRTheory/Scratch.lean && rm KRTheory/Scratch.lean
git status --short   # only Reset.lean + the two .tex files
git add KRTheory/TransMon/Reset.lean blueprint/src/chapters/bar.tex blueprint/src/chapters/reset.tex
git commit -m "Prove DKS 2.12 completing milestone 4"
```

---

## Self-review record (per writing-plans skill)

- **Spec coverage (M4 = spec §3.4 + §3.5 + §7 row 4):** bar def/instances/`bar_divides` = Tasks 2–3; degenerate audit = Task 2's trivialTM example + blueprint remark; `bar_mono` explicitly skipped with spec note (refinement 6, Task 1); resets/flip-flop = Task 4; DKS 2.12 = Tasks 5–6; blueprint chapters+marks = Tasks 1, 6; housekeeping rulings from M3 = Task 1. Acceptance row "2.12 proved" = Task 6's sweep.
- **Placeholder scan:** discovery points are confined to Task 3's iso-vs-mk' route (both fully specified), Task 5's tactic ordering (constructions pinned), and Task 6's two standard-Mathlib-fact sorries + the `omega_or_interval` placeholder (all explicitly flagged REPLACE with named candidate lemmas, gated by hard no-sorry checks). No TBDs elsewhere.
- **Type consistency:** `BarMonoid`/`Resets` constructor names (`of`/`reset`; `id`/`to`) used identically across Tasks 2–6 and the blueprint; `reset_split`'s statement in Task 5 matches Task 6's `calc` use and the blueprint; `Covering.sect`/`stateMap_sect` public names (Task 1) match what `WreathDivision.lean` will call after the move; the 27-example uses M3's `WreathMonoid.natCard` exactly as exported.
- **Computability audit:** no `noncomputable` anywhere in Bar/Reset (Fintypes via `ofEquiv` from computable `Sum`/`Option` instances; `DecidableEq` derived). `Covering.sect` (Task 1) is `noncomputable` (choice) — correctly marked.
- **Edge audit:** `[Nonempty X]` threading — `reset_split` needs `Nonempty Y` (stateMap surjectivity at x₀), supplied in Task 6's induction from `card ≥ 2`; the card-one base avoids Y entirely; `Nonempty X` in 2.12 is refinement 3, recorded in spec + blueprint.
