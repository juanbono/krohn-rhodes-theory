# Krohn–Rhodes Milestone 3 (Wreath Products) Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Build the wreath product of transformation monoids with its division calculus: the `WreathMonoid`/`wreath` definitions, trivial absorption, monotonicity of `≺` under `≀`, one-directional associativity, and the `wreathList` fold with its append lemma.

**Architecture:** Two new files. `KRTheory/TransMon/Wreath.lean` holds the definitional layer (structure, instances, simp kit, `wreath`, `wreathList`); `KRTheory/TransMon/WreathDivision.lean` holds the division lemmas (absorption, monotonicity, associativity, append). This splits spec §4.3's single `Wreath.lean` row into two files for task isolation — an implementation refinement (declaration list unchanged); Task 1 amends the spec table to match. A small `Covering.extMap` API is added to `Division.lean` (the spec's "lemma kit grows on demand" policy, final M0–2 review recommendation).

**Tech Stack:** Lean 4 (toolchain pinned by Mathlib), lake, Mathlib. Base code: branch `milestones-0-2` at `3a074ae` (or `main` after the user merges — executor branches from whichever holds the M0–2 code).

**Spec:** `docs/superpowers/specs/2026-08-17-krohn-rhodes-formalization-design.md` — §3.3 (mathematics), §4.1–§4.3 (architecture), §7 row 3 (acceptance: monoid instance, monotonicity, `wreath_assoc_div`, `wreathList_append`).

## Global Constraints

- All Lean code inside `namespace KRTheory` (and `TransMon` where noted); notation `scoped`.
- Carriers in `Type`; no universe polymorphism; no `DecidableEq` bundling (spec §4.1).
- `noncomputable` is allowed exactly where `Fintype` of a function type forces it (`Fintype (WreathMonoid S T)`, `wreath`, `wreathList`, `Covering.extMap`); the `Monoid (WreathMonoid S T)` instance itself must stay computable.
- Docstrings on every new public declaration **including structure fields**; module docstrings cite [DKS §2.2].
- Every definitional file ends with `example` sanity checks; at least one example per twisted operation must genuinely discriminate the twist direction (guard-comment stating which wrong definition it kills) — M0–2 final-review discipline.
- No `sorry` in committed code at the end of any task; commit messages plain, no trailers.
- Carried from M0–2: defs like `regular`/`wreath` are semireducible — `show`-restatements unstick stalled elaboration; Mathlib name drift resolved via `exact?`/loogle with the math fixed; extra narrowly-scoped `Mathlib.*` imports allowed (document them).
- Formalization-TDD discipline as in the M0–2 plan: RED = statements + `sorry` + examples elaborate; GREEN = proofs in, `grep -rn "sorry" KRTheory/ KRTheory.lean` empty, build clean.

## Mathematical target (fixes notation for all tasks)

For S = (X, M), T = (Y, N):

```
S ≀ T := (X × Y,  W)  where W = {left : Y → M, right : N} with
(w * w').left y  = w.left y * w'.left (y ·_T w.right)      -- the TWIST: w' reads the state after w.right
(w * w').right   = w.right * w'.right
(x, y) ⊳ w       = (x ·_S w.left y,  y ·_T w.right)
```

Division calculus: `trivialTM ≀ T ≺ T`; `S ≺ S ≀ trivialTM`; monotonicity `S₁≺T₁ → S₂≺T₂ → S₁≀S₂ ≺ T₁≀T₂`; `(P ≀ Q) ≀ R ≺ P ≀ (Q ≀ R)`; `wreathList = List.foldr wreath trivialTM`; `wreathList L₁ ≀ wreathList L₂ ≺ wreathList (L₁ ++ L₂)`.

---

### Task 1: Blueprint chapter + spec table amendment

**Files:**
- Create: `blueprint/src/chapters/wreath.tex`
- Modify: `blueprint/src/content.tex` (add `\input{chapters/wreath}` after the division input)
- Modify: `docs/superpowers/specs/2026-08-17-krohn-rhodes-formalization-design.md` (§4.3 table: split the Wreath row)

**Interfaces:**
- Produces: the `\lean{}` name contract for Tasks 2–8: `KRTheory.TransMon.WreathMonoid`, `KRTheory.TransMon.wreath`, `KRTheory.TransMon.WreathMonoid.natCard`, `KRTheory.TransMon.wreathList`, `KRTheory.TransMon.trivial_wreath_div`, `KRTheory.TransMon.div_wreath_trivial`, `KRTheory.TransMon.Covering.wreath`, `KRTheory.TransMon.StrongDivides.wreath`, `KRTheory.TransMon.wreath_assoc_div`, `KRTheory.TransMon.wreathList_append`.

- [ ] **Step 1: Write `blueprint/src/chapters/wreath.tex`**

```latex
\chapter{Wreath products}\label{ch:wreath}

The wreath product composes two transformation monoids into a cascade:
the back machine $T$ reads the input directly, while the front machine
$S$ is driven by a function of the back machine's current state. It is
the composition operation of the Krohn--Rhodes theorem.

\begin{definition}[Wreath product; DKS §2.2]\label{def:wreath}
  \lean{KRTheory.TransMon.WreathMonoid, KRTheory.TransMon.wreath}
  \uses{def:transmon}
  For $S = (X, M)$ and $T = (Y, N)$, the wreath product is
  $S \wr T := (X \times Y,\; W)$ where $W$ has carrier $M^Y \times N$,
  multiplication
  \[ (f, n)(g, k) \;=\; \bigl(y \mapsto f(y)\,g(y \cdot n),\; nk\bigr), \]
  and right action $(x, y) \cdot (f, n) = (x \cdot f(y),\; y \cdot n)$.
  In a product the left factor acts first, so $g$ is evaluated at the
  state \emph{after} $n$ has acted.
\end{definition}

\begin{lemma}[Cardinality]\label{lem:wreath-card}
  \lean{KRTheory.TransMon.WreathMonoid.natCard}\uses{def:wreath}
  $|W| = |M|^{|Y|}\cdot|N|$.
\end{lemma}
\begin{proof}
  $W$ is (as a set) the product $M^Y \times N$.
\end{proof}

\begin{definition}[Iterated wreath product]\label{def:wreathList}
  \lean{KRTheory.TransMon.wreathList}\uses{def:wreath,def:trivialTM}
  For a list $[T_1, \dots, T_k]$ of transformation monoids,
  $\mathrm{wreathList}$ is the right fold
  $T_1 \wr (T_2 \wr (\cdots \wr (T_k \wr \mathbf{1})))$.
  Fixing one association avoids carrying an associativity isomorphism
  through every statement.
\end{definition}

\begin{lemma}[Trivial absorption]\label{lem:wreath-trivial}
  \lean{KRTheory.TransMon.trivial_wreath_div,
        KRTheory.TransMon.div_wreath_trivial}
  \uses{def:wreath,def:trivialTM,def:sdiv}
  $\mathbf{1} \wr T \prec T$ and $S \prec S \wr \mathbf{1}$.
\end{lemma}
\begin{proof}
  For the first: the monoid part of $\mathbf{1} \wr T$ is $N$ in
  disguise; cover with the identity data. For the second: project
  states by $\mathrm{fst}$ and evaluate the function component at the
  unique point.
\end{proof}

\begin{lemma}[Monotonicity]\label{lem:wreath-mono}
  \lean{KRTheory.TransMon.Covering.wreath,
        KRTheory.TransMon.StrongDivides.wreath}
  \uses{def:wreath,def:sdiv}
  If $S_1 \prec T_1$ and $S_2 \prec T_2$ then
  $S_1 \wr S_2 \prec T_1 \wr T_2$.
\end{lemma}
\begin{proof}
  Let $(\varphi_i, N_i', \psi_i)$ witness $S_i \prec T_i$. Cover
  $S_1 \wr S_2$ by the submonoid of pairs $(F, n)$ with
  $n \in N_2'$, $F(y) \in N_1'$ for all $y$, and $F$
  \emph{fiber-compatible}: $\varphi_2(y) = \varphi_2(y')$ implies
  $\psi_1(F(y)) = \psi_1(F(y'))$. Closure under products uses the
  equivariance of the second covering. Fix a section
  $\sigma$ of $\varphi_2$; map $(F, n) \mapsto
  (s \mapsto \psi_1(F(\sigma(s))),\, \psi_2(n))$. The morphism
  property reduces, via equivariance and fiber-compatibility, to
  $\varphi_2(\sigma(s) \cdot n) = \varphi_2(\sigma(s \cdot \psi_2 n))$;
  surjectivity chooses preimages pointwise; equivariance of the new
  covering is fiber-compatibility at $\varphi_2(\sigma(\varphi_2 y)) =
  \varphi_2(y)$.
\end{proof}

\begin{lemma}[Associativity up to division]\label{lem:wreath-assoc}
  \lean{KRTheory.TransMon.wreath_assoc_div}\uses{def:wreath,def:sdiv}
  $(P \wr Q) \wr R \;\prec\; P \wr (Q \wr R)$.
\end{lemma}
\begin{proof}
  Currying: both monoids have carrier
  $M_P^{\,X_Q \times X_R} \times M_Q^{\,X_R} \times M_R$ up to the
  evident bijections, and the twisted multiplications agree under this
  identification; states correspond by re-association. The covering
  uses the full monoid and these bijections.
\end{proof}

\begin{lemma}[Append]\label{lem:wreathList-append}
  \lean{KRTheory.TransMon.wreathList_append}
  \uses{def:wreathList,lem:wreath-trivial,lem:wreath-mono,lem:wreath-assoc,lem:sdiv-preorder}
  $\mathrm{wreathList}(L_1) \wr \mathrm{wreathList}(L_2) \prec
   \mathrm{wreathList}(L_1 \mathbin{+\!\!+} L_2)$.
\end{lemma}
\begin{proof}
  Induction on $L_1$: the base case is trivial absorption; the cons
  case re-associates with Lemma~\ref{lem:wreath-assoc} and applies
  monotonicity and transitivity.
\end{proof}
```

- [ ] **Step 2: Register the chapter**

In `blueprint/src/content.tex`, after `\input{chapters/division}` add:

```latex
\input{chapters/wreath}
```

- [ ] **Step 3: Amend the spec's §4.3 table**

In the design doc, replace the row

```
| `TransMon/Wreath.lean` | `wreath` (`≀`) + monoid & action instances, `wreath_div_wreath`, `wreath_assoc_div`, `trivialTM` absorption, `wreathList`, `wreathList_append` |
```

with

```
| `TransMon/Wreath.lean` | `WreathMonoid` + monoid instance & simp kit, `wreath` (`≀`) + action, `WreathMonoid.natCard`, `wreathList` |
| `TransMon/WreathDivision.lean` | `trivialTM` absorption (`trivial_wreath_div`, `div_wreath_trivial`), `Covering.wreath` / `StrongDivides.wreath` (monotonicity), `wreath_assoc_div`, `wreathList_append` |
```

and in `Division.lean`'s row append: `, Covering.extMap kit (added in M3)`.

- [ ] **Step 4: Compile check (conditional) and commit**

```bash
command -v latexmk >/dev/null && (cd blueprint/src && latexmk -pdf -interaction=nonstopmode print.tex && latexmk -c) || echo "latexmk not installed - skip ok"
git add blueprint docs/superpowers/specs
git commit -m "Add wreath product blueprint chapter"
```

---

### Task 2: WreathMonoid — structure, monoid instance, simp kit, cardinality

**Files:**
- Create: `KRTheory/TransMon/Wreath.lean`
- Modify: `KRTheory.lean` (add `import KRTheory.TransMon.Wreath`)

**Interfaces:**
- Consumes: `TransMon` (Basic.lean).
- Produces (used by every later task):
  - `structure KRTheory.TransMon.WreathMonoid (S T : TransMon) : Type` with fields `left : T.X → S.M`, `right : T.M`
  - `@[ext] WreathMonoid.ext` (two-field extensionality)
  - computable `instance : Monoid (WreathMonoid S T)` with the twisted multiplication
  - `@[simp]` lemmas: `WreathMonoid.mul_left : (w * w').left y = w.left y * w'.left (T.act y w.right)`, `WreathMonoid.mul_right : (w * w').right = w.right * w'.right`, `WreathMonoid.one_left : (1 : WreathMonoid S T).left y = 1`, `WreathMonoid.one_right : (1 : WreathMonoid S T).right = 1`
  - `WreathMonoid.equivProd : WreathMonoid S T ≃ (T.X → S.M) × T.M`
  - `instance : Finite (WreathMonoid S T)`
  - `theorem WreathMonoid.natCard : Nat.card (WreathMonoid S T) = Nat.card S.M ^ Nat.card T.X * Nat.card T.M`

- [ ] **Step 1: Create the file with statements + sorries + examples (RED)**

```lean
import KRTheory.TransMon.Basic

/-!
# Wreath products of transformation monoids

The wreath product `S ≀ T` [DKS §2.2]: states `S.X × T.X`, monoid
`WreathMonoid S T` (functions `T.X → S.M` twisted by `T.M`). The monoid
is a fresh structure rather than the raw product type `(T.X → S.M) × T.M`
because the multiplication is twisted — defining it on the product type
would collide with Mathlib's componentwise `Prod.instMonoid` (instance
diamond). Same design as Mathlib's `RegularWreathProduct`.
-/

namespace KRTheory
namespace TransMon

/-- The monoid part of the wreath product `S ≀ T`: carrier
`(T.X → S.M) × T.M` as a fresh structure (see module docstring), with
multiplication `(f,n)(g,k) = (fun y => f y * g (y·n), n*k)`. [DKS §2.2] -/
@[ext]
structure WreathMonoid (S T : TransMon) : Type where
  /-- The front-machine component: an `S.M`-element for each `T`-state. -/
  left : T.X → S.M
  /-- The back-machine component. -/
  right : T.M

namespace WreathMonoid

variable {S T : TransMon}

instance : Monoid (WreathMonoid S T) where
  mul w w' := ⟨fun y => w.left y * w'.left (T.act y w.right), w.right * w'.right⟩
  one := ⟨fun _ => 1, 1⟩
  mul_assoc w₁ w₂ w₃ := sorry
  one_mul w := sorry
  mul_one w := sorry

@[simp] theorem mul_left (w w' : WreathMonoid S T) (y : T.X) :
    (w * w').left y = w.left y * w'.left (T.act y w.right) := rfl

@[simp] theorem mul_right (w w' : WreathMonoid S T) :
    (w * w').right = w.right * w'.right := rfl

@[simp] theorem one_left (y : T.X) : (1 : WreathMonoid S T).left y = 1 := rfl

@[simp] theorem one_right : (1 : WreathMonoid S T).right = (1 : T.M) := rfl

/-- `WreathMonoid` is, as a type, the product `(T.X → S.M) × T.M`. -/
def equivProd : WreathMonoid S T ≃ (T.X → S.M) × T.M where
  toFun w := (w.left, w.right)
  invFun p := ⟨p.1, p.2⟩
  left_inv w := rfl
  right_inv p := rfl

instance : Finite (WreathMonoid S T) := Finite.of_equiv _ equivProd.symm

/-- `|S ≀ T| = |S.M| ^ |T.X| * |T.M|` at the monoid level. -/
theorem natCard :
    Nat.card (WreathMonoid S T) =
      Nat.card S.M ^ Nat.card T.X * Nat.card T.M := sorry

end WreathMonoid

-- Sanity checks (spec §6).
-- Twist guard: with w = ⟨const 1, 2⟩ and w' = ⟨id, 1⟩ over the regular
-- representation of ZMod 3, (w * w').left 1 = 1 * id (1 * 2) = 2.
-- The UNtwisted componentwise product would give 1 * id 1 = 1, and the
-- wrong-sided twist (evaluating w.left at y · w'.right) would give
-- 1 * id 1 = 1 as well: this example kills both wrong definitions.
example :
    ((⟨fun _ => 1, 2⟩ : WreathMonoid (regular (ZMod 3)) (regular (ZMod 3))) *
      ⟨fun y => y, 1⟩).left 1 = 2 := rfl
example :
    ((⟨fun _ => 1, 2⟩ : WreathMonoid (regular (ZMod 3)) (regular (ZMod 3))) *
      ⟨fun y => y, 1⟩).right = 2 := rfl
example :
    Nat.card (WreathMonoid (regular (ZMod 2)) (regular (ZMod 2))) = 8 := by
  simp [WreathMonoid.natCard, Nat.card_zmod]

end TransMon
end KRTheory
```

Add `import KRTheory.TransMon.Wreath` to `KRTheory.lean`. Build: expect exactly four sorry warnings (three monoid laws + natCard); the twist-guard examples must already pass (`rfl` forces the multiplication as defined). If the anonymous-constructor examples fail to elaborate, ascribe explicitly (`(⟨fun _ => (1 : ZMod 3), (2 : ZMod 3)⟩ : WreathMonoid _ _)`).

- [ ] **Step 2: Prove the monoid laws (GREEN part 1)**

```lean
  mul_assoc w₁ w₂ w₃ := by
    ext y
    · simp [mul_assoc, TransMon.act_mul]
    · simp [mul_assoc]
  one_mul w := by ext y <;> simp
  mul_one w := by ext y <;> simp
```

Watchpoints: `ext` on `WreathMonoid` splits into a function-component goal (needs `funext`, which the `@[ext]` lemma should produce as a `∀ y` goal — if not, `refine WreathMonoid.ext _ _ (funext fun y => ?_) ?_`). The `left` goal of `mul_assoc` is `(w₁.left y * w₂.left (y·r₁)) * w₃.left (y·(r₁*r₂)) = w₁.left y * (w₂.left (y·r₁) * w₃.left ((y·r₁)·r₂))` — closed by `mul_assoc` plus `act_mul` (both simp). Since the `Monoid` instance's `mul` is defined inside the instance, `simp` may need the definitional lemmas: if the `@[simp]` theorems in Step 1 are stated AFTER the instance (they are), use `simp only [mul_left, mul_right, ...]`-style — but note those lemmas are proved `rfl` against this very instance, so prove the laws with the field formulas directly (`show` the unfolded equation) if simp loops.

- [ ] **Step 3: Prove natCard (GREEN part 2)**

```lean
theorem natCard :
    Nat.card (WreathMonoid S T) =
      Nat.card S.M ^ Nat.card T.X * Nat.card T.M := by
  rw [Nat.card_congr (equivProd (S := S) (T := T)), Nat.card_prod, Nat.card_fun]
```

Name-drift watch: `Nat.card_fun : Nat.card (α → β) = Nat.card β ^ Nat.card α` (needs `Finite α` — available). If the name differs, `exact?` on the goal `Nat.card (T.X → S.M) = Nat.card S.M ^ Nat.card T.X`. If the pow orientation is flipped, adjust with `mul_comm`/statement stays as written (fix the proof, not the statement).

- [ ] **Step 4: Build clean + no sorry**

```bash
lake build 2>&1 | tail -5 && (grep -rn "sorry" KRTheory/ KRTheory.lean; test $? -eq 1 && echo "clean")
```

- [ ] **Step 5: Commit**

```bash
git add KRTheory.lean KRTheory/TransMon/Wreath.lean
git commit -m "Add wreath monoid with twisted multiplication"
```

---

### Task 3: wreath (≀), action, wreathList

**Files:**
- Modify: `KRTheory/TransMon/Wreath.lean` (append inside `namespace TransMon`, after `end WreathMonoid` and the examples)

**Interfaces:**
- Consumes: `WreathMonoid` + simp kit (Task 2); `trivialTM`, `Fintype.ofFinite`.
- Produces:
  - `noncomputable def KRTheory.TransMon.wreath (S T : TransMon) : TransMon` — states `S.X × T.X`, monoid `WreathMonoid S T`; scoped infix `≀` at precedence 60, **right-associative** (`infixr`), matching the `foldr` association
  - `@[simp] theorem wreath_act (p : (S ≀ T).X) (w : (S ≀ T).M) : (S ≀ T).act p w = (S.act p.1 (w.left p.2), T.act p.2 w.right)`
  - `noncomputable def KRTheory.TransMon.wreathList : List TransMon → TransMon := fun L => L.foldr wreath trivialTM`
  - `@[simp] wreathList_nil : wreathList [] = trivialTM`; `@[simp] wreathList_cons : wreathList (S :: L) = S ≀ wreathList L`

- [ ] **Step 1: Append definitions + statements (RED)**

```lean
/-- The wreath product of transformation monoids [DKS §2.2]: the cascade
of `S` driven by `T`. `noncomputable` only because `Fintype` of the
function component needs `DecidableEq T.X`, which `TransMon` deliberately
does not carry (spec §4.1); the algebra itself is computable and `rfl`
still evaluates actions and products. -/
noncomputable def wreath (S T : TransMon) : TransMon where
  X := S.X × T.X
  M := WreathMonoid S T
  fintypeM := Fintype.ofFinite _
  act p w := (S.act p.1 (w.left p.2), T.act p.2 w.right)
  act_one p := by simp
  act_mul p w w' := by simp [TransMon.act_mul]

@[inherit_doc]
scoped infixr:60 " ≀ " => TransMon.wreath

@[simp] theorem wreath_act {S T : TransMon} (p : (S ≀ T).X) (w : (S ≀ T).M) :
    (S ≀ T).act p w = (S.act p.1 (w.left p.2), T.act p.2 w.right) := rfl

/-- Iterated wreath product over a list, right fold with base `trivialTM`:
`wreathList [T₁, T₂, T₃] = T₁ ≀ (T₂ ≀ (T₃ ≀ trivialTM))`. Fixing the
association once avoids an associativity isomorphism in every statement
(spec §3.3). -/
noncomputable def wreathList : List TransMon → TransMon :=
  fun L => L.foldr wreath trivialTM

@[simp] theorem wreathList_nil : wreathList [] = trivialTM := rfl

@[simp] theorem wreathList_cons (S : TransMon) (L : List TransMon) :
    wreathList (S :: L) = S ≀ wreathList L := rfl

-- Sanity checks (spec §6). Action evaluation stays rfl-checkable even
-- though `wreath` is noncomputable (defeq is unaffected).
-- Guard: w.left must be evaluated at the CURRENT back-state p.2 = 2,
-- giving (1 * id 2, 2*2) = (2, 1). A wrong definition evaluating w.left
-- at the UPDATED state p.2·w.right = 4 = 1 would give (1 * id 1, 1) =
-- (1, 1) ≠ (2, 1): this example kills that transposition.
example :
    ((regular (ZMod 3)) ≀ (regular (ZMod 3))).act (1, 2) ⟨fun y => y, 2⟩ =
      (2, 1) := rfl
```

Note on the action guard example: with `p = (1, 2)`, `w = ⟨id, 2⟩` over `regular (ZMod 3)`: correct value `(1 * id 2, 2 * 2) = (2, 1)`. A wrong definition evaluating `w.left` at the *updated* state `p.2 · w.right = 4 = 1` gives `(1 * 1, 1) = (1, 1) ≠ (2, 1)` — state the guard in the comment. If `rfl` stalls on the noncomputable def, use `show _ = _ from rfl` or `by simp [wreath]` — the values are fixed, only the script may change.

Elaboration watchpoints: `wreath`'s `fintypeX`/`monoidM` fields should be found by instance search (`Prod` Fintype from the bundled instance fields; `Monoid (WreathMonoid S T)` from Task 2) — supply explicitly (`fintypeX := inferInstance`) only if elaboration fails. `act_one`/`act_mul` proofs: goals are pairs — `Prod.ext` then simp (`simp` alone should close via `Prod.mk.injEq`, `act_one`, `act_mul`, `one_left`, `one_right`, `mul_left`, `mul_right`).

- [ ] **Step 2: Build; iterate to GREEN; no sorry**

```bash
lake build 2>&1 | tail -10 && (grep -rn "sorry" KRTheory/ KRTheory.lean; test $? -eq 1 && echo "clean")
```

- [ ] **Step 3: Commit**

```bash
git add KRTheory/TransMon/Wreath.lean
git commit -m "Add wreath product and iterated wreath list"
```

---

### Task 4: Trivial absorption lemmas

**Files:**
- Create: `KRTheory/TransMon/WreathDivision.lean`
- Modify: `KRTheory.lean` (add `import KRTheory.TransMon.WreathDivision`)

**Interfaces:**
- Consumes: `wreath`/`≀`/`wreath_act`/simp kit (Tasks 2–3); `Covering`, `StrongDivides`, `≺` (Division.lean); `trivialTM`.
- Produces:
  - `theorem KRTheory.TransMon.trivial_wreath_div (T : TransMon) : trivialTM ≀ T ≺ T`
  - `theorem KRTheory.TransMon.div_wreath_trivial (S : TransMon) : S ≺ S ≀ trivialTM`
  - `theorem KRTheory.TransMon.div_wreathList_singleton (S : TransMon) : S ≺ wreathList [S]`

- [ ] **Step 1: Create file, statements + sorries + examples (RED)**

```lean
import KRTheory.TransMon.Wreath
import KRTheory.TransMon.Division

/-!
# Division calculus of wreath products

Absorption of the trivial factor, monotonicity of `≺` under `≀`,
one-directional associativity, and the `wreathList` append lemma
[DKS §2.2–§2.3]. These are the gluing lemmas of the Krohn–Rhodes
induction (spec §3.3, §3.9).
-/

namespace KRTheory
namespace TransMon

/-- Absorb a trivial front factor: `trivialTM ≀ T ≺ T`. -/
theorem trivial_wreath_div (T : TransMon) : trivialTM ≀ T ≺ T := sorry

/-- Any `S` divides its padding by a trivial back factor:
`S ≺ S ≀ trivialTM`. Base case of iterated-wreath gluing. -/
theorem div_wreath_trivial (S : TransMon) : S ≺ S ≀ trivialTM := sorry

/-- `S` divides the singleton iterated wreath. -/
theorem div_wreathList_singleton (S : TransMon) : S ≺ wreathList [S] := sorry

-- Sanity checks (spec §6).
example : trivialTM ≀ trivialTM ≺ trivialTM := trivial_wreath_div _
example : regular (ZMod 2) ≺ wreathList [regular (ZMod 2)] :=
  div_wreathList_singleton _

end TransMon
end KRTheory
```

- [ ] **Step 2: Prove all three (GREEN)**

```lean
theorem trivial_wreath_div (T : TransMon) : trivialTM ≀ T ≺ T :=
  ⟨{ toSubmonoid := ⊤
     stateMap := fun y => (PUnit.unit, y)
     monoidMap :=
       { toFun := fun n => ⟨fun _ => PUnit.unit, (n : T.M)⟩
         map_one' := by ext <;> rfl
         map_mul' := fun n m => by ext <;> rfl }
     stateMap_surj := fun p => ⟨p.2, by obtain ⟨u, y⟩ := p; rfl⟩
     monoidMap_surj := fun w =>
       ⟨⟨w.right, trivial⟩, by
         ext y <;> first | exact Subsingleton.elim _ _ | rfl⟩
     equivariant := fun y n => rfl }⟩

theorem div_wreath_trivial (S : TransMon) : S ≺ S ≀ trivialTM :=
  ⟨{ toSubmonoid := ⊤
     stateMap := Prod.fst
     monoidMap :=
       { toFun := fun w => (w : WreathMonoid S trivialTM).left PUnit.unit
         map_one' := rfl
         map_mul' := fun w w' => by
           -- ((w*w').left) unit = w.left unit * w'.left (unit ⊳ w.right)
           -- and unit ⊳ anything = unit in trivialTM
           simp }
     stateMap_surj := fun x => ⟨(x, PUnit.unit), rfl⟩
     monoidMap_surj := fun m => ⟨⟨⟨fun _ => m, PUnit.unit⟩, trivial⟩, rfl⟩
     equivariant := fun p w => by
       -- fst (p ⊳ w) = S.act p.1 (w.left p.2); p.2 = unit
       cases p; simp [wreath_act] }⟩

theorem div_wreathList_singleton (S : TransMon) : S ≺ wreathList [S] := by
  simpa using div_wreath_trivial S
```

Watchpoints: in `trivial_wreath_div`'s `monoidMap_surj`, the `ext` on the goal `⟨fun _ => unit, ↑⟨w.right, _⟩⟩ = w` needs the left components equal — every function into `PUnit` is `const unit`; if `rfl` balks use `funext y; exact Subsingleton.elim _ _` (or `PUnit.ext`-flavored lemmas). In `div_wreath_trivial`'s `map_mul'`, `trivialTM.act PUnit.unit _ = PUnit.unit` should be `rfl`/`Subsingleton.elim`; if the state that `w'.left` is evaluated at is not syntactically `PUnit.unit`, rewrite with `Subsingleton.elim` first. For `div_wreathList_singleton`: `wreathList [S]` unfolds via the simp lemmas to `S ≀ trivialTM` — `simpa` should transport; if not, `show S ≺ S ≀ trivialTM from div_wreath_trivial S` after `rw [wreathList_cons, wreathList_nil]`.

- [ ] **Step 3: Build clean + no sorry, commit**

```bash
lake build 2>&1 | tail -5 && (grep -rn "sorry" KRTheory/ KRTheory.lean; test $? -eq 1 && echo "clean")
git add KRTheory.lean KRTheory/TransMon/WreathDivision.lean
git commit -m "Add trivial-factor absorption for wreath products"
```

---

### Task 5: Covering.extMap kit

**Files:**
- Modify: `KRTheory/TransMon/Division.lean` (append inside `namespace TransMon`, after `Covering.comp`, before `namespace StrongDivides`'s examples region — any position after `Covering` is defined works; keep it adjacent to the other `Covering` API)

**Interfaces:**
- Consumes: `Covering` (fields toSubmonoid, stateMap, monoidMap, equivariant).
- Produces (Task 6 depends on exactly these):
  - `noncomputable def KRTheory.TransMon.Covering.extMap {S T : TransMon} (c : Covering S T) : T.M → S.M` — `c.monoidMap` totalized by 1 outside the submonoid
  - `theorem Covering.extMap_of_mem (c : Covering S T) {t : T.M} (h : t ∈ c.toSubmonoid) : c.extMap t = c.monoidMap ⟨t, h⟩`
  - `theorem Covering.extMap_coe (c : Covering S T) (n : c.toSubmonoid) : c.extMap ↑n = c.monoidMap n`
  - `theorem Covering.extMap_mul_of_mem (c : Covering S T) {a b : T.M} (ha : a ∈ c.toSubmonoid) (hb : b ∈ c.toSubmonoid) : c.extMap (a * b) = c.extMap a * c.extMap b`
  - `theorem Covering.act_extMap (c : Covering S T) {t : T.M} (h : t ∈ c.toSubmonoid) (y : T.X) : S.act (c.stateMap y) (c.extMap t) = c.stateMap (T.act y t)`

- [ ] **Step 1: Statements + sorries (RED)**

```lean
/-- `c.monoidMap` totalized to all of `T.M`, sending non-members to `1`.
Lets fiber-compatibility conditions be stated without dependent
membership proofs (used by wreath monotonicity). Classical `dite`. -/
noncomputable def Covering.extMap {S T : TransMon} (c : Covering S T) :
    T.M → S.M := fun t =>
  if h : t ∈ c.toSubmonoid then c.monoidMap ⟨t, h⟩ else 1

theorem Covering.extMap_of_mem {S T : TransMon} (c : Covering S T)
    {t : T.M} (h : t ∈ c.toSubmonoid) :
    c.extMap t = c.monoidMap ⟨t, h⟩ := sorry

theorem Covering.extMap_coe {S T : TransMon} (c : Covering S T)
    (n : c.toSubmonoid) : c.extMap ↑n = c.monoidMap n := sorry

theorem Covering.extMap_mul_of_mem {S T : TransMon} (c : Covering S T)
    {a b : T.M} (ha : a ∈ c.toSubmonoid) (hb : b ∈ c.toSubmonoid) :
    c.extMap (a * b) = c.extMap a * c.extMap b := sorry

theorem Covering.act_extMap {S T : TransMon} (c : Covering S T)
    {t : T.M} (h : t ∈ c.toSubmonoid) (y : T.X) :
    S.act (c.stateMap y) (c.extMap t) = c.stateMap (T.act y t) := sorry
```

- [ ] **Step 2: Proofs (GREEN)**

```lean
theorem Covering.extMap_of_mem ... := dif_pos h

theorem Covering.extMap_coe ... := by
  rw [c.extMap_of_mem n.2]   -- then close by Subtype.eta / rfl:
  -- goal c.monoidMap ⟨↑n, n.2⟩ = c.monoidMap n; `exact congrArg _ (Subtype.eta n _)` or rfl

theorem Covering.extMap_mul_of_mem ... := by
  rw [c.extMap_of_mem (mul_mem ha hb), c.extMap_of_mem ha, c.extMap_of_mem hb,
    ← map_mul]
  rfl   -- ⟨a*b, _⟩ = ⟨a,_⟩*⟨b,_⟩ in the submonoid: `rfl` or `Subtype.ext rfl`

theorem Covering.act_extMap ... := by
  rw [c.extMap_of_mem h]
  exact c.equivariant y ⟨t, h⟩
```

- [ ] **Step 3: Build clean + no sorry, commit**

```bash
lake build 2>&1 | tail -5 && (grep -rn "sorry" KRTheory/ KRTheory.lean; test $? -eq 1 && echo "clean")
git add KRTheory/TransMon/Division.lean
git commit -m "Add totalized covering monoid map"
```

---

### Task 6: Monotonicity — Covering.wreath and StrongDivides.wreath (the boss)

**Files:**
- Modify: `KRTheory/TransMon/WreathDivision.lean` (append after the absorption lemmas)

**Interfaces:**
- Consumes: `WreathMonoid` simp kit, `wreath_act` (Tasks 2–3); `Covering`, `extMap` kit (Task 5); `Function.surjInv` / `Function.surjInv_eq` (Mathlib).
- Produces:
  - `noncomputable def KRTheory.TransMon.Covering.wreath {S₁ T₁ S₂ T₂ : TransMon} (c₁ : Covering S₁ T₁) (c₂ : Covering S₂ T₂) : Covering (S₁ ≀ S₂) (T₁ ≀ T₂)`
  - `theorem KRTheory.TransMon.StrongDivides.wreath {S₁ T₁ S₂ T₂ : TransMon} (h₁ : S₁ ≺ T₁) (h₂ : S₂ ≺ T₂) : S₁ ≀ S₂ ≺ T₁ ≀ T₂`

Mathematics (blueprint `lem:wreath-mono`): the covering submonoid is the *fiber-compatible* pairs; note where each hypothesis is spent — closure under `*` spends `c₂.equivariant`; the morphism property spends equivariance + fiber-compatibility; covering-equivariance spends fiber-compatibility at `φ₂(σ(φ₂ y)) = φ₂ y`.

- [ ] **Step 1: Skeleton with the submonoid complete and the rest sorried (RED)**

```lean
/-- The wreath product of two coverings: witnesses monotonicity of `≺`
under `≀` (blueprint lem:wreath-mono). The submonoid consists of the
*fiber-compatible* elements: the back component covers via `c₂`, every
front value lies in `c₁`'s submonoid, and the front function descends
along `c₂.stateMap`-fibers up to `c₁.extMap`. -/
noncomputable def Covering.wreath {S₁ T₁ S₂ T₂ : TransMon}
    (c₁ : Covering S₁ T₁) (c₂ : Covering S₂ T₂) :
    Covering (S₁ ≀ S₂) (T₁ ≀ T₂) where
  toSubmonoid :=
    { carrier := { w | w.right ∈ c₂.toSubmonoid ∧
        (∀ y, w.left y ∈ c₁.toSubmonoid) ∧
        ∀ y y', c₂.stateMap y = c₂.stateMap y' →
          c₁.extMap (w.left y) = c₁.extMap (w.left y') }
      one_mem' := ⟨one_mem _, fun _ => one_mem _, fun _ _ _ => rfl⟩
      mul_mem' := by
        rintro w w' ⟨hr, hl, hc⟩ ⟨hr', hl', hc'⟩
        refine ⟨mul_mem hr hr', fun y => mul_mem (hl y) (hl' _), fun y y' hyy' => ?_⟩
        have hstep : c₂.stateMap (T₂.act y w.right) =
            c₂.stateMap (T₂.act y' w.right) := by
          rw [← c₂.act_extMap hr, ← c₂.act_extMap hr, hyy']
        simp only [WreathMonoid.mul_left]
        rw [c₁.extMap_mul_of_mem (hl y) (hl' _),
          c₁.extMap_mul_of_mem (hl y') (hl' _), hc y y' hyy', hc' _ _ hstep] }
  stateMap := Prod.map c₁.stateMap c₂.stateMap
  monoidMap := sorry
  stateMap_surj := sorry
  monoidMap_surj := sorry
  equivariant := sorry

/-- Monotonicity: division is preserved by wreath products. -/
theorem StrongDivides.wreath {S₁ T₁ S₂ T₂ : TransMon}
    (h₁ : S₁ ≺ T₁) (h₂ : S₂ ≺ T₂) : S₁ ≀ S₂ ≺ T₁ ≀ T₂ := by
  obtain ⟨c₁⟩ := h₁; obtain ⟨c₂⟩ := h₂
  exact ⟨c₁.wreath c₂⟩
```

Build: the submonoid (with its complete `mul_mem'` proof — the mathematical heart, transcribe it faithfully) must elaborate; four sorries expected. If `c₂.act_extMap hr` in `hstep` needs the state argument explicit, write `c₂.act_extMap hr y` / `... y'`; the rewrite direction is: `c₂.stateMap (T₂.act y w.right)` ← `S₂.act (c₂.stateMap y) (c₂.extMap w.right)`, then `hyy'` rewrites the inner `c₂.stateMap y`.

- [ ] **Step 2: Fill monoidMap and stateMap_surj (GREEN part 1)**

Fix a section of `c₂.stateMap` once, as a private abbreviation inside the definition via `let σ := Function.surjInv c₂.stateMap_surj` — or repeat the term; keep whichever elaborates cleanly.

```lean
  monoidMap :=
    { toFun := fun w =>
        ⟨fun s => c₁.extMap ((w : WreathMonoid T₁ T₂).left
            (Function.surjInv c₂.stateMap_surj s)),
          c₂.extMap (w : WreathMonoid T₁ T₂).right⟩
      map_one' := by
        ext s
        · simp [Covering.extMap_coe]  -- extMap 1 = 1 via extMap_of_mem (one_mem) + map_one
        · simp [Covering.extMap_coe]
      map_mul' := by
        rintro ⟨w, hr, hl, hc⟩ ⟨w', hr', hl', hc'⟩
        ext s
        · -- LHS: extMap₁ (w.left (σ s) * w'.left (T₂.act (σ s) w.right))
          -- RHS: extMap₁ (w.left (σ s)) * extMap₁ (w'.left (σ (S₂.act s (extMap₂ w.right))))
          -- Match second factors via hc' with:
          --   c₂.stateMap (T₂.act (σ s) w.right)
          --     = S₂.act (c₂.stateMap (σ s)) (c₂.extMap w.right)   [act_extMap]
          --     = S₂.act s (c₂.extMap w.right)                     [surjInv_eq]
          --     = c₂.stateMap (σ (S₂.act s (c₂.extMap w.right)))   [surjInv_eq]
          sorry -- DISCOVERY: assemble from extMap_mul_of_mem, hc', act_extMap,
                -- Function.surjInv_eq. The mathematical chain is fixed (above);
                -- only the rewrite order is discovered interactively.
        · simp [Covering.extMap_mul_of_mem hr hr'] }
  stateMap_surj := (c₁.stateMap_surj.prodMap c₂.stateMap_surj)
```

Name-drift watch: `Function.Surjective.prodMap` (or `Prod.map_surjective ⟨h₁, h₂⟩`); `Function.surjInv_eq (hf) (b) : f (surjInv hf b) = b`.

- [ ] **Step 3: Fill monoidMap_surj and equivariant (GREEN part 2)**

```lean
  monoidMap_surj := by
    rintro ⟨f, m⟩
    -- choose pointwise ψ₁-preimages of f, constant on φ₂-fibers by construction
    refine ⟨⟨⟨fun y => ↑(Function.surjInv c₁.monoidMap_surj (f (c₂.stateMap y))),
        ↑(Function.surjInv c₂.monoidMap_surj m)⟩,
      ⟨(Function.surjInv c₂.monoidMap_surj m).2,
        fun y => (Function.surjInv c₁.monoidMap_surj _).2,
        fun y y' h => by rw [h]⟩⟩, ?_⟩
    ext s
    · -- extMap₁ ↑(surjInv ψ₁ (f (φ₂ (σ s)))) = f s : coe + surjInv_eq twice
      rw [Covering.extMap_coe, Function.surjInv_eq]
      exact congrArg f (Function.surjInv_eq c₂.stateMap_surj s) ▸ rfl
        -- DISCOVERY: orient the two surjInv_eq rewrites; end state f s = f s
    · rw [Covering.extMap_coe, Function.surjInv_eq]
  equivariant := by
    rintro ⟨x, y⟩ ⟨⟨F, n⟩, hr, hl, hc⟩
    ext
    · -- S₁-component: c₁.act_extMap (hl _) plus fiber-compatibility hc at
      --   c₂.stateMap (σ (c₂.stateMap y)) = c₂.stateMap y   [surjInv_eq]
      sorry -- DISCOVERY: two rewrites (hc, then act_extMap); chain is fixed.
    · exact c₂.act_extMap hr y
```

**Both DISCOVERY sorries must be gone at task end (hard gate).** The mathematical chains are pinned in the comments; only tactic order is open. Fallbacks if `ext` on pair-goals misfires: `Prod.ext` explicitly, or `refine Prod.ext ?_ ?_`. If rewriting under the `fun s => ...` binder stalls, `funext s` first (for the function-component goals `ext s` already does this). If `Subtype` coercions obscure `hc`'s applicability, restate with `show` using `c₁.extMap` on both sides — every wall here has the same shape as M0–2 Task 8's, and the same `show`/`simp only`/`exact?` toolkit clears it.

- [ ] **Step 4: Sanity example + build clean + no sorry**

Append:

```lean
example {S₁ T₁ S₂ T₂ : TransMon} (h₁ : S₁ ≺ T₁) (h₂ : S₂ ≺ T₂) :
    S₁ ≀ S₂ ≺ T₁ ≀ T₂ := h₁.wreath h₂
example (T : TransMon) : T ≀ T ≺ T ≀ T :=
  (StrongDivides.refl T).wreath (.refl T)
```

```bash
lake build 2>&1 | tail -5 && (grep -rn "sorry" KRTheory/ KRTheory.lean; test $? -eq 1 && echo "clean")
```

- [ ] **Step 5: Commit**

```bash
git add KRTheory/TransMon/WreathDivision.lean
git commit -m "Add wreath monotonicity via covering wreath product"
```

---

### Task 7: Associativity up to division

**Files:**
- Modify: `KRTheory/TransMon/WreathDivision.lean` (append)

**Interfaces:**
- Consumes: `WreathMonoid` ext/simp kit, `wreath_act`; `Covering`, `StrongDivides`.
- Produces: `theorem KRTheory.TransMon.wreath_assoc_div (P Q R : TransMon) : (P ≀ Q) ≀ R ≺ P ≀ (Q ≀ R)`

Mathematics (blueprint `lem:wreath-assoc`): the two monoids are the same data up to currying, and the twisted multiplications *agree on the nose* under the identification — the covering uses `⊤` and the currying map; every proof obligation is a computation with the simp kit, no choice needed.

- [ ] **Step 1: Skeleton (RED)**

```lean
/-- One-directional associativity: `(P ≀ Q) ≀ R ≺ P ≀ (Q ≀ R)`.
The underlying map is currying; the twisted multiplications correspond
exactly, so the covering is total (`⊤`) with a bijective monoid map. -/
theorem wreath_assoc_div (P Q R : TransMon) :
    (P ≀ Q) ≀ R ≺ P ≀ (Q ≀ R) :=
  ⟨{ toSubmonoid := ⊤
     stateMap := fun p => ((p.1, p.2.1), p.2.2)
     monoidMap :=
       { toFun := fun w =>
           ⟨fun z => ⟨fun y => (w : WreathMonoid P (Q ≀ R)).left (y, z),
              (w : WreathMonoid P (Q ≀ R)).right.left z⟩,
            (w : WreathMonoid P (Q ≀ R)).right.right⟩
         map_one' := sorry
         map_mul' := sorry }
     stateMap_surj := fun p => ⟨(p.1.1, (p.1.2, p.2)), rfl⟩
     monoidMap_surj := sorry
     equivariant := sorry }⟩
```

Type sanity before building further: `stateMap : P.X × (Q.X × R.X) → (P.X × Q.X) × R.X` ✓; `monoidMap`'s target components: outer `left : R.X → WreathMonoid P Q`, outer `right : R.M` ✓.

- [ ] **Step 2: Fill the four obligations (GREEN)**

```lean
         map_one' := by
           ext z <;> ext <;> simp
         map_mul' := by
           intro w w'
           ext z
           · ext y <;> simp [WreathMonoid.mul_left, WreathMonoid.mul_right, wreath_act]
           · simp
           -- the nested ext pattern may need: ext z; then WreathMonoid.ext;
           -- then funext y — adjust granularity until goals are scalar
           -- equations closed by the simp set {mul_left, mul_right, wreath_act}
     monoidMap_surj := by
       rintro ⟨F, r⟩
       exact ⟨⟨⟨fun yz => (F yz.2).left yz.1, ⟨fun z => (F z).right, r⟩⟩, trivial⟩,
         by ext z <;> first | rfl | (ext y <;> rfl)⟩
     equivariant := by
       rintro ⟨x, y, z⟩ ⟨w, -⟩
       ext <;> simp [wreath_act]
```

The key check the implementer must NOT skip (guards a silent transposition): `map_mul'`'s inner-left goal must reduce to
`w.left (y, z) * w'.left (y ⊳_Q (w.right.left z), z ⊳_R w.right.right) = w.left (y,z) * w'.left ((y, z) ⊳_{Q≀R} w.right)` — which is `rfl`-true because `(y,z) ⊳_{Q≀R} w.right` computes componentwise to exactly that pair (`wreath_act`). If a simp-normal-form mismatch appears here, it means an argument-order transposition somewhere in `toFun` — fix the construction, never weaken the statement.

- [ ] **Step 3: Sanity example + build + no sorry + commit**

```lean
example (P Q R : TransMon) : (P ≀ Q) ≀ R ≺ P ≀ (Q ≀ R) := wreath_assoc_div P Q R
```

```bash
lake build 2>&1 | tail -5 && (grep -rn "sorry" KRTheory/ KRTheory.lean; test $? -eq 1 && echo "clean")
git add KRTheory/TransMon/WreathDivision.lean
git commit -m "Add wreath associativity up to division"
```

---

### Task 8: wreathList_append + milestone acceptance

**Files:**
- Modify: `KRTheory/TransMon/WreathDivision.lean` (append)
- Modify: `blueprint/src/chapters/wreath.tex` (add `\leanok` to all seven anchors)

**Interfaces:**
- Consumes: everything from Tasks 2–7.
- Produces: `theorem KRTheory.TransMon.wreathList_append (L₁ L₂ : List TransMon) : wreathList L₁ ≀ wreathList L₂ ≺ wreathList (L₁ ++ L₂)`

- [ ] **Step 1: Statement + sorry (RED), then proof (GREEN)**

```lean
/-- The append lemma: gluing two iterated wreath decompositions.
This is the lemma that assembles recursive Krohn–Rhodes decompositions
(spec §3.9). -/
theorem wreathList_append (L₁ L₂ : List TransMon) :
    wreathList L₁ ≀ wreathList L₂ ≺ wreathList (L₁ ++ L₂) := by
  induction L₁ with
  | nil => simpa using trivial_wreath_div (wreathList L₂)
  | cons S L₁ ih =>
    -- (S ≀ WL₁) ≀ WL₂  ≺  S ≀ (WL₁ ≀ WL₂)  ≺  S ≀ WL(L₁ ++ L₂)
    calc (wreathList (S :: L₁)) ≀ wreathList L₂
        ≺ S ≀ (wreathList L₁ ≀ wreathList L₂) := by
          simpa using wreath_assoc_div S (wreathList L₁) (wreathList L₂)
      _ ≺ wreathList ((S :: L₁) ++ L₂) := by
          simpa using (StrongDivides.refl S).wreath ih
```

Watchpoints: `calc` needs a `Trans` instance for `≺` — if none is registered, either add `instance : Trans StrongDivides StrongDivides StrongDivides := ⟨StrongDivides.trans⟩` (one line, near the top of `WreathDivision.lean` so this task's Files list stays accurate; note it in the report as new API) or replace the `calc` with explicit `.trans` chaining:
`exact ((by simpa using wreath_assoc_div S (wreathList L₁) (wreathList L₂)) : _).trans (by simpa using (StrongDivides.refl S).wreath ih)`. The `simpa`s only normalize `wreathList_cons`/`wreathList_nil`/`List.cons_append` — if they overshoot, use `rw` with those three lemmas instead.

- [ ] **Step 2: Acceptance examples**

```lean
-- Milestone acceptance (spec §7 row 3) exercised end-to-end:
example (A B C : TransMon) (h : A ≺ B ≀ C) (hB : B ≺ wreathList [B])
    (hC : C ≺ wreathList [C]) : A ≺ wreathList [B, C] :=
  (h.trans (hB.wreath hC)).trans (by simpa using wreathList_append [B] [C])
```

(This is the exact gluing shape the KR induction will use in milestone 8 — if it elaborates, the API is fit for purpose.)

- [ ] **Step 3: Blueprint checkmarks**

In `blueprint/src/chapters/wreath.tex`, add `\leanok` after the `\lean{...}` of: `def:wreath`, `lem:wreath-card`, `def:wreathList`, `lem:wreath-trivial`, `lem:wreath-mono`, `lem:wreath-assoc`, `lem:wreathList-append`.

- [ ] **Step 4: Full acceptance sweep**

```bash
lake build 2>&1 | tail -3
grep -rn "sorry\|admit\|native_decide" KRTheory/ KRTheory.lean; test $? -eq 1 && echo "no escape hatches"
```

Then create `KRTheory/Scratch.lean` (NOT committed):

```lean
import KRTheory.TransMon.WreathDivision
open KRTheory KRTheory.TransMon
#print axioms KRTheory.TransMon.StrongDivides.wreath
#print axioms KRTheory.TransMon.wreath_assoc_div
#print axioms KRTheory.TransMon.wreathList_append
```

```bash
lake env lean KRTheory/Scratch.lean && rm KRTheory/Scratch.lean
```

Expected: each line a subset of `Classical.choice, propext, Quot.sound`.

- [ ] **Step 5: Commit**

```bash
git status --short   # must show only the two intended files
git add KRTheory/TransMon/WreathDivision.lean blueprint/src/chapters/wreath.tex
git commit -m "Add wreath list append lemma completing milestone 3"
```

---

## Self-review record (per writing-plans skill)

- **Spec coverage (milestone 3, spec §3.3 + §7 row 3):** monoid instance = Task 2; monotonicity = Tasks 5–6; `wreath_assoc_div` = Task 7; `wreathList_append` = Task 8; absorption + `wreathList` = Tasks 3–4; blueprint chapter = Task 1, marks = Task 8. Spec's `wreath_div_wreath` name is delivered as `StrongDivides.wreath` (dot-notation composability, matching M0–2's `StrongDivides.trans` convention) with the same statement — recorded here as the naming decision; blueprint uses the new name.
- **Placeholder scan:** three explicit DISCOVERY points (Task 6 Steps 2–3), each with the mathematical chain pinned in comments and gated by the hard no-sorry check at task end — same pattern that succeeded in M0–2 Task 8. No other TBDs.
- **Type consistency:** `WreathMonoid.left/right` field names match Mathlib's `RegularWreathProduct` and are used identically in Tasks 2–8; `≀` is `infixr:60` everywhere (binds tighter than `≺` at 50, associates like `foldr`); `Covering.extMap` signatures in Task 5's Produces block match every use in Task 6; the Task 8 acceptance example uses only names produced by earlier tasks (`.wreath`, `.trans`, `wreathList_append`, `div_wreathList_singleton` not needed there).
- **Noncomputability audit:** `noncomputable` appears exactly on `wreath`, `wreathList`, `Covering.extMap`, `Covering.wreath` (uses extMap + surjInv) — the `Monoid` instance and all simp lemmas stay computable, per Global Constraints.
