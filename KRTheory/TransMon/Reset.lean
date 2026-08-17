-- `WreathDivision` rather than `Wreath`: it re-exports `Wreath` and
-- `Division` (needed for `Covering`/`StrongDivides` in `reset_split`) and
-- additionally carries the `≀`-division calculus that the DKS 2.12
-- induction consumes downstream.
import KRTheory.TransMon.WreathDivision

/-!
# Reset monoids and the flip-flop

`U(X)` [DKS §2.5]: the identity plus one reset per point of `X`. The
flip-flop `U(Bool)` — two states, three elements — is the unique
non-group prime of Krohn–Rhodes theory. Fresh inductive carrier (not
`Option X`) to avoid planting a global `Monoid (Option _)` instance.
Everything here is computable.

The second half of the file is the one-point splitting `reset_split`
[DKS Lemma 2.12, blueprint `lem:reset-split`], the inductive step that
peels a single state off a reset monoid into a flip-flop factor.
-/

namespace KRTheory
namespace TransMon

/-- The reset monoid's carrier: `id` plus one reset per point. -/
inductive Resets (X : Type) : Type
  /-- The identity element. -/
  | id
  /-- The reset onto `x`. -/
  | to (x : X)

namespace Resets

variable {X : Type}

/-- Right-selection multiplication: the LAST reset wins; `id` is
neutral. (Left factor acts first, and a later reset overwrites.) -/
instance : Monoid (Resets X) where
  mul a b := match b with | .id => a | .to y => .to y
  one := .id
  mul_assoc a b c := by cases c <;> cases b <;> rfl
  one_mul a := by cases a <;> rfl
  mul_one _ := rfl

/-- Multiplying by a reset on the right always lands on that reset,
regardless of the left factor: the later reset wins. -/
@[simp] theorem mul_to (a : Resets X) (y : X) :
    (a * .to y : Resets X) = .to y := rfl
/-- The identity of `Resets X` is `id`. -/
@[simp] theorem one_def : (1 : Resets X) = (.id : Resets X) := rfl
/-- `id` is right-neutral for `*`: this is `mul_one` restated with
`one_def` unfolded, spelled out directly on the `id` constructor so
`simp` also normalizes goals that never mention `1`. -/
@[simp] theorem mul_id (a : Resets X) : (a * .id : Resets X) = a := rfl

/-- As a type, `Resets X` is `Option X`. -/
def equivOption : Resets X ≃ Option X where
  toFun a := match a with | .id => none | .to x => some x
  invFun o := match o with | none => .id | some x => .to x
  left_inv a := by cases a <;> rfl
  right_inv o := by cases o <;> rfl

/-- `Resets X` has decidable equality whenever `X` does, transported
across `equivOption`. `Resets` deliberately does not bundle
`DecidableEq X`, so — mirroring `BarMonoid`'s `equivSum.decidableEq`
instance in `Bar.lean` — this is stated as an explicit conditional
instance rather than via `deriving DecidableEq`, which leaves no room to
attach the docstring the standing repo convention requires on every
public instance. -/
instance [DecidableEq X] : DecidableEq (Resets X) := equivOption.decidableEq

/-- `Resets X` is finite, via the equivalence `equivOption` with the
finite `Option X`. -/
instance [Fintype X] : Fintype (Resets X) := Fintype.ofEquiv _ equivOption.symm

/-- `|U(X)'s monoid| = |X| + 1`. -/
theorem natCard [Fintype X] : Nat.card (Resets X) = Nat.card X + 1 := by
  rw [Nat.card_congr equivOption, Finite.card_option]

end Resets

/-- The reset transformation monoid `U(X)` [DKS §2.5]: `Resets X`
acting on `X`, `to y` constantly. Computable. -/
def resetMonoid (X : Type) [Fintype X] : TransMon where
  X := X
  M := Resets X
  act x r := match r with | .id => x | .to y => y
  act_one _ := rfl
  act_mul x a b := by cases b <;> rfl

/-- `resetMonoid`'s identity element acts trivially, fixing every state. -/
@[simp] theorem resetMonoid_act_id {X : Type} [Fintype X] (x : X) :
    (resetMonoid X).act x .id = x := rfl
/-- `resetMonoid`'s reset `to y` acts as the constant map onto `y`, from
any current state. -/
@[simp] theorem resetMonoid_act_to {X : Type} [Fintype X] (x y : X) :
    (resetMonoid X).act x (.to y) = y := rfl

/-- The flip-flop: two states, three elements — the non-group prime.
[DKS §2.5] -/
def flipFlop : TransMon := resetMonoid Bool

/-!
### The one-point splitting

`reset_split` [DKS Lemma 2.12, blueprint `lem:reset-split`]: with a point
`x₀ : X` singled out, `U(X)` is covered by `U(X \ {x₀}) ≀ U(2)`. The back
flip-flop records the single bit "am I sitting on `x₀`?"; the front reset
monoid records "and if not, on which other point?". The state map
`(y, b) ↦ if b then x₀ else y` is the resulting two-chart atlas of `X`,
and the covering submonoid is cut out by the three conditions that make
that atlas consistent (see `splitSub`).

The four private helpers below carry the covering's data. They are
stated for an *arbitrary* finite `Y` equipped with a map `f : Y → X`
hitting everything but `x₀`, rather than for `Y = {x // x ≠ x₀}`
directly, for two reasons.

* `Fintype {x : X // x ≠ x₀}` is not derivable from `Fintype X` alone
  (`Subtype.fintype` wants `DecidablePred`, hence `DecidableEq X`, which
  `TransMon` deliberately never bundles — spec §4.1). The fixed
  statement of `reset_split` therefore has to be elaborated under
  `open scoped Classical`; keeping the helpers parametric in `Y` stops
  that classical instance from appearing in a single intermediate goal.
* Every helper statement then lives at *concrete* types (`Resets Y`,
  `Resets Bool`, `Y × Bool`), which is what lets `rw`/`simp` fire at all.
  At the projected types (`flipFlop.X`, `(resetMonoid Y).M`,
  `(resetMonoid Y ≀ flipFlop).M`) matching stalls for the reason the
  `Wreath.lean` mirror-kit docstring records: `wreath`, `resetMonoid` and
  `flipFlop` are semireducible, so e.g. `true : flipFlop.X` is not
  type-correct at `rw`'s restricted transparency and any pattern
  variable landing there fails to unify. The repair used throughout
  below is the one already established in `WreathDivision.lean`: `show`
  the definitionally equal, fully unfolded goal (`show` elaborates at
  default transparency), then rewrite with fully concrete hypotheses.
-/

/-- Constructor discrimination in `Resets`: a reset is never the
identity. Stated separately because the goals needing it below sit at
projected types (`(resetMonoid Z).M`), where `exact` reaches it up to
definitional unfolding but `simp` cannot fire directly. -/
private theorem to_ne_id {Z : Type} (z : Z) : (Resets.to z : Resets Z) ≠ .id := by
  simp

/-- The covering's state map `φ`, as a function of concrete type: the
state `(y, b)` of `U(Y) ≀ U(2)` denotes `x₀` when the flip-flop bit is
set and `f y` otherwise. -/
private def splitState {X Y : Type} (x₀ : X) (f : Y → X) (p : Y × Bool) : X :=
  if p.2 then x₀ else f p.1

/-- The covering's monoid map `ψ`, as a function of the two components
that matter: the back component `r` and the (constant, on the covering
submonoid) front value `a`. Three families — identity, reset onto `x₀`,
reset onto `f y` — and one junk value on the `(id, to false)` pair, which
`splitSub`'s condition C2 makes unreachable. -/
private def splitMap {X Y : Type} (x₀ : X) (f : Y → X) (a : Resets Y)
    (r : Resets Bool) : Resets X :=
  match r with
  | .id => .id
  | .to true => .to x₀
  | .to false => match a with
      | .id => .id
      | .to y => .to (f y)

/-- The covering submonoid of `U(Y) ≀ U(2)`: the elements whose front
component is constant (C1), whose front component is a genuine reset
whenever the back component resets the bit to `false` (C2), and whose
front component is the identity whenever the back component is (C3).
C1 makes `splitMap` well defined, C2 rules out its junk value, and C3
pins the identity fibre — together they are exactly closure under the
twisted multiplication. -/
private def splitSub (Y : Type) [Fintype Y] :
    Submonoid (resetMonoid Y ≀ flipFlop).M where
  carrier := {w | (∀ b b', w.left b = w.left b') ∧
      (w.right = .to false → w.left true ≠ .id) ∧
      (w.right = .id → w.left true = .id)}
  one_mem' := by
    refine ⟨fun _ _ => rfl, fun h => ?_, fun _ => rfl⟩
    -- C2 is vacuous at `1`: its back component is `id`, not `to false`.
    exact absurd (show (Resets.id : Resets Bool) = Resets.to false from h)
      (to_ne_id false).symm
  mul_mem' := by
    rintro w w' ⟨hw1, hw2, hw3⟩ ⟨hw1', hw2', hw3'⟩
    refine ⟨?_, ?_, ?_⟩
    · -- C1: a product of constant front components is constant.
      intro b b'
      show w.left b * w'.left (flipFlop.act b w.right) =
        w.left b' * w'.left (flipFlop.act b' w.right)
      rw [hw1 b b', hw1' (flipFlop.act b w.right) (flipFlop.act b' w.right)]
    · -- C2: case on `w'`'s back component.
      intro hr
      replace hr : w.right * w'.right = Resets.to false := hr
      show w.left true * w'.left (flipFlop.act true w.right) ≠ Resets.id
      rw [hw1' (flipFlop.act true w.right) true]
      rcases hr' : w'.right with _ | c
      · -- `w'` is identity-like, so the product inherits `w`'s C2.
        rw [hr'] at hr
        rw [hw3' hr']
        exact hw2 hr
      · rw [hr'] at hr
        cases c
        · -- `w'` itself resets to `false`; its front value wins.
          have h2 := hw2' hr'
          rcases hl : w'.left true with _ | z
          · exact absurd hl h2
          · exact to_ne_id z
        · -- `w'` resets to `true`, so the product cannot reset to `false`.
          exact absurd
            (show (Resets.to true : Resets Bool) = Resets.to false from hr) (by simp)
    · -- C3: the product's back component is `id` only if both are.
      intro hr
      replace hr : w.right * w'.right = Resets.id := hr
      show w.left true * w'.left (flipFlop.act true w.right) = Resets.id
      rw [hw1' (flipFlop.act true w.right) true]
      rcases hr' : w'.right with _ | c
      · rw [hr'] at hr
        rw [hw3' hr']
        exact hw3 hr
      · rw [hr'] at hr
        exact absurd (show (Resets.to c : Resets Bool) = Resets.id from hr) (to_ne_id c)

/-- The covering `U(X) ≺ U(Y) ≀ U(2)` behind `reset_split`, for any
finite `Y` mapping onto `X \ {x₀}` via `f`. Splitting the construction
off from the theorem keeps every proof obligation at concrete types (see
the section preamble). -/
private def splitCovering {X Y : Type} [Fintype X] [Fintype Y] [Nonempty Y]
    (x₀ : X) (f : Y → X) (hf : ∀ x : X, x ≠ x₀ → ∃ y, f y = x) :
    Covering (resetMonoid X) (resetMonoid Y ≀ flipFlop) where
  toSubmonoid := splitSub Y
  stateMap := splitState x₀ f
  monoidMap :=
    { toFun := fun n => splitMap x₀ f ((n.1 : (resetMonoid Y ≀ flipFlop).M).left true)
        (n.1 : (resetMonoid Y ≀ flipFlop).M).right
      map_one' := rfl
      map_mul' := by
        rintro ⟨w, -, -, -⟩ ⟨w', hw1', hw2', hw3'⟩
        show splitMap x₀ f (w.left true * w'.left (flipFlop.act true w.right))
            (w.right * w'.right) =
          splitMap x₀ f (w.left true) w.right * splitMap x₀ f (w'.left true) w'.right
        rw [hw1' (flipFlop.act true w.right) true]
        -- The three closure cases again, mirrored at the value level.
        rcases hr' : w'.right with _ | c
        · rw [hw3' hr']
          rfl
        · cases c
          · have h2 := hw2' hr'
            rcases hl : w'.left true with _ | z
            · exact absurd hl h2
            · rfl
          · rfl }
  stateMap_surj := by
    intro x
    by_cases h : x = x₀
    · -- `x₀` is read off any front state with the bit set.
      refine ⟨(Classical.arbitrary Y, true), ?_⟩
      show x₀ = x
      exact h.symm
    · obtain ⟨y, hy⟩ := hf x h
      refine ⟨(y, false), ?_⟩
      show f y = x
      exact hy
  monoidMap_surj := by
    intro a
    rcases a with _ | x
    · exact ⟨1, rfl⟩
    · by_cases h : x = x₀
      · refine ⟨⟨⟨fun _ => Resets.id, Resets.to true⟩, fun _ _ => rfl, ?_, ?_⟩, ?_⟩
        · intro hc
          exact absurd
            (show (Resets.to true : Resets Bool) = Resets.to false from hc) (by simp)
        · intro hc
          exact absurd (show (Resets.to true : Resets Bool) = Resets.id from hc)
            (to_ne_id true)
        · show (Resets.to x₀ : Resets X) = Resets.to x
          rw [h]
      · obtain ⟨y, hy⟩ := hf x h
        refine ⟨⟨⟨fun _ => Resets.to y, Resets.to false⟩, fun _ _ => rfl,
          fun _ => to_ne_id y, ?_⟩, ?_⟩
        · intro hc
          exact absurd (show (Resets.to false : Resets Bool) = Resets.id from hc)
            (to_ne_id false)
        · show (Resets.to (f y) : Resets X) = Resets.to x
          rw [hy]
  equivariant := by
    rintro p ⟨w, hw1, hw2, hw3⟩
    show (resetMonoid X).act (splitState x₀ f p) (splitMap x₀ f (w.left true) w.right) =
      splitState x₀ f ((resetMonoid Y).act p.1 (w.left p.2), flipFlop.act p.2 w.right)
    rcases hr : w.right with _ | c
    · -- identity: both sides fix the state (C1 + C3 make the front trivial)
      rw [hw1 p.2 true, hw3 hr]
      rfl
    · cases c
      · -- reset to `false`: C2 makes the front component a genuine reset
        rw [hw1 p.2 true]
        rcases hl : w.left true with _ | z
        · exact absurd hl (hw2 hr)
        · rfl
      · -- reset to `true`: both sides land on `x₀`
        rfl

open scoped Classical in
/-- DKS Lemma 2.12's inductive step (blueprint `lem:reset-split`): with a
point `x₀ : X` singled out, the reset monoid `U(X)` strongly divides
`U(X \ {x₀}) ≀ U(2)` — one state is peeled off into a flip-flop factor.
The covering sends the state `(y, b)` to `x₀` when the flip-flop bit is
set and to `y` otherwise, and its submonoid is `splitSub`.

`open scoped Classical` is needed for the *statement*: `Fintype X` alone
does not give `Fintype {x : X // x ≠ x₀}`, since `Subtype.fintype` wants
`DecidablePred (· ≠ x₀)` and `TransMon` deliberately bundles no
`DecidableEq` (spec §4.1). Callers must therefore reach the classical
instance the same way (`open scoped Classical`, or the `classical`
tactic); a mismatched `Fintype` instance is repaired by `convert`, which
closes the residual goal by `Subsingleton (Fintype _)` — see the `Bool`
sanity check below. -/
theorem reset_split (X : Type) [Fintype X] (x₀ : X)
    [Nonempty {x : X // x ≠ x₀}] :
    resetMonoid X ≺ resetMonoid {x : X // x ≠ x₀} ≀ flipFlop :=
  ⟨splitCovering x₀ Subtype.val fun x hx => ⟨⟨x, hx⟩, rfl⟩⟩

-- Sanity checks (spec §6).
-- Selection-direction guard: the RIGHT (later) reset must win; a
-- left-wins definition would return .to false here.
example : ((.to false * .to true : Resets Bool)) = .to true := by decide
example : ((.to true * .id : Resets Bool)) = .to true := by decide
example : Nat.card flipFlop.M = 3 := by
  show Nat.card (Resets Bool) = 3
  rw [Resets.natCard, Nat.card_eq_fintype_card]
  decide
example : flipFlop.act false (.to true) = true := rfl
example : flipFlop.act true (.id) = true := rfl
-- The spec-§6 figure, corrected (was wrongly 36): 3² · 3 = 27.
example : Nat.card (WreathMonoid flipFlop flipFlop) = 27 := by
  rw [WreathMonoid.natCard]
  show Nat.card (Resets Bool) ^ Nat.card Bool * Nat.card (Resets Bool) = 27
  rw [Resets.natCard, Nat.card_eq_fintype_card]
  decide
-- Splitting the two-state reset monoid: `U(2) ≺ U(1) ≀ U(2)`. `convert`
-- (not `exact`) because `Fintype {b : Bool // b ≠ true}` is synthesized
-- decidably here but classically in `reset_split`; the residual goal is
-- closed by `Subsingleton (Fintype _)`.
example : resetMonoid Bool ≺ resetMonoid {b : Bool // b ≠ true} ≀ flipFlop := by
  have : Nonempty {b : Bool // b ≠ true} := ⟨⟨false, by decide⟩⟩
  convert reset_split Bool true

end TransMon
end KRTheory
