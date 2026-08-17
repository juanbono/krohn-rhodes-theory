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

end TransMon
end KRTheory
