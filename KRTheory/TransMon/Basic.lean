import Mathlib.Tactic
import Mathlib.Data.ZMod.Basic
-- Only for the noncommutative sanity check on `regular` below: `ZMod n`
-- is commutative and can't witness right-action chirality, so we borrow
-- `Equiv.Perm (Fin 3)` as a small noncommutative test monoid.
import Mathlib.GroupTheory.Perm.Basic

/-!
# Transformation monoids

The core object of the Krohn–Rhodes formalization [DKS §2.1]: a finite
state set with a right action of a finite monoid. Design decisions
(bundled structure, raw right action) are recorded in the design doc
§4.1. Right-action convention: in `x ⊳ (m * n)`, `m` acts first.
-/

namespace KRTheory

/-- A finite transformation monoid `(X, M)`: finite states `X`, finite
monoid `M`, right action `act`. Faithfulness is NOT required; see
`TransMon.Faithful`. [DKS §2.1] -/
structure TransMon : Type 1 where
  /-- The state set. -/
  X : Type
  /-- The monoid carrier. -/
  M : Type
  /-- `X` is finite. -/
  [finiteX : Finite X]
  /-- `M` has a monoid structure. -/
  [monoidM : Monoid M]
  /-- `M` is finite. -/
  [finiteM : Finite M]
  /-- The right action of `M` on `X`. -/
  act : X → M → X
  /-- The identity of `M` acts trivially. -/
  act_one : ∀ x, act x 1 = x
  /-- The action of a product `m * n` is sequential: `m` acts first, then `n`. -/
  act_mul : ∀ x m n, act x (m * n) = act (act x m) n

namespace TransMon

attribute [instance] finiteX monoidM finiteM
attribute [simp] act_one act_mul

/-- Right-action notation. `m` binds tighter so `x ⊳ m * n` parses as
`x ⊳ (m * n)`. Sugar over `T.act`; use `T.act` when the ambient `T` is a
compound object Lean cannot infer. -/
scoped notation:65 x:65 " ⊳ " m:66 => TransMon.act _ x m

-- Exercises `⊳` (spec §6): acting by `m * n` is acting by `m`, then `n`.
example (T : TransMon) (x : T.X) (m n : T.M) :
    x ⊳ (m * n) = (x ⊳ m) ⊳ n := T.act_mul x m n

/-- The one-state, one-element transformation monoid; base of iterated
wreath products. -/
def trivialTM : TransMon where
  X := PUnit
  M := PUnit
  act _ _ := PUnit.unit
  act_one x := by cases x; rfl
  act_mul _ _ _ := rfl

-- Sanity checks (spec §6): the trivial object is as small as it claims.
example : Nat.card trivialTM.X = 1 := by
  show Nat.card PUnit = 1
  exact Nat.card_unique
example : Nat.card trivialTM.M = 1 := by
  show Nat.card PUnit = 1
  exact Nat.card_unique
example (x : trivialTM.X) (m : trivialTM.M) : trivialTM.act x m = x := by
  cases x; rfl

/-- `T.Faithful`: the action distinguishes monoid elements. A `def`, not
a class — bundled values make instance search unreliable (spec §4.1). -/
def Faithful (T : TransMon) : Prop :=
  ∀ ⦃m n : T.M⦄, (∀ x : T.X, T.act x m = T.act x n) → m = n

/-- The trivial transformation monoid is faithful: `M` has only one element,
so there is nothing to distinguish. -/
theorem trivialTM_faithful : trivialTM.Faithful := by
  intro m n _
  rfl

/-- The regular representation `(M, M)`: `M` acting on itself by right
multiplication. Always faithful; the bridge from abstract monoids to
transformation monoids. [DKS §2.1] -/
def regular (M : Type) [Monoid M] [Finite M] : TransMon where
  X := M
  M := M
  act x m := x * m
  act_one := mul_one
  act_mul x m n := (mul_assoc x m n).symm

/-- The regular representation is faithful: if `x * m = x * n` for all `x`,
evaluate at `x = 1` to get `m = n`. [DKS §2.1] -/
theorem regular_faithful (M : Type) [Monoid M] [Finite M] :
    (regular M).Faithful := by
  show ∀ ⦃m n : M⦄, (∀ x : M, (regular M).act x m = (regular M).act x n) → m = n
  intro m n h
  have h1 : (1 : M) * m = (1 : M) * n := h 1
  simpa using h1

-- Sanity checks (spec §6).
example : Nat.card (regular (ZMod 3)).X = 3 := by
  show Nat.card (ZMod 3) = 3
  rw [Nat.card_eq_fintype_card, ZMod.card]
example : (regular (ZMod 3)).act (2 : ZMod 3) (2 : ZMod 3) = (1 : ZMod 3) := rfl  -- 2·2 = 4 ≡ 1
example : (regular (ZMod 4)).act (3 : ZMod 4) (2 : ZMod 4) = (2 : ZMod 4) := rfl  -- 3·2 = 6 ≡ 2

-- Noncommutative sanity check (spec §6): `ZMod n` above is commutative,
-- so `x * m = m * x` there and the examples can't see which side of `*`
-- `regular`'s action puts `x` on. `Equiv.Perm (Fin 3)` is noncommutative
-- and does: `Equiv.swap 0 1` and `Equiv.swap 1 2` don't commute, so these
-- checks would genuinely fail if `regular`'s `act` were defined as
-- `act x m := m * x` (left action) instead of `act x m := x * m` (the
-- intended right action) — swapping the factors would swap the results.
example :
    (regular (Equiv.Perm (Fin 3))).act (Equiv.swap 0 1) (Equiv.swap 1 2)
      = Equiv.swap 0 1 * Equiv.swap 1 2 := rfl
example :
    Equiv.toFun ((regular (Equiv.Perm (Fin 3))).act (Equiv.swap 0 1) (Equiv.swap 1 2)) 0
      = 1 := rfl  -- m first: swap 1 2 fixes 0, then swap 0 1 sends 0 ↦ 1

end TransMon
end KRTheory
