import Mathlib.Tactic

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
  [fintypeX : Fintype X]
  [monoidM : Monoid M]
  [fintypeM : Fintype M]
  /-- The right action of `M` on `X`. -/
  act : X → M → X
  act_one : ∀ x, act x 1 = x
  act_mul : ∀ x m n, act x (m * n) = act (act x m) n

namespace TransMon

attribute [instance] fintypeX monoidM fintypeM
attribute [simp] act_one act_mul

/-- Right-action notation. `m` binds tighter so `x ⊳ m * n` parses as
`x ⊳ (m * n)`. Sugar over `T.act`; use `T.act` when the ambient `T` is a
compound object Lean cannot infer. -/
scoped notation:65 x:65 " ⊳ " m:66 => TransMon.act _ x m

/-- The one-state, one-element transformation monoid; base of iterated
wreath products. -/
def trivialTM : TransMon where
  X := PUnit
  M := PUnit
  act _ _ := PUnit.unit
  act_one x := by cases x; rfl
  act_mul _ _ _ := rfl

-- Sanity checks (spec §6): the trivial object is as small as it claims.
example : Fintype.card trivialTM.X = 1 := rfl
example : Fintype.card trivialTM.M = 1 := rfl
example (x : trivialTM.X) (m : trivialTM.M) : trivialTM.act x m = x := by
  cases x; rfl

end TransMon
end KRTheory
