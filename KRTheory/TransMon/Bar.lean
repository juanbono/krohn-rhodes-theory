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

namespace BarMonoid

variable {T : TransMon}

/-- The twisted multiplication; left factor acts first. -/
instance : Monoid (BarMonoid T) where
  mul w w' := match w, w' with
    | .of m, .of n => .of (m * n)
    | _, .reset x => .reset x
    | .reset x, .of m => .reset (T.act x m)
  one := .of 1
  mul_assoc a b c := by
    rcases a with m | x <;> rcases b with n | y <;> rcases c with p | z <;> try rfl
    · show (BarMonoid.of ((m * n) * p) : BarMonoid T) = .of (m * (n * p))
      rw [mul_assoc]
    · show (BarMonoid.reset (T.act (T.act x n) p) : BarMonoid T) = .reset (T.act x (n * p))
      rw [TransMon.act_mul]
  one_mul a := by
    rcases a with m | x <;> try rfl
    show (BarMonoid.of (1 * m) : BarMonoid T) = .of m
    rw [one_mul]
  mul_one a := by
    rcases a with m | x
    · show (BarMonoid.of (m * 1) : BarMonoid T) = .of m
      rw [mul_one]
    · show (BarMonoid.reset (T.act x 1) : BarMonoid T) = .reset x
      rw [TransMon.act_one]

/-- Two original elements multiply exactly as they do in `T.M`. -/
@[simp] theorem of_mul_of (m n : T.M) :
    (.of m * .of n : BarMonoid T) = .of (m * n) := rfl
/-- An original element followed by a reset is that reset: resets absorb
anything to their left. -/
@[simp] theorem of_mul_reset (m : T.M) (x : T.X) :
    (.of m * .reset x : BarMonoid T) = .reset x := rfl
/-- A reset followed by `m` is a reset to wherever `m` moves the reset
target — the left factor (the reset) acts first. -/
@[simp] theorem reset_mul_of (x : T.X) (m : T.M) :
    (.reset x * .of m : BarMonoid T) = .reset (T.act x m) := rfl
/-- Two resets in a row: only the rightmost survives. -/
@[simp] theorem reset_mul_reset (x y : T.X) :
    (.reset x * .reset y : BarMonoid T) = .reset y := rfl
/-- The identity of `BarMonoid T` is the original identity, wrapped by `of`. -/
@[simp] theorem one_def : (1 : BarMonoid T) = .of 1 := rfl

/-- Embedding of the original monoid. -/
def ofHom : T.M →* BarMonoid T where
  toFun := .of
  map_one' := rfl
  map_mul' _ _ := rfl

/-- `ofHom` computes as `of` on elements. -/
@[simp] theorem ofHom_apply (m : T.M) : (ofHom m : BarMonoid T) = .of m := rfl

/-- `ofHom` is injective: distinct original elements stay distinct once
wrapped by `of`. -/
theorem ofHom_injective : Function.Injective (ofHom (T := T)) :=
  fun _ _ h => by injection h

/-- As a type, `BarMonoid T` is the sum of the monoid and the states. -/
def equivSum : BarMonoid T ≃ T.M ⊕ T.X where
  toFun w := match w with | .of m => .inl m | .reset x => .inr x
  invFun s := match s with | .inl m => .of m | .inr x => .reset x
  left_inv w := by cases w <;> rfl
  right_inv s := by cases s <;> rfl

/-- `BarMonoid T` has decidable equality whenever `T`'s pieces do.
`TransMon` deliberately does not bundle `DecidableEq` on `X`/`M` (see the
`wreath` docstring), so an unconditional `deriving DecidableEq` on the
inductive above is not derivable: Lean's deriving handler only closes
`DecidableEq` goals by instance search over the *ambient* context, and
for the opaque projections `T.M`/`T.X` there is nothing to find — unlike
a bare type parameter, `T.M`/`T.X` cannot be generalized into a fresh
instance argument by the handler itself. This is the conditional
instance the handler would have produced had it been able to, obtained
the same way `Fintype` is above: transported across `equivSum`. -/
instance [DecidableEq T.X] [DecidableEq T.M] : DecidableEq (BarMonoid T) :=
  equivSum.decidableEq

/-- `BarMonoid T` is finite: transported from the computable
`Fintype (T.M ⊕ T.X)` instance across `equivSum`. -/
instance : Fintype (BarMonoid T) := Fintype.ofEquiv _ equivSum.symm

/-- `|BarMonoid T| = |M| + |X|`. -/
theorem natCard : Nat.card (BarMonoid T) = Nat.card T.M + Nat.card T.X := by
  rw [Nat.card_congr equivSum, Nat.card_sum]

end BarMonoid

/-- The bar operation `T.bar` [DKS §2.4]: same states, resets adjoined.
Computable (contrast `wreath`). -/
def bar (T : TransMon) : TransMon where
  X := T.X
  M := BarMonoid T
  act x w := match w with | .of m => T.act x m | .reset x₀ => x₀
  act_one x := by simp
  act_mul x w w' := by cases w <;> cases w' <;> simp [TransMon.act_mul]

/-- `T.bar` acts on an `of`-wrapped element exactly as `T` itself acts. -/
@[simp] theorem bar_act_of {T : TransMon} (x : T.X) (m : T.M) :
    T.bar.act x (.of m) = T.act x m := rfl
/-- `T.bar` acts on a reset by jumping straight to the reset target,
regardless of the current state. -/
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
  rw [BarMonoid.natCard, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]  -- 3 + 3
  rfl
example (x : trivialTM.X) :
    trivialTM.bar.act x (.reset PUnit.unit) = PUnit.unit := rfl

end TransMon
end KRTheory
