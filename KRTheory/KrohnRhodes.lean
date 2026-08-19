import KRTheory.FiniteMonoid
import KRTheory.GroupCase
import KRTheory.Decomposition

/-!
# The Krohn–Rhodes theorem

The main induction and the two v1 main theorems [DKS Thm 4.1; spec
§3.9; blueprint `ch:krohnrhodes`]: every faithful finite transformation
monoid with nonempty states divides an iterated wreath product of
flip-flops and regular representations of finite simple groups dividing
its monoid — and the abstract finite-monoid corollary.

Factors are carried as `KRPrime`: canonical objects (THE flip-flop, a
`regular G`), not isomorphism classes, so the statements need no
TransMon-isomorphism API (spec §3.9).
-/

namespace KRTheory
namespace TransMon

/-- A Krohn–Rhodes prime factor [blueprint `def:krprime`]: the
flip-flop, or a bundled finite (simple, in the theorems' conclusions)
group. -/
inductive KRPrime : Type 1 where
  /-- The flip-flop factor `U₂`. -/
  | flipflop : KRPrime
  /-- A group factor. -/
  | grp (G : BundledFinGroup) : KRPrime

/-- The transformation monoid a prime stands for [blueprint
`def:krprime`]: the canonical flip-flop, or the regular representation
of the group. -/
def KRPrime.toTransMon : KRPrime → TransMon
  | .flipflop => flipFlop
  | .grp G => regular G.carrier

/-- Equation lemma (the match-compiled `toTransMon` does not
`rfl`-reduce under `rw`'s closing check). -/
@[simp] theorem KRPrime.toTransMon_flipflop :
    KRPrime.flipflop.toTransMon = flipFlop := rfl

/-- Equation lemma, group case. -/
@[simp] theorem KRPrime.toTransMon_grp (G : BundledFinGroup) :
    (KRPrime.grp G).toTransMon = regular G.carrier := rfl

-- Sanity (spec §6): the flip-flop prime is THE flip-flop — 2 states,
-- 3 monoid elements; a group prime's monoid is the group itself.
example : Nat.card KRPrime.flipflop.toTransMon.M = 3 := by
  rw [KRPrime.toTransMon_flipflop]
  show Nat.card (Resets Bool) = 3
  rw [Resets.natCard, Nat.card_eq_fintype_card]
  decide
example : Nat.card KRPrime.flipflop.toTransMon.X = 2 := by
  rw [KRPrime.toTransMon_flipflop]
  show Nat.card Bool = 2
  rw [Nat.card_eq_fintype_card]
  decide
example (G : BundledFinGroup) : (KRPrime.grp G).toTransMon.M = G.carrier := rfl

end TransMon
end KRTheory
