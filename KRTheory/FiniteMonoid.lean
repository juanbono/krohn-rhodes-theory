import Mathlib.Tactic

/-!
# Finite monoid preliminaries

Counting and unit lemmas for finite monoids [spec §3.6 prelims,
blueprint ch. `ch:finitemonoid`]. Mathlib already provides the
one-sided-inverse lemmas (`mul_eq_one_comm`,
`IsUnit.of_mul_eq_one_right`); this file holds what it lacks.
Upstream candidates (spec §9).
-/

namespace KRTheory

/-- A predicate that fails somewhere carves out a strictly smaller
subtype. `Nat.card` analogue of `Fintype.card_subtype_lt`
[blueprint `lem:card-subtype-lt`]. -/
theorem Nat.card_subtype_lt {α : Type} [Finite α] {p : α → Prop} {x : α}
    (hx : ¬ p x) : Nat.card {a // p a} < Nat.card α := by
  have : Fintype α := Fintype.ofFinite α
  classical
  simpa [Nat.card_eq_fintype_card] using
    Fintype.card_subtype_lt (p := p) (x := x) hx

variable {M : Type} [Monoid M] [Finite M]

/-- Every element of a finite monoid has an idempotent power `a ^ n`,
`n ≥ 1` [blueprint `lem:idem-pow`]. Pigeonhole gives `a ^ i = a ^ j`
with `i < j`; the period `p := j - i` then absorbs (`a ^ (k + p) =
a ^ k` for `k ≥ i`), and `n := p * (i + 1)` is a multiple of `p` at
least `i`. -/
theorem exists_pow_idempotent (a : M) :
    ∃ n : ℕ, 0 < n ∧ IsIdempotentElem (a ^ n) := by
  sorry

-- Sanity (spec §6): in `ZMod 4`, the element `2` squares to `0`, and
-- `0` is idempotent; `exists_pow_idempotent` must therefore be
-- satisfiable at `n = 2` — witness check, plus the generic call.
example : IsIdempotentElem ((2 : ZMod 4) ^ 2) := by
  -- `show` unfolds the semireducible `IsIdempotentElem` so `decide`
  -- finds its `Decidable` instance at the bare equation
  show (2 : ZMod 4) ^ 2 * (2 : ZMod 4) ^ 2 = (2 : ZMod 4) ^ 2
  decide
example : ∃ n : ℕ, 0 < n ∧ IsIdempotentElem ((2 : ZMod 4) ^ n) :=
  exists_pow_idempotent 2

end KRTheory
