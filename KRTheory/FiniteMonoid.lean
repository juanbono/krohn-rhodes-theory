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

end KRTheory
