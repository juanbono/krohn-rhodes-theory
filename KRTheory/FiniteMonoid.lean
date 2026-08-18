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
  -- pigeonhole: two powers coincide
  obtain ⟨s, t, hne, hst⟩ :=
    Finite.exists_ne_map_eq_of_infinite (fun n : ℕ => a ^ n)
  obtain ⟨i, j, hlt, hij⟩ : ∃ i j : ℕ, i < j ∧ a ^ i = a ^ j := by
    rcases lt_or_gt_of_ne hne with h | h
    · exact ⟨s, t, h, hst⟩
    · exact ⟨t, s, h, hst.symm⟩
  set p := j - i with hp
  have hp1 : 0 < p := by omega
  -- one period absorbs past the ramp `i`
  have hstep : ∀ t : ℕ, a ^ (i + t + p) = a ^ (i + t) := by
    intro t
    have h1 : i + t + p = j + t := by omega
    rw [h1, pow_add, pow_add, ← hij]
  -- …hence any number of periods
  have habs : ∀ m t : ℕ, a ^ (i + t + m * p) = a ^ (i + t) := by
    intro m
    induction m with
    | zero => intro t; simp
    | succ m ihm =>
      intro t
      have h1 : i + t + (m + 1) * p = i + (t + m * p) + p := by
        rw [Nat.succ_mul]; omega
      rw [h1, hstep (t + m * p)]
      have h2 : i + (t + m * p) = i + t + m * p := by omega
      rw [h2, ihm t]
  -- the witness: a p-multiple past the ramp
  have hile : i + 1 ≤ p * (i + 1) := Nat.le_mul_of_pos_left _ hp1
  refine ⟨p * (i + 1), by positivity, ?_⟩
  set t₀ := p * (i + 1) - i with ht₀
  have hsplit : p * (i + 1) = i + t₀ := by omega
  have e1 : p * (i + 1) + p * (i + 1) = i + t₀ + (i + 1) * p := by
    rw [Nat.mul_comm (i + 1) p]; omega
  show a ^ (p * (i + 1)) * a ^ (p * (i + 1)) = a ^ (p * (i + 1))
  calc a ^ (p * (i + 1)) * a ^ (p * (i + 1))
      = a ^ (p * (i + 1) + p * (i + 1)) := (pow_add a _ _).symm
    _ = a ^ (i + t₀ + (i + 1) * p) := by rw [e1]
    _ = a ^ (i + t₀) := habs (i + 1) t₀
    _ = a ^ (p * (i + 1)) := by rw [← hsplit]

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
