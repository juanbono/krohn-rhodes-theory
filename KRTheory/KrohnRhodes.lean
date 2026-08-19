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

/-- The group branch of the induction [blueprint `lem:kr-group-branch`]:
if every element of `T.M` is a unit and states are nonempty, Q(T) holds
outright. Faithfulness is NOT needed — `group_bar_div` (M6,
strengthened) does not use it. The group structure is Mathlib's
`groupOfIsUnit`, which extends the bundled monoid instance in place, so
`regular T.M` is the same transformation monoid on both sides of the
glue (spec §8 risk row, resolved). -/
theorem krohnRhodes_bar_of_units (T : TransMon) (hX : Nonempty T.X)
    (hg : ∀ m : T.M, IsUnit m) :
    ∃ L : List KRPrime,
      T.bar ≺ wreathList (L.map KRPrime.toTransMon) ∧
      ∀ p ∈ L, ∀ G, p = KRPrime.grp G →
        IsSimpleGroup G.carrier ∧ G.carrier ≺ₘ T.M := by
  have := hX
  let _ : Group T.M := groupOfIsUnit hg
  obtain ⟨n, hff⟩ := reset_div_flipFlops T.X
  obtain ⟨Gs, hGs, hfac⟩ := transfGroup_div_wreath_simples T.M
  refine ⟨List.replicate n .flipflop ++ Gs.map .grp, ?_, ?_⟩
  · calc T.bar
        ≺ resetMonoid T.X ≀ regular T.M := group_bar_div T hg
      _ ≺ wreathList (List.replicate n flipFlop) ≀
            wreathList (Gs.map fun H => regular H.carrier) :=
          StrongDivides.wreath hff hGs
      _ ≺ wreathList ((List.replicate n KRPrime.flipflop
            ++ Gs.map KRPrime.grp).map KRPrime.toTransMon) := by
          rw [List.map_append, List.map_replicate,
            KRPrime.toTransMon_flipflop, List.map_map]
          exact wreathList_append _ _
  · intro p hp G hpG
    rcases List.mem_append.mp hp with hp | hp
    · exact absurd ((List.eq_of_mem_replicate hp).symm.trans hpG) (by simp)
    · obtain ⟨H, hH, rfl⟩ := List.mem_map.mp hp
      obtain rfl : H = G := by injection hpG
      exact hfac H hH

/-- The main induction [blueprint `thm:kr-bar`] — predicate Q of spec
§3.9: the barred `T` divides a wreath of primes whose group factors are
simple and divide `T.M`. Plain strong induction on `Nat.card T.M`
(blueprint `rem:kr-measure`: both recursive calls strictly shrink the
monoid; the spec's lex second component is never exercised). -/
theorem krohnRhodes_bar (T : TransMon) (hT : T.Faithful)
    (hX : Nonempty T.X) :
    ∃ L : List KRPrime,
      T.bar ≺ wreathList (L.map KRPrime.toTransMon) ∧
      ∀ p ∈ L, ∀ G, p = KRPrime.grp G →
        IsSimpleGroup G.carrier ∧ G.carrier ≺ₘ T.M := by
  revert hT hX
  generalize hcard : Nat.card T.M = n
  induction n using Nat.strong_induction_on generalizing T with
  | _ n ih =>
    intro hT hX
    by_cases hg : ∀ m : T.M, IsUnit m
    · exact krohnRhodes_bar_of_units T hX hg
    · obtain ⟨N, c, hc, hNtop, hgen⟩ := exists_gen_nonunit hg
      obtain ⟨L₁, hdiv₁, hfac₁⟩ :=
        ih (Nat.card (localDivisor T c).M)
          (hcard ▸ localDivisor_card_lt hc) (localDivisor T c) rfl
          (localDivisor_faithful hT c) (localDivisor_X_nonempty T c hX)
      obtain ⟨L₂, hdiv₂, hfac₂⟩ :=
        ih (Nat.card (rightFactor T N).M)
          (hcard ▸ card_submonoid_lt_of_ne_top N hNtop) (rightFactor T N)
          rfl (rightFactor_faithful T N) ⟨Sum.inr 1⟩
      refine ⟨L₁ ++ L₂, ?_, ?_⟩
      · calc T.bar
            ≺ (localDivisor T c).bar ≀ (rightFactor T N).bar :=
              decomposition T hT N c hc hgen
          _ ≺ wreathList (L₁.map KRPrime.toTransMon) ≀
                wreathList (L₂.map KRPrime.toTransMon) :=
              StrongDivides.wreath hdiv₁ hdiv₂
          _ ≺ wreathList ((L₁ ++ L₂).map KRPrime.toTransMon) := by
              rw [List.map_append]
              exact wreathList_append _ _
      · intro p hp G hpG
        rcases List.mem_append.mp hp with hp | hp
        · obtain ⟨hsimple, hdivM⟩ := hfac₁ p hp G hpG
          exact ⟨hsimple, hdivM.trans (localDivisor_divides c)⟩
        · obtain ⟨hsimple, hdivM⟩ := hfac₂ p hp G hpG
          exact ⟨hsimple, hdivM.trans (MonoidDivides.of_submonoid N)⟩

/-- **The Krohn–Rhodes theorem**, transformation form, strong version
[DKS Thm 4.1; spec §3.9; blueprint `thm:krohnrhodes`]: a faithful
finite transformation monoid with nonempty states strongly divides an
iterated wreath product of flip-flops and simple-group regulars, every
group factor dividing `T.M`. `[Nonempty T.X]` is necessary: an
empty-state transformation monoid strongly divides no wreath of primes
(their state spaces are nonempty). -/
theorem krohnRhodes (T : TransMon) (hT : T.Faithful) [Nonempty T.X] :
    ∃ L : List KRPrime,
      T ≺ wreathList (L.map KRPrime.toTransMon) ∧
      ∀ p ∈ L, ∀ G, p = KRPrime.grp G →
        IsSimpleGroup G.carrier ∧ G.carrier ≺ₘ T.M := by
  obtain ⟨L, hdiv, hfac⟩ := krohnRhodes_bar T hT ‹Nonempty T.X›
  exact ⟨L, (bar_divides T).trans hdiv, hfac⟩

/-- **The Krohn–Rhodes theorem**, abstract finite-monoid form [spec
§3.9; blueprint `thm:krohnrhodes-monoid`]: via the regular
representation. -/
theorem krohnRhodes_monoid (M : Type) [Monoid M] [Finite M] :
    ∃ L : List KRPrime,
      M ≺ₘ (wreathList (L.map KRPrime.toTransMon)).M ∧
      ∀ p ∈ L, ∀ G, p = KRPrime.grp G →
        IsSimpleGroup G.carrier ∧ G.carrier ≺ₘ M := by
  have : Nonempty (regular M).X := ⟨(1 : M)⟩
  obtain ⟨L, hdiv, hfac⟩ := krohnRhodes (regular M) (regular_faithful M)
  exact ⟨L, hdiv.monoidDivides, hfac⟩

-- Sanity (spec §6): the main theorem instantiates on a concrete monoid
-- (instances resolve; the `Nonempty` bridge works as documented).
example : ∃ L : List KRPrime,
    regular (ZMod 2) ≺ wreathList (L.map KRPrime.toTransMon) ∧
    ∀ p ∈ L, ∀ G, p = KRPrime.grp G →
      IsSimpleGroup G.carrier ∧ G.carrier ≺ₘ (regular (ZMod 2)).M := by
  have : Nonempty (regular (ZMod 2)).X := ⟨(1 : ZMod 2)⟩
  exact krohnRhodes (regular (ZMod 2)) (regular_faithful _)

end TransMon
end KRTheory
