import KRTheory.TransMon.WreathDivision
import KRTheory.TransMon.Bar
import KRTheory.TransMon.Reset
-- Only for `alternatingGroup`, used in the examples below; `Subgroup`,
-- `QuotientGroup`, and `IsSimpleGroup` are already reachable transitively
-- through the three imports above.
import Mathlib.GroupTheory.SpecificGroups.Alternating

/-!
# The group case

The base case of the Krohn–Rhodes induction [spec §3.7, blueprint
`ch:groupcase`]: every finite group's regular representation divides an
iterated wreath product of simple-group regulars
(`transfGroup_div_wreath_simples`, via Kaloujnine–Krasner and a fused
composition-series induction), and [DKS] 2.11 (`group_bar_div`): barred
transformation groups divide a reset-monoid/regular wreath.

Group-ness of a `TransMon` is the Prop `∀ m : T.M, IsUnit m` — a
`[Group T.M]` instance would diamond with the bundled `monoidM`
(spec §3.7 as amended 2026-08-18). The Kaloujnine–Krasner section uses
`Quotient.out` (classical choice) quarantined inside private defs.
-/

namespace KRTheory
namespace TransMon

/-- A bundled finite group [blueprint `def:bundledfingroup`]: the factor
datatype for group decompositions. Lives here rather than in
`KrohnRhodes.lean` (spec §4.3 as amended): the factor list of
`transfGroup_div_wreath_simples` is exactly a `List BundledFinGroup`,
and M8's `KRPrime.grp` consumes it unchanged. -/
structure BundledFinGroup : Type 1 where
  /-- The underlying type. -/
  carrier : Type
  /-- The group structure. -/
  [group : Group carrier]
  /-- Finiteness. -/
  [finite : Finite carrier]

attribute [instance] BundledFinGroup.group BundledFinGroup.finite

variable {G : Type} [Group G] [Finite G]

/-- Every nontrivial finite group has a maximal proper normal subgroup
[blueprint `lem:max-normal`]: the proper normal subgroups form a
nonempty (`⊥`) subset of the finite subgroup lattice. -/
theorem exists_maximal_normal_subgroup [Nontrivial G] :
    ∃ N : Subgroup G, N.Normal ∧ N ≠ ⊤ ∧
      ∀ K : Subgroup G, K.Normal → N < K → K = ⊤ := by
  obtain ⟨N, ⟨hN, hNtop⟩, hmax⟩ :=
    (wellFounded_gt (α := Subgroup G)).has_min
      {K : Subgroup G | K.Normal ∧ K ≠ ⊤} ⟨⊥, inferInstance, bot_ne_top⟩
  refine ⟨N, hN, hNtop, fun K hK hNK => ?_⟩
  by_contra hKtop
  exact hmax K ⟨hK, hKtop⟩ hNK

omit [Finite G] in
/-- The quotient by a maximal proper normal subgroup is simple
[blueprint `lem:simple-quotient`]: normal subgroups of `G ⧸ N` pull
back along the projection to normal subgroups of `G` containing `N`. -/
theorem isSimpleGroup_quotient (N : Subgroup G) [N.Normal]
    (hNtop : N ≠ ⊤)
    (hmax : ∀ K : Subgroup G, K.Normal → N < K → K = ⊤) :
    IsSimpleGroup (G ⧸ N) := by
  have : Nontrivial (G ⧸ N) := QuotientGroup.nontrivial_iff.mpr hNtop
  refine ⟨fun H hH => ?_⟩
  set K := Subgroup.comap (QuotientGroup.mk' N) H with hKdef
  have hKnormal : K.Normal := hH.comap _
  have hNK : N ≤ K := by
    have h := Subgroup.ker_le_comap (QuotientGroup.mk' N) H
    rw [QuotientGroup.ker_mk' N] at h
    exact h
  have hHmap : H = Subgroup.map (QuotientGroup.mk' N) K :=
    (Subgroup.map_comap_eq_self_of_surjective
      (QuotientGroup.mk'_surjective N) H).symm
  rcases eq_or_lt_of_le hNK with heq | hlt
  · left
    have hmapN : Subgroup.map (QuotientGroup.mk' N) N = ⊥ := by
      rw [eq_bot_iff]
      rintro x ⟨g, hg, rfl⟩
      simpa using (QuotientGroup.eq_one_iff g).mpr hg
    rw [hHmap, ← heq, hmapN]
  · right
    rw [hHmap, hmax K hKnormal hlt, ← MonoidHom.range_eq_map]
    exact MonoidHom.range_eq_top.mpr (QuotientGroup.mk'_surjective N)

omit [Finite G] in
/-- A subgroup's carrier divides the mother group as a monoid
[blueprint `lem:subgroup-mdiv`]: the identity correspondence on
`N.toSubmonoid`. -/
theorem subgroup_monoidDivides (N : Subgroup G) : ↥N ≺ₘ G := by
  exact ⟨N.toSubmonoid,
    { toFun := fun x => ⟨x.1, x.2⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl },
    fun x => ⟨⟨x.1, x.2⟩, rfl⟩⟩

omit [Finite G] in
/-- The quotient by a normal subgroup divides the mother group
[blueprint `lem:subgroup-mdiv`]: the projection is a surjective
homomorphism. -/
theorem quotient_monoidDivides (N : Subgroup G) [N.Normal] :
    (G ⧸ N) ≺ₘ G := by
  exact .of_surjective (QuotientGroup.mk' N) (QuotientGroup.mk'_surjective N)

/-- Proper subgroups are strictly smaller — the measure of the fused
induction. Derived from the card product formula: the quotient is
nontrivial, so it contributes a factor `≥ 2`. -/
theorem card_subgroup_lt_of_ne_top (N : Subgroup G) [N.Normal]
    (h : N ≠ ⊤) : Nat.card ↥N < Nat.card G := by
  have h2 : 1 < Nat.card (G ⧸ N) :=
    Finite.one_lt_card_iff_nontrivial.mpr
      (QuotientGroup.nontrivial_iff.mpr h)
  have hpos : 0 < Nat.card ↥N := Nat.card_pos
  calc Nat.card ↥N = 1 * Nat.card ↥N := (one_mul _).symm
    _ < Nat.card (G ⧸ N) * Nat.card ↥N := by
        exact Nat.mul_lt_mul_of_lt_of_le h2 le_rfl hpos
    _ = Nat.card G :=
        (Subgroup.card_eq_card_quotient_mul_card_subgroup N).symm

/-- A subsingleton group's regular representation divides the trivial
transformation monoid — the base of the fused induction. -/
theorem regular_div_trivialTM_of_subsingleton (G : Type) [Group G]
    [Finite G] [Subsingleton G] : regular G ≺ trivialTM := by
  have : Subsingleton (regular G).X := ‹Subsingleton G›
  have : Subsingleton (regular G).M := ‹Subsingleton G›
  exact ⟨{ toSubmonoid := ⊤
           stateMap := fun _ => (1 : G)
           monoidMap :=
             { toFun := fun _ => (1 : G)
               map_one' := rfl
               map_mul' := fun _ _ => (one_mul 1).symm }
           stateMap_surj := fun x => ⟨PUnit.unit, Subsingleton.elim _ _⟩
           monoidMap_surj := fun m => ⟨⟨PUnit.unit, trivial⟩,
             Subsingleton.elim _ _⟩
           equivariant := fun _ _ => Subsingleton.elim _ _ }⟩

-- Sanity (spec §6): the smallest bundled groups; a concrete maximal
-- normal witness call; the division feeders on `Perm (Fin 3)` and its
-- alternating subgroup.
-- (`Multiplicative` because `ZMod 2`'s raw monoid is multiplicative and
-- not a group; the additive group made multiplicative is.)
example : (⟨Multiplicative (ZMod 2)⟩ : BundledFinGroup).carrier =
    Multiplicative (ZMod 2) := rfl
example : ∃ N : Subgroup (Equiv.Perm (Fin 3)), N.Normal ∧ N ≠ ⊤ ∧
    ∀ K : Subgroup (Equiv.Perm (Fin 3)), K.Normal → N < K → K = ⊤ :=
  exists_maximal_normal_subgroup
example : ↥(alternatingGroup (Fin 3)) ≺ₘ Equiv.Perm (Fin 3) :=
  subgroup_monoidDivides _
example : (Equiv.Perm (Fin 3) ⧸ alternatingGroup (Fin 3)) ≺ₘ
    Equiv.Perm (Fin 3) := quotient_monoidDivides _

end TransMon
end KRTheory
