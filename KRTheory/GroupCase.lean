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

section KaloujnineKrasner

variable (G : Type) [Group G] [Finite G] (N : Subgroup G) [N.Normal]

/-- The KK cocycle: front coordinate of the classical embedding at
section point `q`: `s(q) · g · s(q·ḡ)⁻¹ ∈ N`, with `s := Quotient.out`.
`Classical.choice` enters through `out` and stays inside this section's
private defs. -/
private noncomputable def kkCocycle (g : G) (q : G ⧸ N) : ↥N :=
  ⟨q.out * g * ((q * QuotientGroup.mk g).out)⁻¹, by
    have : QuotientGroup.mk
        (q.out * g * ((q * QuotientGroup.mk g).out)⁻¹) = (1 : G ⧸ N) := by
      rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv,
        QuotientGroup.out_eq', QuotientGroup.out_eq']
      group
    exact (QuotientGroup.eq_one_iff _).mp this⟩

/-- The KK embedding `G → ↥N ≀ (G ⧸ N)` (monoid part): cocycle front,
projection back. A `MonoidHom` via the cocycle identity. -/
private noncomputable def kkEmbed :
    G →* WreathMonoid (regular ↥N) (regular (G ⧸ N)) where
  toFun g := ⟨fun q => kkCocycle G N g q, QuotientGroup.mk g⟩
  map_one' := by
    have hleft : kkCocycle G N 1 = fun _ : G ⧸ N => (1 : ↥N) := by
      funext q
      apply Subtype.ext
      show q.out * (1 : G) * ((q * QuotientGroup.mk (1 : G)).out)⁻¹ = (1 : G)
      rw [QuotientGroup.mk_one, mul_one, mul_one]
      group
    apply WreathMonoid.ext
    · exact hleft
    · show QuotientGroup.mk (1 : G) = (1 : G ⧸ N)
      rfl
  map_mul' := by
    intro g h
    have hleft : kkCocycle G N (g * h) =
        fun q => kkCocycle G N g q * kkCocycle G N h (q * QuotientGroup.mk g) := by
      funext q
      apply Subtype.ext
      show q.out * (g * h) * ((q * QuotientGroup.mk (g * h)).out)⁻¹
          = (q.out * g * ((q * QuotientGroup.mk g).out)⁻¹) *
            ((q * QuotientGroup.mk g).out * h *
              ((q * QuotientGroup.mk g * QuotientGroup.mk h).out)⁻¹)
      rw [QuotientGroup.mk_mul]
      group
    apply WreathMonoid.ext
    · exact hleft
    · show QuotientGroup.mk (g * h) = QuotientGroup.mk g * QuotientGroup.mk h
      rfl

/-- The explicit retraction recovering `g` from `kkEmbed g`:
`s(1̄)⁻¹ · (front at 1̄) · s(back)`. -/
private noncomputable def kkRetract
    (w : WreathMonoid (regular ↥N) (regular (G ⧸ N))) : G :=
  ((1 : G ⧸ N).out)⁻¹ * N.subtype (w.left (1 : G ⧸ N)) * (w.right).out

private theorem kkRetract_kkEmbed (g : G) :
    kkRetract G N (kkEmbed G N g) = g := by
  show ((1 : G ⧸ N).out)⁻¹ *
      ((1 : G ⧸ N).out * g * (((1 : G ⧸ N) * QuotientGroup.mk g).out)⁻¹) *
      ((QuotientGroup.mk g : G ⧸ N)).out = g
  rw [one_mul]
  group

/-- Kaloujnine–Krasner as a strong division [spec §3.7, blueprint
`lem:kaloujnine-krasner`]: `(G,G) ≺ (N,N) ≀ (G⧸N, G⧸N)`. States map by
`(n, q) ↦ n · s(q)`; the covering submonoid is the embedding's range,
inverted by the explicit retraction. -/
theorem kaloujnine_krasner_div :
    regular G ≺ regular ↥N ≀ regular (G ⧸ N) := by
  refine ⟨{ toSubmonoid := MonoidHom.mrange (kkEmbed G N)
            stateMap := fun p => N.subtype p.1 * (p.2).out
            monoidMap :=
              { toFun := fun w => kkRetract G N w.1
                map_one' := by
                  show kkRetract G N (1 : ↥(MonoidHom.mrange (kkEmbed G N))).1 = (1 : G)
                  have h1 : ((1 : ↥(MonoidHom.mrange (kkEmbed G N))).1 :
                      WreathMonoid (regular ↥N) (regular (G ⧸ N))) = kkEmbed G N 1 :=
                    (map_one (kkEmbed G N)).symm
                  rw [h1]
                  exact kkRetract_kkEmbed G N 1
                map_mul' := by
                  rintro ⟨_, g, rfl⟩ ⟨_, h, rfl⟩
                  show kkRetract G N _
                      = kkRetract G N (kkEmbed G N g) * kkRetract G N (kkEmbed G N h)
                  rw [kkRetract_kkEmbed, kkRetract_kkEmbed]
                  show kkRetract G N (kkEmbed G N g * kkEmbed G N h) = g * h
                  rw [← map_mul]
                  exact kkRetract_kkEmbed G N (g * h) }
            stateMap_surj := ?_
            monoidMap_surj := fun g =>
              ⟨⟨kkEmbed G N g, g, rfl⟩, kkRetract_kkEmbed G N g⟩
            equivariant := ?_ }⟩
  · -- surjectivity of φ: g = (g * s(π g)⁻¹) * s(π g), first factor ∈ N
    show ∀ g : G, ∃ y : ↥N × (G ⧸ N), (y.1 : G) * y.2.out = g
    intro g
    refine ⟨⟨⟨g * (((QuotientGroup.mk g : G ⧸ N)).out)⁻¹, ?_⟩,
      QuotientGroup.mk g⟩, ?_⟩
    · exact (QuotientGroup.eq_one_iff _).mp (by
        rw [QuotientGroup.mk_mul, QuotientGroup.mk_inv,
          QuotientGroup.out_eq']
        group)
    · show g * ((QuotientGroup.mk g : G ⧸ N).out)⁻¹ *
        ((QuotientGroup.mk g : G ⧸ N)).out = g
      group
  · -- equivariance: φ((n,q) ⊳ kkEmbed g) = φ(n,q) * g
    show ∀ (y : ↥N × (G ⧸ N)) (m : ↥(MonoidHom.mrange (kkEmbed G N))),
        (y.1 : G) * y.2.out * kkRetract G N m.1
          = N.subtype ((regular ↥N ≀ regular (G ⧸ N)).act y m.1).1
              * ((regular ↥N ≀ regular (G ⧸ N)).act y m.1).2.out
    rintro ⟨n, q⟩ ⟨_, g, rfl⟩
    show (n : G) * q.out * kkRetract G N (kkEmbed G N g)
        = ((n * kkCocycle G N g q : ↥N) : G) * (q * QuotientGroup.mk g).out
    rw [kkRetract_kkEmbed]
    show (n : G) * q.out * g
        = (n : G) * (kkCocycle G N g q : G) * (q * QuotientGroup.mk g).out
    show (n : G) * q.out * g
        = (n : G) * (q.out * g * ((q * QuotientGroup.mk g).out)⁻¹) *
          (q * QuotientGroup.mk g).out
    group

end KaloujnineKrasner

-- Acceptance (spec §7 row 6 shape): the classic concrete instance.
-- `decide`-guards are not possible in this section (`Quotient.out` is
-- noncomputable); the twisted monoid laws pin the chirality instead
-- (Covering.wreath precedent, plan Decision 6).
example : regular (Equiv.Perm (Fin 3)) ≺
    regular ↥(alternatingGroup (Fin 3)) ≀
      regular (Equiv.Perm (Fin 3) ⧸ alternatingGroup (Fin 3)) :=
  kaloujnine_krasner_div _ _

end TransMon
end KRTheory
