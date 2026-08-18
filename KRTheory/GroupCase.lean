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

/-- The group half of Krohn–Rhodes [spec §3.7, blueprint
`lem:group-series`]: every finite group's regular representation
strongly divides an iterated wreath of simple-group regulars, each
factor dividing `G`. Fused strong induction on `Nat.card G` — one
maximal proper normal subgroup is peeled per step (no composition-series
artifact; spec §3.7 as amended 2026-08-18). -/
theorem transfGroup_div_wreath_simples (G : Type) [Group G] [Finite G] :
    ∃ L : List BundledFinGroup,
      regular G ≺ wreathList (L.map fun H => regular H.carrier) ∧
      ∀ H ∈ L, IsSimpleGroup H.carrier ∧ H.carrier ≺ₘ G := by
  generalize hcard : Nat.card G = n
  induction n using Nat.strong_induction_on generalizing G with
  | _ n ih =>
    rcases subsingleton_or_nontrivial G with hG | hG
    · -- trivial group: the empty decomposition
      exact ⟨[], by simpa using regular_div_trivialTM_of_subsingleton G,
        by simp⟩
    · obtain ⟨N, hNnorm, hNtop, hmax⟩ :=
        exists_maximal_normal_subgroup (G := G)
      have := hNnorm
      have hsimple := isSimpleGroup_quotient N hNtop hmax
      obtain ⟨L, hLdiv, hLcond⟩ := ih (Nat.card ↥N)
        (by have := card_subgroup_lt_of_ne_top N hNtop; omega)
        ↥N rfl
      refine ⟨L ++ [⟨G ⧸ N⟩], ?_, ?_⟩
      · calc regular G
            ≺ regular ↥N ≀ regular (G ⧸ N) :=
              kaloujnine_krasner_div G N
          _ ≺ wreathList (L.map fun H => regular H.carrier) ≀
                wreathList [regular (G ⧸ N)] :=
              hLdiv.wreath (div_wreathList_singleton _)
          _ ≺ wreathList ((L.map fun H => regular H.carrier) ++
                [regular (G ⧸ N)]) := wreathList_append _ _
          _ = wreathList ((L ++ [(⟨G ⧸ N⟩ : BundledFinGroup)]).map fun H =>
                regular H.carrier) := by simp
      · intro H hH
        rcases List.mem_append.mp hH with h | h
        · obtain ⟨hs, hd⟩ := hLcond H h
          exact ⟨hs, hd.trans (subgroup_monoidDivides N)⟩
        · simp only [List.mem_singleton] at h
          subst h
          exact ⟨hsimple, quotient_monoidDivides N⟩

-- Acceptance sweep (spec §7 row 6): the theorem instantiates at the
-- smallest interesting groups; the factor conditions destructure.
example : ∃ L : List BundledFinGroup,
    regular (Equiv.Perm (Fin 3)) ≺
      wreathList (L.map fun H => regular H.carrier) ∧
    ∀ H ∈ L, IsSimpleGroup H.carrier ∧
      H.carrier ≺ₘ Equiv.Perm (Fin 3) :=
  transfGroup_div_wreath_simples _
-- `Multiplicative (ZMod 5)`: the cyclic group of order 5 (`ZMod 5`'s
-- raw monoid is multiplicative and not a group).
example : ∃ L : List BundledFinGroup,
    regular (Multiplicative (ZMod 5)) ≺
      wreathList (L.map fun H => regular H.carrier) ∧
    ∀ H ∈ L, IsSimpleGroup H.carrier ∧
      H.carrier ≺ₘ Multiplicative (ZMod 5) :=
  transfGroup_div_wreath_simples _

section GroupBar

variable (T : TransMon)

/-!
### Computation bridges

Every goal in this section sits at the projected type
`(resetMonoid T.X ≀ regular T.M).M`, so `w.right`/`w'.right` carry the
opaque stated type `(regular T.M).M` even though they are `T.M` values.
Writing `g * w.right` fresh (as source syntax) then fails to elaborate:
`HMul` instance search won't unfold `regular` to find the underlying
`Monoid T.M` instance, and generic `rw`/`simp` lemmas over such a
product likewise fail their own internal type-check once `w.left`/
`w.right` appear anywhere else in the same goal (a projection on the
opaque `w` cannot be re-verified at `rw`'s restricted transparency).
`mulTM` sidesteps this: a monomorphic function forces the (successful)
*application*-level unification instead of instance search, and the
handful of lemmas below restate the algebra needed by `mul_mem'` and
`group_bar_div` purely in terms of it, so those proofs can close by
`exact`/`congrArg` composition rather than by rewriting the opaque
goal directly. Follows `Reset.lean`'s `show`-then-rewrite discipline;
`mulTM`-avoidance is the extra rung this section needs.
-/

/-- Multiplication in `T.M`, spelled as a named function rather than
`*` for the reason above. -/
private def mulTM (g r : T.M) : T.M := g * r

/-- `mulTM` unfolds to ordinary multiplication. -/
private theorem mulTM_def (g r : T.M) : mulTM T g r = g * r := rfl

/-- `1` is neutral for `mulTM` on the left. -/
private theorem mulTM_one_mul (r : T.M) : mulTM T 1 r = r := by
  rw [mulTM_def, one_mul]

/-- `T.act` unfolds over an `mulTM` product: the `act_mul` identity,
restated through `mulTM` for `equivariant`'s type-A case. -/
private theorem act_mulTM (x : T.X) (a b : T.M) :
    T.act x (mulTM T a b) = T.act (T.act x a) b := by
  rw [mulTM_def, T.act_mul]

/-- `T.act` distributes over an `mulTM`-shaped product with the reset
factor on the right: associativity plus `act_mul`, proved once at
concrete types so `mul_mem'`/`map_mul'` can apply it by `exact` instead
of `rw`-ing a goal that mixes `w.right` with other `T.act`
applications. -/
private theorem act_mul_mulTM (x : T.X) (a b c : T.M) :
    T.act x (a * mulTM T b c) = T.act (T.act x (a * b)) c := by
  rw [mulTM_def, ← mul_assoc, T.act_mul]

/-- Mirror of `act_mul_mulTM` with the `mulTM`-shaped factor on the
left instead of the right. -/
private theorem act_mul_mulTM' (x : T.X) (a b c : T.M) :
    T.act x (mulTM T a b * c) = T.act (T.act x (a * b)) c := by
  rw [mulTM_def, T.act_mul]

/-- The two associativity shapes above land on the same value: lets
`mul_mem'`'s type-B·B case transport between the covering conditions
on `w` and on `w'` without further rewriting. -/
private theorem mulTM_swap_act (x : T.X) (a b c : T.M) :
    T.act x (a * mulTM T b c) = T.act x (mulTM T a b * c) :=
  (act_mul_mulTM T x a b c).trans (act_mul_mulTM' T x a b c).symm

/-- The wreath product's front component of `w * w'`, read at `1` and
re-expressed via `mulTM`: `w`'s own reading point times `w'`'s reading
shifted by `w.right`. The identity `group_bar_div`'s `map_mul'`
case-splits on. -/
private theorem groupBarMap_left_one (w w' : (resetMonoid T.X ≀ regular T.M).M) :
    (w * w').left (1 : T.M) = w.left (1 : T.M) * w'.left w.right := by
  show w.left (1 : T.M) * w'.left (mulTM T 1 w.right) = w.left (1 : T.M) * w'.left w.right
  exact congrArg (w.left (1 : T.M) * w'.left ·) (mulTM_one_mul T w.right)

/-- The type-A/type-B classification conditions for the 2.11 covering
(mirror of `splitSub`'s style in `Reset.lean`):
C1 — the front component has uniform shape;
C2 — for reset fronts, the landing state `x ⊳ (g * r)` is independent
of the sample point `g`. -/
private def groupBarSub : Submonoid (resetMonoid T.X ≀ regular T.M).M where
  carrier := {w | (∀ g g' : T.M, (w.left g = Resets.id ↔ w.left g' = Resets.id)) ∧
    ∀ (g g' : T.M) (x x' : T.X), w.left g = Resets.to x → w.left g' = Resets.to x' →
      have r : T.M := w.right
      T.act x (g * r) = T.act x' (g' * r)}
  one_mem' := by
    refine ⟨fun _ _ => Iff.rfl, fun g g' x x' hx _ => ?_⟩
    change (Resets.id : Resets T.X) = Resets.to x at hx
    exact absurd hx (by simp)
  mul_mem' := by
    rintro w w' ⟨hC1, hC2⟩ ⟨hC1', hC2'⟩
    refine ⟨fun g g' => ?_, fun g g' x x' hgx hg'x' => ?_⟩
    · -- C1: transport the front's id-ness between samples `g`/`g'`,
      -- casing on `w'`'s shape at the shifted points `g * w.right` and
      -- `g' * w.right` (the reset-selection law reduces the product's
      -- front to whichever factor is non-`id`).
      show w.left g * w'.left (mulTM T g w.right) = Resets.id ↔
        w.left g' * w'.left (mulTM T g' w.right) = Resets.id
      rcases hb : w'.left (mulTM T g w.right) with _ | y
      · show w.left g = Resets.id ↔ w.left g' * w'.left (mulTM T g' w.right) = Resets.id
        rcases hb' : w'.left (mulTM T g' w.right) with _ | z
        · show w.left g = Resets.id ↔ w.left g' = Resets.id
          exact hC1 g g'
        · show w.left g = Resets.id ↔ (Resets.to z : Resets T.X) = Resets.id
          exact absurd (hb'.symm.trans ((hC1' (mulTM T g w.right) (mulTM T g' w.right)).mp hb))
            (by simp)
      · show (Resets.to y : Resets T.X) = Resets.id ↔
          w.left g' * w'.left (mulTM T g' w.right) = Resets.id
        rcases hb' : w'.left (mulTM T g' w.right) with _ | z
        · show (Resets.to y : Resets T.X) = Resets.id ↔ w.left g' = Resets.id
          exact absurd (hb.symm.trans ((hC1' (mulTM T g w.right) (mulTM T g' w.right)).mpr hb'))
            (by simp)
        · show (Resets.to y : Resets T.X) = Resets.id ↔ (Resets.to z : Resets T.X) = Resets.id
          exact ⟨fun h => absurd h (by simp), fun h => absurd h (by simp)⟩
    · -- C2: the four cases of the case-map. A·B/B·B (`w'` supplies the
      -- reset at the shifted point) close via `hC2'` + associativity;
      -- B·A (`w` supplies it) closes via `hC2` + `T.act_mul`; the two
      -- mixed shapes are impossible by C1's uniformity on `w'`.
      change w.left g * w'.left (mulTM T g w.right) = Resets.to x at hgx
      change w.left g' * w'.left (mulTM T g' w.right) = Resets.to x' at hg'x'
      show T.act x (g * mulTM T w.right w'.right) = T.act x' (g' * mulTM T w.right w'.right)
      rcases hb : w'.left (mulTM T g w.right) with _ | y
      · rw [hb] at hgx
        change w.left g = Resets.to x at hgx
        rcases hb' : w'.left (mulTM T g' w.right) with _ | z
        · rw [hb'] at hg'x'
          change w.left g' = Resets.to x' at hg'x'
          exact (act_mul_mulTM T x g w.right w'.right).trans
            ((congrArg (T.act · w'.right) (hC2 g g' x x' hgx hg'x')).trans
              (act_mul_mulTM T x' g' w.right w'.right).symm)
        · exact absurd (hb'.symm.trans ((hC1' (mulTM T g w.right) (mulTM T g' w.right)).mp hb))
            (by simp)
      · rw [hb] at hgx
        change (Resets.to y : Resets T.X) = Resets.to x at hgx
        rcases hb' : w'.left (mulTM T g' w.right) with _ | z
        · exact absurd (hb.symm.trans ((hC1' (mulTM T g w.right) (mulTM T g' w.right)).mpr hb'))
            (by simp)
        · rw [hb'] at hg'x'
          change (Resets.to z : Resets T.X) = Resets.to x' at hg'x'
          have hbx : w'.left (mulTM T g w.right) = Resets.to x := hb.trans hgx
          have hb'x' : w'.left (mulTM T g' w.right) = Resets.to x' := hb'.trans hg'x'
          exact (mulTM_swap_act T x g w.right w'.right).trans
            ((hC2' (mulTM T g w.right) (mulTM T g' w.right) x x' hbx hb'x').trans
              (mulTM_swap_act T x' g' w.right w'.right).symm)

/-- The covering's value map: read the front at `1`. Type A (`id`)
covers the original element `w.right`; type B (`to x`) covers the reset
onto the landing state `x ⊳ w.right`. -/
private def groupBarMap (w : (resetMonoid T.X ≀ regular T.M).M) :
    BarMonoid T :=
  match w.left (1 : T.M) with
  | Resets.id => .of w.right
  | Resets.to x => .reset (T.act x w.right)

/-- [DKS] 2.11 [blueprint `lem:group-bar`], strengthened: neither
faithfulness nor nonempty states are needed (spec §3.7 as amended
2026-08-18). If every element of `T.M` is a unit, the barred `T`
strongly divides `U(T.X) ≀ (T.M, T.M)`. The right factor is the
REGULAR representation of `T.M` even when `T.X ≠ T.M` [DKS §2.4]. -/
theorem group_bar_div (hg : ∀ m : T.M, IsUnit m) :
    T.bar ≺ resetMonoid T.X ≀ regular T.M := by
  refine ⟨{ toSubmonoid := groupBarSub T
            stateMap := fun p => T.act p.1 p.2
            monoidMap :=
              { toFun := fun w => groupBarMap T w.1
                map_one' := rfl
                map_mul' := ?_ }
            stateMap_surj := fun x => ⟨(x, (1 : T.M)), T.act_one x⟩
            monoidMap_surj := ?_
            equivariant := ?_ }⟩
  · -- map_mul': the front of the product read at `1` is
    -- `w.left 1 * w'.left w.right` (`groupBarMap_left_one`); case on
    -- `w.left 1` (transported to `w`'s own reading point) and
    -- `w'.left w.right` (transported to `w'`'s own reading point via
    -- `hC1'`), mirroring `BarMonoid`'s four-case multiplication table.
    rintro ⟨w, hC1, hC2⟩ ⟨w', hC1', hC2'⟩
    show (match (w * w').left (1 : T.M) with
        | Resets.id => BarMonoid.of (w * w').right
        | Resets.to x => BarMonoid.reset (T.act x (w * w').right) : BarMonoid T) =
      (match w.left (1 : T.M) with
        | Resets.id => BarMonoid.of w.right
        | Resets.to x => BarMonoid.reset (T.act x w.right) : BarMonoid T) *
      (match w'.left (1 : T.M) with
        | Resets.id => BarMonoid.of w'.right
        | Resets.to x => BarMonoid.reset (T.act x w'.right) : BarMonoid T)
    have hleft : (w * w').left (1 : T.M) = w.left (1 : T.M) * w'.left w.right :=
      groupBarMap_left_one T w w'
    have hright : (w * w').right = w.right * w'.right := wreath_mul_right w w'
    rw [hleft, hright]
    rcases hA : w.left (1 : T.M) with _ | x0 <;> rcases hB : w'.left w.right with _ | y0
    · -- A·A
      have hw'1 : w'.left (1 : T.M) = Resets.id := (hC1' 1 w.right).mpr hB
      rw [hw'1]
      rfl
    · -- A·B: `w'` supplies the reset; align the sample points `w.right`
      -- and `1` via `hC2'`, bridged by `one_mul`.
      rcases hw'1 : w'.left (1 : T.M) with _ | y0'
      · exact absurd ((hC1' 1 w.right).mp hw'1) (by rw [hB]; simp)
      · show (BarMonoid.reset (T.act y0 (w.right * w'.right)) : BarMonoid T) =
          (BarMonoid.of w.right : BarMonoid T) *
            (BarMonoid.reset (T.act y0' w'.right) : BarMonoid T)
        show (BarMonoid.reset (T.act y0 (w.right * w'.right)) : BarMonoid T) =
          (BarMonoid.reset (T.act y0' w'.right) : BarMonoid T)
        exact congrArg BarMonoid.reset
          ((hC2' w.right 1 y0 y0' hB hw'1).trans (congrArg (T.act y0') (one_mul w'.right)))
    · -- B·A: `w` supplies the reset; `T.act_mul` closes it directly.
      have hw'1 : w'.left (1 : T.M) = Resets.id := (hC1' 1 w.right).mpr hB
      rw [hw'1]
      show (BarMonoid.reset (T.act x0 (w.right * w'.right)) : BarMonoid T) =
        (BarMonoid.reset (T.act x0 w.right) : BarMonoid T) * (BarMonoid.of w'.right : BarMonoid T)
      show (BarMonoid.reset (T.act x0 (w.right * w'.right)) : BarMonoid T) =
        (BarMonoid.reset (T.act (T.act x0 w.right) w'.right) : BarMonoid T)
      exact congrArg BarMonoid.reset (T.act_mul x0 w.right w'.right)
    · -- B·B: same alignment as A·B.
      rcases hw'1 : w'.left (1 : T.M) with _ | y0'
      · exact absurd ((hC1' 1 w.right).mp hw'1) (by rw [hB]; simp)
      · show (BarMonoid.reset (T.act y0 (w.right * w'.right)) : BarMonoid T) =
          (BarMonoid.reset (T.act x0 w.right) : BarMonoid T) *
            (BarMonoid.reset (T.act y0' w'.right) : BarMonoid T)
        show (BarMonoid.reset (T.act y0 (w.right * w'.right)) : BarMonoid T) =
          (BarMonoid.reset (T.act y0' w'.right) : BarMonoid T)
        exact congrArg BarMonoid.reset
          ((hC2' w.right 1 y0 y0' hB hw'1).trans (congrArg (T.act y0') (one_mul w'.right)))
  · -- monoidMap_surj: `of m` is covered by the constant-`id` front
    -- (type A, back `m`); `reset x0` is covered by the unit-inverse
    -- front `g ↦ to (x0 ⊳ ↑(hg g).unit⁻¹)` (type B, back `1`) — the
    -- unit hypothesis enters exactly here.
    rintro (m | x0)
    · exact ⟨⟨⟨fun _ => Resets.id, m⟩, fun _ _ => Iff.rfl, fun g g' x x' hx _ =>
        absurd hx (by simp)⟩, rfl⟩
    · have act_inv_eq : ∀ g : T.M,
          T.act (T.act x0 (↑(hg g).unit⁻¹ : T.M)) g = x0 := fun g => by
        rw [← T.act_mul, IsUnit.val_inv_mul, T.act_one]
      refine ⟨⟨⟨fun g => Resets.to (T.act x0 (↑(hg g).unit⁻¹ : T.M)), 1⟩, ?_, ?_⟩, ?_⟩
      · exact fun g g' => ⟨fun h => absurd h (by simp), fun h => absurd h (by simp)⟩
      · intro g g' x x' hgx hg'x'
        show T.act x (g * (1 : T.M)) = T.act x' (g' * (1 : T.M))
        injection hgx with hx
        injection hg'x' with hx'
        rw [mul_one, mul_one, ← hx, ← hx']
        exact (act_inv_eq g).trans (act_inv_eq g').symm
      · show BarMonoid.reset (T.act (T.act x0 (↑(hg 1).unit⁻¹ : T.M)) (1 : T.M)) =
          (BarMonoid.reset x0 : BarMonoid T)
        exact congrArg BarMonoid.reset (act_inv_eq 1)
  · -- equivariant: case on `w.left 1`'s shape, transporting to sample
    -- `g` by C1; type A closes by `act_mulTM`, type B by `hC2` between
    -- samples `1` and `g` (`one_mul` aligns the exponents).
    rintro ⟨x, g⟩ ⟨w, hC1, hC2⟩
    show T.bar.act (T.act x g) (groupBarMap T w) =
      T.act ((resetMonoid T.X).act x (w.left g)) (mulTM T g w.right)
    rw [show groupBarMap T w = match w.left (1 : T.M) with
        | Resets.id => BarMonoid.of w.right
        | Resets.to x1 => BarMonoid.reset (T.act x1 w.right) from rfl]
    rcases hA : w.left (1 : T.M) with _ | x1
    · have hAg : w.left g = Resets.id := (hC1 1 g).mp hA
      show T.bar.act (T.act x g) (BarMonoid.of w.right : BarMonoid T) =
        T.act ((resetMonoid T.X).act x (w.left g)) (mulTM T g w.right)
      rw [hAg]
      show T.act (T.act x g) w.right = T.act x (mulTM T g w.right)
      exact (act_mulTM T x g w.right).symm
    · rcases hAg : w.left g with _ | x2
      · exact absurd ((hC1 1 g).mpr hAg) (by rw [hA]; simp)
      · show T.bar.act (T.act x g) (BarMonoid.reset (T.act x1 w.right) : BarMonoid T) =
          T.act x2 (mulTM T g w.right)
        show T.act x1 w.right = T.act x2 (mulTM T g w.right)
        exact (congrArg (T.act x1) (one_mul w.right)).symm.trans (hC2 1 g x1 x2 hA hAg)

-- Sanity (spec §6): 2.11 at the regular representation of `Perm (Fin 3)`
-- (every element a unit via `Group.isUnit`).
example : (regular (Equiv.Perm (Fin 3))).bar ≺
    resetMonoid (Equiv.Perm (Fin 3)) ≀ regular (Equiv.Perm (Fin 3)) :=
  group_bar_div _ fun g : Equiv.Perm (Fin 3) => Group.isUnit g
-- Guard: `groupBarMap` reads the front AT 1 and moves the target BY
-- `w.right` ON THE RIGHT: for `w = ⟨const (to x₀), m⟩` the value must
-- be `reset (x₀ ⊳ m)`; a transposed definition reading `x₀` alone (or
-- acting on the left) gives `reset x₀ ≠`. Over the noncommutative
-- `regular (Equiv.Perm (Fin 3))` with `x₀ := swap 0 1`, `m := swap 1 2`:
example : groupBarMap (regular (Equiv.Perm (Fin 3)))
    ⟨fun _ => Resets.to (Equiv.swap 0 1), Equiv.swap 1 2⟩ =
    BarMonoid.reset (Equiv.swap 0 1 * Equiv.swap 1 2) := rfl
example : (Equiv.swap 0 1 * Equiv.swap 1 2 : Equiv.Perm (Fin 3)) ≠
    Equiv.swap 0 1 := by decide

end GroupBar

end TransMon
end KRTheory
