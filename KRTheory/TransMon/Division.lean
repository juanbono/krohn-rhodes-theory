import KRTheory.TransMon.Basic

/-!
# Division

Monoid division [DKS §2.3]: `M ≺ₘ N` iff `M` is a quotient of a
submonoid of `N` — the "at most as complicated as" preorder. Strong
division of transformation monoids lives in the second half of this
file (Tasks 7–8).
-/

namespace KRTheory

/-- `M ≺ₘ N`: `M` is a homomorphic image of a submonoid of `N`.
[DKS §2.3] -/
def MonoidDivides (M N : Type) [Monoid M] [Monoid N] : Prop :=
  ∃ (N' : Submonoid N) (ψ : N' →* M), Function.Surjective ψ

@[inherit_doc]
scoped infix:50 " ≺ₘ " => MonoidDivides

-- No `Trans` instance (hence no `calc` support) is possible for `≺ₘ`:
-- `Trans` wants a bare relation `α → β → Sort u`, and `MonoidDivides`
-- carries `[Monoid _]` binders between its arguments. Chains use `.trans`.
-- (`≺` on `TransMon` has no such binders; it does get `calc` support.)

namespace MonoidDivides

variable {M N P : Type} [Monoid M] [Monoid N] [Monoid P]

/-- `≺ₘ` is reflexive: `M` divides itself via the top submonoid and its
equivalence with `M`. [DKS §2.3] -/
theorem refl (M : Type) [Monoid M] : M ≺ₘ M :=
  ⟨⊤, Submonoid.topEquiv.toMonoidHom, Submonoid.topEquiv.surjective⟩

/-- A monoid surjected onto by `N` divides `N` (via the top submonoid).
[DKS §2.3] -/
theorem of_surjective (f : N →* M) (hf : Function.Surjective f) :
    M ≺ₘ N :=
  ⟨⊤, f.comp (Submonoid.subtype ⊤), fun m => by
    obtain ⟨n, hn⟩ := hf m
    exact ⟨⟨n, trivial⟩, hn⟩⟩

/-- Any submonoid of `N` divides `N`, via the identity morphism. [DKS §2.3] -/
theorem of_submonoid (N' : Submonoid N) : (↥N') ≺ₘ N :=
  ⟨N', MonoidHom.id ↥N', Function.surjective_id⟩

/-- `≺ₘ` is transitive: pull the submonoid witnessing `N ≺ₘ P` back along
`χ` to a submonoid `Q` of `P'`, push `Q` into `P`, and compose with the
morphism witnessing `M ≺ₘ N`. [DKS §2.3, blueprint `lem:mdiv-preorder`] -/
theorem trans (h₁ : M ≺ₘ N) (h₂ : N ≺ₘ P) : M ≺ₘ P := by
  obtain ⟨N', ψ, hψ⟩ := h₁
  obtain ⟨P', χ, hχ⟩ := h₂
  -- Q : the preimage of N' along χ, as a submonoid of P'
  let Q : Submonoid P' := N'.comap χ
  -- e : Q, viewed inside P via the inclusion P' ↪ P, is isomorphic to Q
  let e : Q ≃* Q.map P'.subtype :=
    Submonoid.equivMapOfInjective Q P'.subtype P'.subtype_injective
  -- morphism: (Q in P) ≃* Q →* N' →* M; surjectivity: each stage is surjective
  exact ⟨Q.map P'.subtype,
    ψ.comp ((χ.submonoidComap N').comp e.symm.toMonoidHom),
    hψ.comp ((χ.submonoidComap_surjective_of_surjective N' hχ).comp e.symm.surjective)⟩

/-- Division cannot increase size: `M` is a surjective image of a
submonoid of `N`, so `|M| ≤ |N'| ≤ |N|`. The point of this lemma is
NEGATIVE evidence — it is what lets `≺ₘ` be *refuted* on concrete
examples, and hence what rules out `≺ₘ` having accidentally been defined
as an always-true relation. See the sanity checks at the foot of this
file. -/
theorem card_le [Finite N] (h : M ≺ₘ N) : Nat.card M ≤ Nat.card N := by
  obtain ⟨N', ψ, hψ⟩ := h
  exact le_trans (Nat.card_le_card_of_surjective ψ hψ)
    (Nat.card_le_card_of_injective _ Subtype.val_injective)

end MonoidDivides

-- Sanity checks (spec §6).
example : ZMod 2 ≺ₘ (ZMod 2 × ZMod 3) :=
  .of_surjective (MonoidHom.fst _ _) Prod.fst_surjective
example : ZMod 6 ≺ₘ ZMod 6 := .refl _

namespace TransMon

/-- A covering witnessing strong division `S ≺ T` [DKS §2.3]: a
submonoid of `T.M` mapping onto `S.M`, equivariantly over a state
surjection `T.X ↠ S.X`. A `Type`-valued witness; the `Prop` is
`StrongDivides`. -/
structure Covering (S T : TransMon) : Type where
  /-- The submonoid `N' ≤ T.M` doing the covering. -/
  toSubmonoid : Submonoid T.M
  /-- `φ`: state surjection, from the big machine down to the small. -/
  stateMap : T.X → S.X
  /-- `ψ`: the monoid surjection. -/
  monoidMap : toSubmonoid →* S.M
  /-- `φ` is onto: every state of `S` is hit from `T`. -/
  stateMap_surj : Function.Surjective stateMap
  /-- `ψ` is onto: every element of `S.M` is hit from `N'`. -/
  monoidMap_surj : Function.Surjective monoidMap
  /-- The covering commutes with the actions: acting in `T` by `n` and
  then projecting the state equals projecting the state first and then
  acting in `S` by the image of `n`. -/
  equivariant : ∀ (y : T.X) (n : toSubmonoid),
    S.act (stateMap y) (monoidMap n) = stateMap (T.act y ↑n)

/-- `S ≺ T`: strong division of transformation monoids [DKS §2.3]. A
`Prop`-valued wrapper around `Covering`, in the same spirit as
`MonoidDivides` wrapping its existential witness. -/
def StrongDivides (S T : TransMon) : Prop := Nonempty (Covering S T)

-- Notation check (spec §8): every `≺` infix in Mathlib is declared
-- `local` (never `scoped` or global) — e.g. in `Order.Basic`,
-- `Order.Zorn`, `EuclideanDomain.Defs` — so none of it leaks into scope
-- here; our `scoped` declaration below is safe and does not shadow or
-- get shadowed.
@[inherit_doc]
scoped infix:50 " ≺ " => StrongDivides

namespace StrongDivides

/-- `≺` is reflexive: every transformation monoid strongly divides
itself, via the identity covering (top submonoid, identity state map,
`Submonoid.topEquiv` as the monoid map). [DKS §2.3] -/
theorem refl (T : TransMon) : T ≺ T :=
  ⟨{ toSubmonoid := ⊤
     stateMap := id
     monoidMap := Submonoid.topEquiv.toMonoidHom
     stateMap_surj := Function.surjective_id
     monoidMap_surj := Submonoid.topEquiv.surjective
     equivariant := fun _y _n => rfl }⟩

/-- Strong division yields division of the underlying monoids — the
lemma through which every abstract corollary is extracted. -/
theorem monoidDivides {S T : TransMon} (h : S ≺ T) : S.M ≺ₘ T.M := by
  obtain ⟨c⟩ := h
  exact ⟨c.toSubmonoid, c.monoidMap, c.monoidMap_surj⟩

/-- Strong division cannot increase the monoid: read off the covering's
`ψ` and count. Finiteness comes from `T`'s bundled `finiteM`, so there is
no side condition. -/
theorem card_le {S T : TransMon} (h : S ≺ T) :
    Nat.card S.M ≤ Nat.card T.M :=
  MonoidDivides.card_le h.monoidDivides

/-- Strong division cannot increase the state set either: `φ` is a
surjection `T.X ↠ S.X`. Together with `card_le` this is what makes `≺`
refutable — see the sanity checks at the foot of this file. -/
theorem card_X_le {S T : TransMon} (h : S ≺ T) :
    Nat.card S.X ≤ Nat.card T.X := by
  obtain ⟨c⟩ := h
  exact Nat.card_le_card_of_surjective c.stateMap c.stateMap_surj

end StrongDivides

/-- Composition of coverings: witnesses transitivity of `≺`.
State maps compose contravariantly (`U.X → T.X → S.X`); the monoid data
is pulled back as in `MonoidDivides.trans` — the covering submonoid of
`U.M` is `ψ₂⁻¹(N₁) ≤ N₂` pushed forward into `U.M`, and the monoid map is
`ψ₂` followed by `ψ₁`. [DKS §2.3, blueprint `lem:sdiv-preorder`] -/
def Covering.comp {S T U : TransMon}
    (c₁ : Covering S T) (c₂ : Covering T U) : Covering S U where
  toSubmonoid :=
    ((c₁.toSubmonoid.comap c₂.monoidMap).map c₂.toSubmonoid.subtype)
  stateMap := c₁.stateMap ∘ c₂.stateMap
  -- `n ↦ ψ₁ (ψ₂ n)`, assembled in three steps: the submonoid above sits
  -- inside `c₂.toSubmonoid` (`inclusion`), on it `c₂.monoidMap` lands in
  -- `c₁.toSubmonoid` (`codRestrict`), and `c₁.monoidMap` finishes the
  -- trip to `S.M`.
  -- `monoidMap_surj` and `equivariant` below rely on this composite
  -- reducing definitionally to `c₁.monoidMap ⟨c₂.monoidMap n, _⟩` through
  -- `Submonoid.inclusion`/`MonoidHom.codRestrict`.
  monoidMap :=
    c₁.monoidMap.comp
      ((c₂.monoidMap.comp
        (Submonoid.inclusion (by rintro _ ⟨y, -, rfl⟩; exact y.2))).codRestrict
          c₁.toSubmonoid (by rintro ⟨_, y, hy, rfl⟩; exact hy))
  stateMap_surj := c₁.stateMap_surj.comp c₂.stateMap_surj
  monoidMap_surj := by
    -- lift `s : S.M` through `ψ₁` to `t ∈ N₁`, then through `ψ₂` to
    -- `u ∈ N₂`; `u` lies in the covering submonoid since `ψ₂ u = t ∈ N₁`.
    intro s
    obtain ⟨t, ht⟩ := c₁.monoidMap_surj s
    obtain ⟨u, hu⟩ := c₂.monoidMap_surj ↑t
    have hmem : c₂.monoidMap u ∈ c₁.toSubmonoid := by rw [hu]; exact t.2
    refine ⟨⟨↑u, u, hmem, rfl⟩, ?_⟩
    exact (congrArg c₁.monoidMap (Subtype.ext hu :
      (⟨c₂.monoidMap u, hmem⟩ : c₁.toSubmonoid) = t)).trans ht
  equivariant := by
    -- every element of the composed submonoid is `↑n` for some
    -- `n ∈ ψ₂⁻¹(N₁)`; then chase `c₁.equivariant` at the `T`-level and
    -- `c₂.equivariant` at the `U`-level.
    rintro y ⟨_, n, hn, rfl⟩
    exact (c₁.equivariant _ ⟨c₂.monoidMap n, hn⟩).trans
      (congrArg c₁.stateMap (c₂.equivariant y n))

/-- `≺` is transitive: compose the witnessing coverings. [DKS §2.3,
blueprint `lem:sdiv-preorder`] -/
theorem StrongDivides.trans {S T U : TransMon}
    (h₁ : S ≺ T) (h₂ : T ≺ U) : S ≺ U := by
  obtain ⟨c₁⟩ := h₁; obtain ⟨c₂⟩ := h₂
  exact ⟨c₁.comp c₂⟩

/-- Registers `≺` with the `calc` tactic, so chains of strong-division
steps can be written as `calc`-blocks instead of explicit `.trans`
composition. -/
instance : Trans StrongDivides StrongDivides StrongDivides := ⟨StrongDivides.trans⟩

open scoped Classical in
/-- `c.monoidMap` totalized to all of `T.M`, sending non-members to `1`.
Lets fiber-compatibility conditions be stated without dependent
membership proofs (used by wreath monotonicity). Classical `dite`. -/
noncomputable def Covering.extMap {S T : TransMon} (c : Covering S T) :
    T.M → S.M := fun t =>
  if h : t ∈ c.toSubmonoid then c.monoidMap ⟨t, h⟩ else 1

/-- `extMap` agrees with `c.monoidMap` on members of the covering
submonoid — the defining case of the totalization. -/
theorem Covering.extMap_of_mem {S T : TransMon} (c : Covering S T)
    {t : T.M} (h : t ∈ c.toSubmonoid) :
    c.extMap t = c.monoidMap ⟨t, h⟩ := dif_pos h

/-- `extMap` recovers `c.monoidMap` exactly on (the coercion of) the
covering submonoid. -/
theorem Covering.extMap_coe {S T : TransMon} (c : Covering S T)
    (n : c.toSubmonoid) : c.extMap ↑n = c.monoidMap n := by
  rw [c.extMap_of_mem n.2]

/-- The totalization `extMap` preserves the unit: `1` lies in every
covering submonoid, where `extMap` agrees with the monoid hom
`c.monoidMap`. -/
theorem Covering.extMap_one {S T : TransMon} (c : Covering S T) :
    c.extMap 1 = 1 := (c.extMap_coe 1).trans (map_one _)

/-- `extMap` is multiplicative on pairs drawn from the covering
submonoid, inherited from `c.monoidMap`'s multiplicativity there. -/
theorem Covering.extMap_mul_of_mem {S T : TransMon} (c : Covering S T)
    {a b : T.M} (ha : a ∈ c.toSubmonoid) (hb : b ∈ c.toSubmonoid) :
    c.extMap (a * b) = c.extMap a * c.extMap b := by
  rw [c.extMap_of_mem (mul_mem ha hb), c.extMap_of_mem ha, c.extMap_of_mem hb,
    ← map_mul]
  rfl

/-- The covering's equivariance condition, restated through `extMap` for
elements of the covering submonoid. -/
theorem Covering.act_extMap {S T : TransMon} (c : Covering S T)
    {t : T.M} (h : t ∈ c.toSubmonoid) (y : T.X) :
    S.act (c.stateMap y) (c.extMap t) = c.stateMap (T.act y t) := by
  rw [c.extMap_of_mem h]
  exact c.equivariant y ⟨t, h⟩

/-- A chosen section of the state surjection: `c.stateMap (c.sect x) = x`.
Noncomputable (choice); used by wreath monotonicity and, later, the
group case. -/
noncomputable def Covering.sect {S T : TransMon} (c : Covering S T) :
    S.X → T.X := Function.surjInv c.stateMap_surj

/-- The defining property of the section: `stateMap` retracts it. -/
@[simp]
theorem Covering.stateMap_sect {S T : TransMon} (c : Covering S T)
    (x : S.X) : c.stateMap (c.sect x) = x :=
  Function.surjInv_eq c.stateMap_surj x

-- Sanity checks (spec §6).
example : trivialTM ≺ trivialTM := .refl _
example : (regular (ZMod 3)) ≺ (regular (ZMod 3)) := .refl _
example (h : trivialTM ≺ regular (ZMod 2)) :
    trivialTM.M ≺ₘ (regular (ZMod 2)).M := h.monoidDivides
example {S T U : TransMon} (h₁ : S ≺ T) (h₂ : T ≺ U) : S ≺ U :=
  h₁.trans h₂

-- NEGATIVE sanity checks (spec §6, negative direction). Every check
-- above is affirmative — they would all still pass if a surjectivity
-- field were dropped from `Covering`, which would make `≺` near-trivial
-- and the Krohn–Rhodes statement nearly content-free. These two witness
-- that `≺` and `≺ₘ` are genuinely refutable relations.
example : ¬ (regular (ZMod 3) ≺ trivialTM) := by
  intro h
  have h3 : Nat.card (regular (ZMod 3)).M = 3 := by
    show Nat.card (ZMod 3) = 3
    rw [Nat.card_eq_fintype_card, ZMod.card]
  have h1 : Nat.card trivialTM.M = 1 := by
    show Nat.card PUnit = 1
    exact Nat.card_unique
  have hle := StrongDivides.card_le h
  rw [h3, h1] at hle
  omega

example : ¬ (ZMod 3 ≺ₘ PUnit) := by
  intro h
  have hle := MonoidDivides.card_le h
  rw [show Nat.card (ZMod 3) = 3 by rw [Nat.card_eq_fintype_card, ZMod.card],
    show Nat.card PUnit = 1 from Nat.card_unique] at hle
  omega

end TransMon

end KRTheory
