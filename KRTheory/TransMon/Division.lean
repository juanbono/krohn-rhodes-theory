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

-- Notation check (spec §8): every non-`scoped`/non-`local` `≺` infix in
-- Mathlib is declared `local` (`Order.Basic`, `Order.Zorn`,
-- `EuclideanDomain.Defs`, etc.), so none of it leaks into scope here;
-- `scoped` below is safe and does not shadow or get shadowed.
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

end StrongDivides

-- Sanity checks (spec §6).
example : trivialTM ≺ trivialTM := .refl _
example : (regular (ZMod 3)) ≺ (regular (ZMod 3)) := .refl _
example (h : trivialTM ≺ regular (ZMod 2)) :
    trivialTM.M ≺ₘ (regular (ZMod 2)).M := h.monoidDivides

end TransMon

end KRTheory
