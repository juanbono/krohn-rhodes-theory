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

end KRTheory
