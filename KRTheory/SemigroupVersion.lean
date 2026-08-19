import KRTheory.KrohnRhodes

/-!
# The semigroup form of Krohn–Rhodes

The classical 1965 statement [spec §1 item 3, §3.9; blueprint
`ch:semigroup`]: every finite semigroup divides an iterated wreath
product of flip-flops and simple groups. Derived from the monoid form
by adjoining an identity (`WithOne`).

Semigroup division `≺ₛ` mirrors `≺ₘ` (`Division.lean`) with
subsemigroups and `MulHom`s in place of submonoids and `MonoidHom`s.
-/

namespace KRTheory

/-- `S ≺ₛ T` [DKS §2.3, blueprint `def:semdiv`]: `S` is a homomorphic
image of a subsemigroup of `T`. -/
def SemigroupDivides (S T : Type) [Semigroup S] [Semigroup T] : Prop :=
  ∃ (T' : Subsemigroup T) (ψ : T' →ₙ* S), Function.Surjective ψ

@[inherit_doc]
scoped infix:50 " ≺ₛ " => SemigroupDivides

namespace SemigroupDivides

variable {S T U : Type} [Semigroup S] [Semigroup T] [Semigroup U]

/-- `≺ₛ` is reflexive, via the top subsemigroup [blueprint
`lem:semdiv-preorder`]. -/
theorem refl (S : Type) [Semigroup S] : S ≺ₛ S :=
  ⟨⊤, { toFun := fun x => x.1, map_mul' := fun _ _ => rfl }, fun s => ⟨⟨s, trivial⟩, rfl⟩⟩

/-- Subsemigroups divide their ambient semigroup [blueprint
`lem:semdiv-preorder`]. -/
theorem of_subsemigroup (T' : Subsemigroup T) : (↥T') ≺ₛ T :=
  ⟨T', MulHom.id ↥T', Function.surjective_id⟩

/-- `≺ₛ` is transitive [blueprint `lem:semdiv-preorder`]: pull the
subsemigroup witnessing `T ≺ₛ U` back along `χ` and push it into `U`,
mirroring `MonoidDivides.trans`. Mathlib supplies
`submonoidComap_surjective_of_surjective` for monoids but has no
subsemigroup analogue, so that step is proved inline (spec §9
upstreaming candidate). -/
theorem trans (h₁ : S ≺ₛ T) (h₂ : T ≺ₛ U) : S ≺ₛ U := by
  obtain ⟨T', ψ, hψ⟩ := h₁
  obtain ⟨U', χ, hχ⟩ := h₂
  -- Q : the preimage of T' along χ, as a subsemigroup of U'
  let Q : Subsemigroup U' := T'.comap χ
  -- e : Q, viewed inside U via the inclusion U' ↪ U, is isomorphic to Q
  let e : Q ≃* Q.map (MulMemClass.subtype U') :=
    Subsemigroup.equivMapOfInjective Q (MulMemClass.subtype U')
      (MulMemClass.subtype_injective U')
  have hcomap : Function.Surjective (χ.subsemigroupComap T') := by
    rintro ⟨t, ht⟩
    obtain ⟨u, hu⟩ := hχ t
    refine ⟨⟨u, ?_⟩, Subtype.ext hu⟩
    show χ u ∈ T'
    rw [hu]; exact ht
  exact ⟨Q.map (MulMemClass.subtype U'),
    ψ.comp ((χ.subsemigroupComap T').comp e.symm.toMulHom),
    hψ.comp (hcomap.comp e.symm.surjective)⟩

end SemigroupDivides

/-- Monoid division is semigroup division [blueprint
`lem:semdiv-of-mdiv`]: forget the units. -/
theorem monoidDivides_semigroupDivides {M N : Type} [Monoid M] [Monoid N]
    (h : M ≺ₘ N) : M ≺ₛ N := by
  obtain ⟨N', ψ, hψ⟩ := h
  exact ⟨N'.toSubsemigroup, ψ.toMulHom, hψ⟩

/-- Adjoining an identity is harmless [blueprint `lem:withone-transfer`]:
`S ≺ₛ S¹`. The copy of `S` inside `WithOne S` is a subsemigroup (a
product of two non-identity elements is non-identity), and the
coercion's inverse is a surjective homomorphism onto `S`. -/
theorem withOne_transfer (S : Type) [Semigroup S] : S ≺ₛ WithOne S := by
  refine ⟨{ carrier := Set.range ((↑) : S → WithOne S)
            mul_mem' := ?_ },
    { toFun := fun x => Classical.choose x.2
      map_mul' := ?_ }, ?_⟩
  · rintro a b ⟨x, rfl⟩ ⟨y, rfl⟩
    exact ⟨x * y, WithOne.coe_mul x y⟩
  · rintro a b
    -- both sides are the unique `S`-preimages; compare after coercion
    apply WithOne.coe_inj.mp
    rw [WithOne.coe_mul, Classical.choose_spec a.2, Classical.choose_spec b.2,
      Classical.choose_spec (a * b).2]
    rfl
  · intro s
    refine ⟨⟨(s : WithOne S), s, rfl⟩, ?_⟩
    apply WithOne.coe_inj.mp
    exact Classical.choose_spec (⟨(s : WithOne S), s, rfl⟩ :
      { x : WithOne S // x ∈ Set.range ((↑) : S → WithOne S) }).2

/-- Factor transport [blueprint `lem:semdiv-group-withone`, spec §3.9 as
resolved 2026-08-19]: a NONTRIVIAL group dividing `S¹` as a monoid
already divides `S` as a semigroup. Nontriviality is load-bearing — it
supplies the preimage of `1` as a product `h * h⁻¹` — and comes free
from `IsSimpleGroup` at the call site. -/
theorem semigroupDivides_of_monoidDivides_withOne {G S : Type} [Group G]
    [Nontrivial G] [Semigroup S] (h : G ≺ₘ WithOne S) : G ≺ₛ S := by
  obtain ⟨N', ψ, hψ⟩ := h
  have hmul : ∀ {x y : S}, (x : WithOne S) ∈ N' → (y : WithOne S) ∈ N' →
      ((x * y : S) : WithOne S) ∈ N' := by
    intro x y hx hy
    rw [WithOne.coe_mul]
    exact N'.mul_mem hx hy
  -- every non-identity element of `G` is hit by an `S`-element of `N'`
  have hne : ∀ g : G, g ≠ 1 → ∃ x : S, ∃ hx : (x : WithOne S) ∈ N', ψ ⟨_, hx⟩ = g := by
    intro g hg
    obtain ⟨n, hn⟩ := hψ g
    have hn1 : n.1 ≠ 1 := by
      intro h1
      apply hg
      rw [← hn]
      have : n = 1 := Subtype.ext h1
      rw [this, map_one]
    obtain ⟨x, hx⟩ := WithOne.ne_one_iff_exists.mp hn1
    refine ⟨x, hx ▸ n.2, ?_⟩
    rw [← hn]
    congr 1
    exact Subtype.ext hx
  refine ⟨{ carrier := {x : S | (x : WithOne S) ∈ N'}
            mul_mem' := fun hx hy => hmul hx hy },
    { toFun := fun x => ψ ⟨(x.1 : WithOne S), x.2⟩
      map_mul' := ?_ }, ?_⟩
  · intro a b
    rw [← map_mul]
    congr 1
  · intro g
    rcases eq_or_ne g 1 with rfl | hg
    · -- the identity: `h * h⁻¹` for any `h ≠ 1` — this is why `Nontrivial` is needed
      obtain ⟨h, hh⟩ := exists_ne (1 : G)
      obtain ⟨x, hx, hxg⟩ := hne h hh
      obtain ⟨y, hy, hyg⟩ := hne h⁻¹ (inv_ne_one.mpr hh)
      refine ⟨⟨x * y, hmul hx hy⟩, ?_⟩
      show ψ ⟨((x * y : S) : WithOne S), _⟩ = 1
      have : (⟨((x * y : S) : WithOne S), hmul hx hy⟩ : N') = ⟨_, hx⟩ * ⟨_, hy⟩ :=
        Subtype.ext (WithOne.coe_mul x y)
      rw [this, map_mul, hxg, hyg, mul_inv_cancel]
    · obtain ⟨x, hx, hxg⟩ := hne g hg
      exact ⟨⟨x, hx⟩, hxg⟩

open TransMon in
/-- **The Krohn–Rhodes theorem**, classical semigroup form (Krohn–Rhodes
1965) [spec §1 item 3, §3.9; blueprint `thm:krohnrhodes-semigroup`]:
every finite semigroup divides an iterated wreath product of flip-flops
and regular representations of finite simple groups, each group factor
dividing `S`. `Finite (WithOne S)` is supplied locally —
instance search does not cross the `WithOne`/`Option` synonym. -/
theorem krohnRhodes_semigroup (S : Type) [Semigroup S] [Finite S] :
    ∃ L : List KRPrime,
      S ≺ₛ (wreathList (L.map KRPrime.toTransMon)).M ∧
      ∀ p ∈ L, ∀ G, p = KRPrime.grp G →
        IsSimpleGroup G.carrier ∧ G.carrier ≺ₛ S := by
  have : Finite (WithOne S) := inferInstanceAs (Finite (Option S))
  obtain ⟨L, hdiv, hfac⟩ := krohnRhodes_monoid (WithOne S)
  refine ⟨L, (withOne_transfer S).trans (monoidDivides_semigroupDivides hdiv), ?_⟩
  intro p hp G hpG
  obtain ⟨hsimple, hdivG⟩ := hfac p hp G hpG
  have : Nontrivial G.carrier := hsimple.toNontrivial
  exact ⟨hsimple, semigroupDivides_of_monoidDivides_withOne hdivG⟩

-- Sanity (spec §6): the theorem instantiates on a concrete finite
-- semigroup (every finite monoid is one).
open TransMon in
example : ∃ L : List KRPrime,
    ZMod 6 ≺ₛ (wreathList (L.map KRPrime.toTransMon)).M ∧
    ∀ p ∈ L, ∀ G, p = KRPrime.grp G →
      IsSimpleGroup G.carrier ∧ G.carrier ≺ₛ ZMod 6 :=
  krohnRhodes_semigroup _

end KRTheory
