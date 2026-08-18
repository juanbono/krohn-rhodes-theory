import KRTheory.TransMon.Division

/-!
# Local divisors

The local divisor `Mc = cM ∩ Mc` at `c : M` [DKS §2.5, blueprint
`ch:localdivisor`]: product `(mc) ∘ (cn) = mcn`, identity `c`. The
recursion of the Krohn–Rhodes induction descends into local divisors;
the three lemmas here (faithfulness [DKS 2.13], cardinality drop,
division) are what make that descent sound — see spec §3.6.

The carrier is a fresh structure, NOT a subtype of `M`: the product is
not the restriction of `M`'s product, so a `Monoid` instance on a
subtype would be a diamond trap (same rationale as `WreathMonoid`).
Two sites read a decomposition witness via `Classical.choose`: the
product (quarantined by `mul_spec`/`mul_spec_right`) and the action
(quarantined by `localDivisor_act_spec`) — nothing downstream ever
mentions the choice directly (spec §8 mitigation).
-/

namespace KRTheory
namespace TransMon

variable {M : Type} [Monoid M] [Finite M]

/-- An element of the local divisor at `c`: a value in `cM ∩ Mc`
[DKS §2.5, blueprint `def:localdiv`]. -/
@[ext]
structure LocalDivisor (c : M) : Type where
  /-- The underlying element of `M`. -/
  val : M
  /-- Membership in `cM`. -/
  mem_left : ∃ m, val = c * m
  /-- Membership in `Mc`. -/
  mem_right : ∃ m, val = m * c

namespace LocalDivisor

variable {c : M}

/-- As a type, `LocalDivisor c` is the subtype `cM ∩ Mc` of `M`. -/
def equivSubtype :
    LocalDivisor c ≃ {u : M // (∃ m, u = c * m) ∧ ∃ m, u = m * c} where
  toFun u := ⟨u.val, u.mem_left, u.mem_right⟩
  invFun s := ⟨s.1, s.2.1, s.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- `LocalDivisor c` is finite, via `equivSubtype` and `Subtype.finite`
(no decidability needed — the point of the amended §4.1 bundling). -/
instance : Finite (LocalDivisor c) := Finite.of_equiv _ equivSubtype.symm

/-!
Bootstrap section. `Monoid`'s law fields (`mul_assoc`, `one_mul`,
`mul_one`) need `*`/`1` notation for `LocalDivisor c` and a
`mul_spec`-shaped fact to rewrite with — but a `where`-block instance
cannot resolve notation for the very type it is building (elaborating
`u * v`/`(1 : LocalDivisor c)` there needs `Mul`/`One (LocalDivisor c)`
already registered by instance search, and the instance under
construction isn't registered until it is complete; probe-verified:
`show`/fresh `*`/`1` syntax there fails with `failed to synthesize
HMul`/`OfNat`). So `Mul` and `One` are bootstrapped here as
`local instance`s, visible to search only inside this section; the
`Monoid` instance below reuses their fields verbatim
(`mul := (· * ·)`, `one := (1 : LocalDivisor c)`). Once the section
closes, these local instances drop out of search entirely, leaving the
`Monoid`-derived `Mul`/`One` as the only resolution path for
`mul_spec` onward and for downstream files — matching what a single
bundled instance would have provided, had self-reference through
notation been possible. The `mul` field's body is untouched from the
design: `Classical.choose` appears in this definition and only here —
the two `mul_spec` proofs unfold it, and nothing else in the file or
downstream mentions it.
-/

section

/-- Bootstrap-only: the twisted product, scoped to this section so
`mul_assoc`/`one_mul`/`mul_one` can use `*` notation and `mul_spec_aux`
below. Drops out of instance search once the section ends, leaving the
`Monoid` instance's derived `Mul` as the only resolution path. -/
private noncomputable local instance instMulAux : Mul (LocalDivisor c) where
  mul u v :=
    { val := Classical.choose u.mem_right * v.val
      mem_left := by
        obtain ⟨n, hn⟩ := v.mem_left
        obtain ⟨m₁, hm₁⟩ := u.mem_left
        refine ⟨m₁ * n, ?_⟩
        rw [hn, ← mul_assoc, ← Classical.choose_spec u.mem_right, hm₁,
          mul_assoc]
      mem_right := by
        obtain ⟨n₂, hn₂⟩ := v.mem_right
        exact ⟨Classical.choose u.mem_right * n₂, by rw [hn₂, mul_assoc]⟩ }

/-- Bootstrap-only: the identity `c`, scoped like `instMulAux` above. -/
private local instance instOneAux : One (LocalDivisor c) where
  one := ⟨c, ⟨1, (mul_one c).symm⟩, ⟨1, (one_mul c).symm⟩⟩

omit [Finite M] in
/-- Bootstrap-only: `(1 : LocalDivisor c).val = c`, feeding
`mul_spec_aux` below (the public `val_one` restates it after the
section). -/
private theorem val_one_aux : (1 : LocalDivisor c).val = c := rfl

omit [Finite M] in
/-- Bootstrap-only mirror of `mul_spec` (see below), proven against the
scoped `Mul`/`One` instances so the `Monoid` instance's laws can cite
it; the public `mul_spec` after the section restates the identical
fact against the (only, by then) visible `Monoid`-derived instance. -/
private theorem mul_spec_aux (u v : LocalDivisor c) {m : M} (hm : u.val = m * c) :
    (u * v).val = m * v.val := by
  show Classical.choose u.mem_right * v.val = m * v.val
  obtain ⟨n, hn⟩ := v.mem_left
  rw [hn, ← mul_assoc, ← mul_assoc, ← Classical.choose_spec u.mem_right, ← hm]

/-- The twisted product `(mc) ∘ (cn) := mcn` and identity `c`
[DKS §2.5]. The product reads an `Mc`-decomposition of the left factor
via `Classical.choose`; use `mul_spec`, never the definition. -/
noncomputable instance : Monoid (LocalDivisor c) where
  mul := (· * ·)
  one := (1 : LocalDivisor c)
  mul_assoc u v w := by
    ext
    obtain ⟨m₂, hm₂⟩ := u.mem_right
    obtain ⟨q₂, hq₂⟩ := v.mem_right
    have hL' : (u * v).val = m₂ * q₂ * c := by
      rw [mul_spec_aux u v hm₂, hq₂, mul_assoc]
    rw [mul_spec_aux (u * v) w hL', mul_spec_aux u (v * w) hm₂,
      mul_spec_aux v w hq₂, mul_assoc]
  one_mul u := by
    ext
    rw [mul_spec_aux 1 u (m := 1) (val_one_aux.trans (one_mul c).symm), one_mul]
  mul_one u := by
    ext
    obtain ⟨m₂, hm₂⟩ := u.mem_right
    rw [mul_spec_aux u 1 hm₂, val_one_aux, ← hm₂]

end

omit [Finite M] in
/-- The identity of the local divisor is `c` itself. -/
@[simp] theorem val_one : (1 : LocalDivisor c).val = c := rfl

omit [Finite M] in
/-- Choose-independence [DKS §2.5, blueprint `def:localdiv`]: ANY
`Mc`-witness for the left factor computes the product. This is the
lemma that quarantines `Classical.choose`. -/
theorem mul_spec (u v : LocalDivisor c) {m : M} (hm : u.val = m * c) :
    (u * v).val = m * v.val := by
  show Classical.choose u.mem_right * v.val = m * v.val
  obtain ⟨n, hn⟩ := v.mem_left
  rw [hn, ← mul_assoc, ← mul_assoc, ← Classical.choose_spec u.mem_right, ← hm]

omit [Finite M] in
/-- The dual computation: any `cM`-witness for the RIGHT factor gives
`(u * v).val = u.val * n`. -/
theorem mul_spec_right (u v : LocalDivisor c) {n : M} (hn : v.val = c * n) :
    (u * v).val = u.val * n := by
  obtain ⟨m₂, hm₂⟩ := u.mem_right
  rw [mul_spec u v hm₂, hn, ← mul_assoc, ← hm₂]

end LocalDivisor

-- Sanity (spec §6): in `ZMod 4` at `c = 2` the carrier is `{0, 2}`,
-- `2` is the identity, `0` absorbs. Products are evaluated through
-- `mul_spec` (the definition's `choose` does not compute).
private def ld0 : LocalDivisor (2 : ZMod 4) :=
  ⟨0, ⟨0, by decide⟩, ⟨0, by decide⟩⟩
private def ld2 : LocalDivisor (2 : ZMod 4) :=
  ⟨2, ⟨1, by decide⟩, ⟨1, by decide⟩⟩
example : (ld0 * ld2).val = 0 :=
  (LocalDivisor.mul_spec ld0 ld2 (m := 0) (by decide)).trans (by decide)
example : (ld2 * ld0).val = 0 :=
  (LocalDivisor.mul_spec ld2 ld0 (m := 1) (by decide)).trans (by decide)
-- Chirality guard: `mul_spec` multiplies the witness on the LEFT of
-- `v.val`. In `Function.End (Fin 2)` (a noncommutative non-group
-- monoid) a transposed definition `v.val * m` would differ; the
-- concrete instance is built in Task 8's guard once `act` exists, at
-- the transformation-monoid level where chirality is observable.

/-- Bootstrap-only: the existence half of `localDivisor_act_spec` — the
action's target lands back in the image `X·c`, for ANY valid
`cM`-witness `m` of `u.val` (not just the one `Classical.choose` happens
to pick). Feeds the `act` field's own membership proof and the third
leg of `act_mul` below, both of which need this before `localDivisor`
exists to state the public lemma against. -/
private theorem localDivisor_mem_aux (T : TransMon) (c : T.M) {x : T.X}
    (hx : ∃ y, x = T.act y c) (u : LocalDivisor c) {m : T.M} (hm : u.val = c * m) :
    ∃ y, T.act x m = T.act y c := by
  obtain ⟨y, hy⟩ := hx
  obtain ⟨m₂, hm₂⟩ := u.mem_right
  exact ⟨T.act y m₂, by rw [hy, ← T.act_mul, ← hm, hm₂, T.act_mul]⟩

/-- Bootstrap-only mirror of `localDivisor_act_spec`, proven directly
about the raw action formula against a plain `x : T.X` (before it is
packaged into the `localDivisor` `TransMon`), so the `act_one`/`act_mul`
fields below can cite it while `localDivisor` is still being built. The
public `localDivisor_act_spec` after `localDivisor` restates the
identical fact against the completed structure — the same relationship
`mul_spec_aux` has to `mul_spec` above. -/
private theorem localDivisor_act_spec_aux (T : TransMon) (c : T.M) {x : T.X}
    (hx : ∃ y, x = T.act y c) (u : LocalDivisor c) {m : T.M}
    (hm : u.val = c * m) :
    T.act x (Classical.choose u.mem_left) = T.act x m := by
  obtain ⟨y, hy⟩ := hx
  rw [hy, ← T.act_mul, ← T.act_mul, ← Classical.choose_spec u.mem_left, hm]

/-- The local divisor as a transformation monoid [DKS §2.5, blueprint
`def:localdiv-tm`]: `LocalDivisor c` acting on the image `X·c` by
`ξ ∘ (cm) := ξ · m`. The action reads a `cM`-decomposition via
`Classical.choose`; use `localDivisor_act_spec`, never the
definition. -/
noncomputable def localDivisor (T : TransMon) (c : T.M) : TransMon where
  X := {x : T.X // ∃ y, x = T.act y c}
  M := LocalDivisor c
  act ξ u :=
    ⟨T.act ξ.val (Classical.choose u.mem_left),
      localDivisor_mem_aux T c ξ.2 u (Classical.choose_spec u.mem_left)⟩
  act_one ξ := by
    apply Subtype.ext
    show T.act ξ.val (Classical.choose (1 : LocalDivisor c).mem_left) = ξ.val
    rw [localDivisor_act_spec_aux T c ξ.2 1 (LocalDivisor.val_one.trans (mul_one c).symm),
      T.act_one]
  act_mul ξ u v := by
    apply Subtype.ext
    obtain ⟨mᵤ, hmᵤ⟩ := u.mem_left
    obtain ⟨mᵥ, hmᵥ⟩ := v.mem_left
    have huv : (u * v).val = c * (mᵤ * mᵥ) := by
      rw [LocalDivisor.mul_spec_right u v hmᵥ, hmᵤ, mul_assoc]
    show T.act ξ.val (Classical.choose (u * v).mem_left)
        = T.act (T.act ξ.val (Classical.choose u.mem_left)) (Classical.choose v.mem_left)
    rw [localDivisor_act_spec_aux T c ξ.2 (u * v) huv, T.act_mul,
      localDivisor_act_spec_aux T c ξ.2 u hmᵤ,
      localDivisor_act_spec_aux T c (localDivisor_mem_aux T c ξ.2 u hmᵤ) v hmᵥ]

/-- Choose-independence for the action: ANY `cM`-witness computes it. -/
theorem localDivisor_act_spec (T : TransMon) (c : T.M) (ξ : (localDivisor T c).X)
    (u : (localDivisor T c).M) {m : T.M} (hm : u.val = c * m) :
    ((localDivisor T c).act ξ u).val = T.act ξ.val m := by
  show T.act ξ.val (Classical.choose u.mem_left) = T.act ξ.val m
  exact localDivisor_act_spec_aux T c ξ.2 u hm

/-- [DKS] 2.13 (blueprint `lem:localdiv-faithful`): local divisors of
faithful transformation monoids are faithful — the induction may
recurse into them. -/
theorem localDivisor_faithful {T : TransMon} (hT : T.Faithful)
    (c : T.M) : (localDivisor T c).Faithful := by
  intro u v h
  apply LocalDivisor.ext
  refine hT fun x => ?_
  obtain ⟨mu, hmu⟩ := u.mem_left
  obtain ⟨mv, hmv⟩ := v.mem_left
  calc T.act x u.val
      = T.act (T.act x c) mu := by rw [hmu, T.act_mul]
    _ = ((localDivisor T c).act ⟨T.act x c, x, rfl⟩ u).val :=
        (localDivisor_act_spec T c ⟨T.act x c, x, rfl⟩ u hmu).symm
    _ = ((localDivisor T c).act ⟨T.act x c, x, rfl⟩ v).val := by
        rw [h ⟨T.act x c, x, rfl⟩]
    _ = T.act (T.act x c) mv := localDivisor_act_spec T c ⟨T.act x c, x, rfl⟩ v hmv
    _ = T.act x v.val := by rw [hmv, ← T.act_mul]

-- Sanity (spec §6). Over `regular (ZMod 4)` at `c = 2`: the state
-- space is the image `{0, 2}`, and acting by the reset-like element
-- `0` of the local divisor sends every state to `0 · m`-form values.
-- Concretely: state `ξ := 0` (in the image via `0 = 0 * 2`) acted on by
-- `ld0` (`ld0.val = 0`, a `cM`-witness `m = 0` since `0 = 2 * 0`) lands
-- back on `0`.
private def xi0 :
    (localDivisor (regular (ZMod 4)) (2 : ZMod 4)).X :=
  ⟨(0 : ZMod 4), (0 : ZMod 4), show (0 : ZMod 4) = 0 * 2 by decide⟩

example :
    ((localDivisor (regular (ZMod 4)) (2 : ZMod 4)).act xi0 ld0).val = (0 : ZMod 4) := by
  rw [localDivisor_act_spec (regular (ZMod 4)) (2 : ZMod 4) xi0 ld0
    (m := (0 : ZMod 4)) (show ld0.val = 2 * 0 by decide)]
  show (0 : ZMod 4) * 0 = 0
  decide

-- Chirality guard: `act ξ u = ξ · m` for `u = c * m` — the witness
-- multiplies on the RIGHT of the state. With the noncommutative
-- `regular (Function.End (Fin 2))`, a transposed definition
-- (`ξ ∘ u := ξ · m'` read from `u = m' * c`) picks the OTHER
-- factorization and produces a different state; the example below
-- pins the correct one via `localDivisor_act_spec` + `decide`.
private def id2 : Function.End (Fin 2) := fun x => x
private def swap2 : Function.End (Fin 2) := fun x => 1 - x
private def const0 : Function.End (Fin 2) := fun _ => 0
private def const1 : Function.End (Fin 2) := fun _ => 1

-- `Function.End (Fin 2) := Fin 2 → Fin 2` is a plain `def`, so instance
-- search does not see through it to the Pi-type's `Finite`/`DecidableEq`
-- instances on its own; bridge them once, for this guard's use only
-- (same rationale as `BarMonoid`'s conditional `DecidableEq` in
-- `Bar.lean`).
private instance : Finite (Function.End (Fin 2)) :=
  inferInstanceAs (Finite (Fin 2 → Fin 2))
private instance : DecidableEq (Function.End (Fin 2)) :=
  inferInstanceAs (DecidableEq (Fin 2 → Fin 2))

-- `c := swap2`, the unique non-identity UNIT of `Function.End (Fin 2)`.
-- (Every non-unit of this 4-element monoid is a left-zero constant map,
-- for which `cM` collapses to `{c}` and the action degenerates to the
-- identity no matter which witness is read — no non-unit `c` in this
-- particular monoid can guard chirality, so the unit `swap2` is the
-- only workable choice here; non-unit `c` is exercised by the `ZMod 4`
-- sanity example above and by `localDivisor_card_lt`/`localDivisor_divides`
-- in Task 9.)
private def guardU : LocalDivisor (swap2 : Function.End (Fin 2)) :=
  ⟨const0, ⟨const1, by decide⟩, ⟨const0, by decide⟩⟩

private def guardXi :
    (localDivisor (regular (Function.End (Fin 2))) swap2).X :=
  ⟨swap2, id2, show swap2 = id2 * swap2 by decide⟩

-- The correct reading (the `mem_left`/cM-witness `const1`) pins the
-- result to `const0`.
example :
    ((localDivisor (regular (Function.End (Fin 2))) swap2).act guardXi guardU).val
      = const0 := by
  rw [localDivisor_act_spec (regular (Function.End (Fin 2))) swap2 guardXi guardU
    (m := const1) (show const0 = swap2 * const1 by decide)]
  show swap2 * const1 = const0
  decide

-- A transposed definition reading the `mem_right`/Mc-witness `const0`
-- instead would compute `swap2 * const0 = const1 ≠ const0`: this example
-- kills that transposition.
example : (swap2 * const0 : Function.End (Fin 2)) = const1 := by decide
example : (const0 : Function.End (Fin 2)) ≠ const1 := by decide

/-- Cardinality drop (blueprint `lem:localdiv-card`): a non-unit's
local divisor is strictly smaller — the recursion's measure. `1` is
not in the carrier: `1 = c * m` would make `c` a unit by finiteness
(`mul_eq_one_comm`). -/
theorem localDivisor_card_lt {c : M} (hc : ¬ IsUnit c) :
    Nat.card (LocalDivisor c) < Nat.card M := by
  rw [Nat.card_congr (LocalDivisor.equivSubtype (c := c))]
  refine Finite.card_subtype_lt (x := (1 : M)) ?_
  rintro ⟨⟨m, hm⟩, -⟩
  -- hm : (1 : M) = c * m — c is right-invertible, hence (finite) a unit
  exact hc ⟨⟨c, m, hm.symm, mul_eq_one_comm.mp hm.symm⟩, rfl⟩

omit [Finite M] in
/-- Division (blueprint `lem:localdiv-divides`): `Mc ≺ₘ M` via the
submonoid `N = {m | c * m ∈ Mc}` and `ψ : m ↦ c * m`. THE lemma that
keeps the strong form alive through recursion (spec §3.6): simple
groups arising inside `Mc` divide `Mc`, hence divide `M`. -/
theorem localDivisor_divides (c : M) : LocalDivisor c ≺ₘ M := by
  refine ⟨{ carrier := {m | ∃ m₂, c * m = m₂ * c}
            one_mem' := ⟨1, by rw [mul_one, one_mul]⟩
            mul_mem' := ?_ },
    { toFun := fun m => ⟨c * m.1, ⟨m.1, rfl⟩, m.2⟩
      map_one' := ?_
      map_mul' := ?_ }, ?_⟩
  · -- mul_mem': c(mn) = m₂(cn) = m₂n₂c
    rintro m n ⟨m₂, hm₂⟩ ⟨n₂, hn₂⟩
    exact ⟨m₂ * n₂, by rw [← mul_assoc, hm₂, mul_assoc, hn₂, ← mul_assoc]⟩
  · -- ψ 1 = ⟨c * 1⟩ = ⟨c⟩ = 1
    ext
    simp
  · -- ψ(m n) = ψ m * ψ n via mul_spec_right with witness ψ n = c * n
    rintro ⟨m, hm⟩ ⟨n, hn⟩
    ext
    rw [LocalDivisor.mul_spec_right _ _ (n := n) rfl]
    show c * (m * n) = c * m * n
    rw [mul_assoc]
  · -- surjective: u = c * m = m₂ * c puts m in N with ψ m = u
    rintro ⟨u, ⟨m, hm⟩, ⟨m₂, hm₂⟩⟩
    exact ⟨⟨m, m₂, by rw [← hm, hm₂]⟩, by ext; exact hm.symm⟩

-- Sanity (spec §6): `2` is not a unit in `ZMod 4`, so its local
-- divisor (carrier `{0, 2}`) is strictly smaller and divides.
example : ¬ IsUnit (2 : ZMod 4) := by decide
example : Nat.card (LocalDivisor (2 : ZMod 4)) < Nat.card (ZMod 4) :=
  localDivisor_card_lt (by decide)
example : LocalDivisor (2 : ZMod 4) ≺ₘ ZMod 4 := localDivisor_divides _
-- Milestone acceptance shape (spec §7 row 5): the measure and the
-- division hold together for any non-unit.
example (c : ZMod 4) (h : ¬ IsUnit c) :
    LocalDivisor c ≺ₘ ZMod 4 ∧ Nat.card (LocalDivisor c) < Nat.card (ZMod 4) :=
  ⟨localDivisor_divides c, localDivisor_card_lt h⟩

end TransMon
end KRTheory
