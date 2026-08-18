import KRTheory.FiniteMonoid
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
The product reads a decomposition witness via `Classical.choose`; the
`mul_spec`/`mul_spec_right` lemmas quarantine that choice — nothing
downstream ever mentions it (spec §8 mitigation).
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
below. Shadowed in visibility by the `Monoid` instance's derived `Mul`
once the section ends. -/
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

end TransMon
end KRTheory
