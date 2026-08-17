import KRTheory.TransMon.Wreath
import KRTheory.TransMon.Division

/-!
# Division calculus of wreath products

Absorption of the trivial factor, monotonicity of `≺` under `≀`,
one-directional associativity, and the `wreathList` append lemma
[DKS §2.2–§2.3]. These are the gluing lemmas of the Krohn–Rhodes
induction (spec §3.3, §3.9).
-/

namespace KRTheory
namespace TransMon

/-- Absorb a trivial front factor: `trivialTM ≀ T ≺ T`. -/
theorem trivial_wreath_div (T : TransMon) : trivialTM ≀ T ≺ T :=
  ⟨{ toSubmonoid := ⊤
     stateMap := fun y => (PUnit.unit, y)
     monoidMap :=
       { toFun := fun n => ⟨fun _ => PUnit.unit, (n : T.M)⟩
         map_one' := WreathMonoid.ext (funext fun _ => rfl) rfl
         map_mul' := fun n m =>
           WreathMonoid.ext (funext fun _ => rfl) rfl }
     stateMap_surj := fun p => ⟨p.2, by obtain ⟨u, y⟩ := p; rfl⟩
     monoidMap_surj := fun w =>
       ⟨⟨w.right, trivial⟩,
         WreathMonoid.ext (funext fun _ => rfl) rfl⟩
     equivariant := fun y n => rfl }⟩

/-- Any `S` divides its padding by a trivial back factor:
`S ≺ S ≀ trivialTM`. Base case of iterated-wreath gluing. -/
theorem div_wreath_trivial (S : TransMon) : S ≺ S ≀ trivialTM :=
  ⟨{ toSubmonoid := ⊤
     stateMap := Prod.fst
     monoidMap :=
       { toFun := fun w => w.1.left PUnit.unit
         map_one' := rfl
         map_mul' := fun _w _w' =>
           -- ((w*w').left) unit = w.left unit * w'.left (unit ⊳ w.right)
           -- and unit ⊳ anything = unit in trivialTM, all definitionally
           rfl }
     stateMap_surj := fun x => ⟨(x, PUnit.unit), rfl⟩
     monoidMap_surj := fun m => ⟨⟨⟨fun _ => m, PUnit.unit⟩, trivial⟩, rfl⟩
     equivariant := fun _p _w =>
       -- fst (p ⊳ w) = S.act p.1 (w.left p.2); p.2 = unit, all definitionally
       rfl }⟩

/-- `S` divides the singleton iterated wreath. -/
theorem div_wreathList_singleton (S : TransMon) : S ≺ wreathList [S] := by
  simpa using div_wreath_trivial S

/-!
### Monotonicity of `≺` under `≀`

Two `private` helpers feed `Covering.wreath` below (a third, `extMap_one`,
is now the public `Covering.extMap_one` in `Division.lean`); the public
API of this section is only `Covering.wreath` and `StrongDivides.wreath`.
-/

/-- (private) A chosen set-theoretic section of the state surjection
`c.stateMap`. Used by `Covering.wreath` to push front-machine data of
`T₁ ≀ T₂` down to `S₁ ≀ S₂`: a front value must be read off at *some*
`T₂`-state above the given `S₂`-state, and fiber-compatibility makes the
choice irrelevant. -/
private noncomputable def Covering.sect {S T : TransMon} (c : Covering S T) :
    S.X → T.X := Function.surjInv c.stateMap_surj

/-- (private) The defining equation of `Covering.sect`: it really is a
section of `c.stateMap`. -/
private theorem Covering.stateMap_sect {S T : TransMon} (c : Covering S T)
    (s : S.X) : c.stateMap (c.sect s) = s :=
  Function.surjInv_eq c.stateMap_surj s

/-- The wreath product of two coverings: witnesses monotonicity of `≺`
under `≀` (blueprint lem:wreath-mono). The submonoid consists of the
*fiber-compatible* elements: the back component covers via `c₂`, every
front value lies in `c₁`'s submonoid, and the front function descends
along `c₂.stateMap`-fibers up to `c₁.extMap`. The monoid map reads the
front component off at a chosen section of `c₂.stateMap`, and fiber
compatibility is exactly what makes that a homomorphism. -/
noncomputable def Covering.wreath {S₁ T₁ S₂ T₂ : TransMon}
    (c₁ : Covering S₁ T₁) (c₂ : Covering S₂ T₂) :
    Covering (S₁ ≀ S₂) (T₁ ≀ T₂) where
  toSubmonoid :=
    { carrier := { w | w.right ∈ c₂.toSubmonoid ∧
        (∀ y, w.left y ∈ c₁.toSubmonoid) ∧
        ∀ y y', c₂.stateMap y = c₂.stateMap y' →
          c₁.extMap (w.left y) = c₁.extMap (w.left y') }
      one_mem' := ⟨one_mem _, fun _ => one_mem _, fun _ _ _ => rfl⟩
      mul_mem' := by
        rintro w w' ⟨hr, hl, hc⟩ ⟨hr', hl', hc'⟩
        refine ⟨mul_mem hr hr', fun y => mul_mem (hl y) (hl' _), fun y y' hyy' => ?_⟩
        -- the twisted second factors are read at `T₂`-states that `c₂`
        -- identifies — this is where `c₂.equivariant` is spent
        have hstep : c₂.stateMap (T₂.act y w.right) =
            c₂.stateMap (T₂.act y' w.right) := by
          rw [← c₂.act_extMap hr, ← c₂.act_extMap hr, hyy']
        show c₁.extMap (w.left y * w'.left (T₂.act y w.right)) =
          c₁.extMap (w.left y' * w'.left (T₂.act y' w.right))
        rw [c₁.extMap_mul_of_mem (hl y) (hl' _),
          c₁.extMap_mul_of_mem (hl y') (hl' _), hc y y' hyy', hc' _ _ hstep] }
  stateMap := Prod.map c₁.stateMap c₂.stateMap
  monoidMap :=
    { toFun := fun w =>
        ⟨fun s => c₁.extMap ((w : (T₁ ≀ T₂).M).left (c₂.sect s)),
          c₂.extMap (w : (T₁ ≀ T₂).M).right⟩
      map_one' := by
        refine WreathMonoid.ext (funext fun _ => ?_) ?_
        · show c₁.extMap (1 : T₁.M) = 1
          exact c₁.extMap_one
        · show c₂.extMap (1 : T₂.M) = 1
          exact c₂.extMap_one
      map_mul' := by
        rintro ⟨w, hr, hl, _hc⟩ ⟨w', hr', hl', hc'⟩
        refine WreathMonoid.ext (funext fun s => ?_) ?_
        · -- the two front factors are read at different `T₂`-states, but
          -- `c₂` identifies them, so fiber-compatibility of `w'` applies
          have hfib : c₂.stateMap (T₂.act (c₂.sect s) w.right) =
              c₂.stateMap (c₂.sect (S₂.act s (c₂.extMap w.right))) := by
            rw [← c₂.act_extMap hr, c₂.stateMap_sect, c₂.stateMap_sect]
          show c₁.extMap (w.left (c₂.sect s) * w'.left (T₂.act (c₂.sect s) w.right)) =
            c₁.extMap (w.left (c₂.sect s)) *
              c₁.extMap (w'.left (c₂.sect (S₂.act s (c₂.extMap w.right))))
          rw [c₁.extMap_mul_of_mem (hl _) (hl' _), hc' _ _ hfib]
        · show c₂.extMap (w.right * w'.right) =
            c₂.extMap w.right * c₂.extMap w'.right
          exact c₂.extMap_mul_of_mem hr hr' }
  stateMap_surj := c₁.stateMap_surj.prodMap c₂.stateMap_surj
  monoidMap_surj := by
    intro v
    -- choose `ψ`-preimages pointwise; reading the front component through
    -- `c₂.stateMap` makes the choice constant on fibers by construction
    refine ⟨⟨⟨fun y => ↑(Function.surjInv c₁.monoidMap_surj (v.left (c₂.stateMap y))),
        ↑(Function.surjInv c₂.monoidMap_surj v.right)⟩,
      (Function.surjInv c₂.monoidMap_surj v.right).2,
      fun y => (Function.surjInv c₁.monoidMap_surj (v.left (c₂.stateMap y))).2,
      fun _ _ h => congrArg
        (fun a => c₁.extMap ↑(Function.surjInv c₁.monoidMap_surj (v.left a))) h⟩, ?_⟩
    refine WreathMonoid.ext (funext fun s => ?_) ?_
    · show c₁.extMap ↑(Function.surjInv c₁.monoidMap_surj
        (v.left (c₂.stateMap (c₂.sect s)))) = v.left s
      rw [Covering.extMap_coe, Function.surjInv_eq c₁.monoidMap_surj,
        c₂.stateMap_sect]
    · show c₂.extMap ↑(Function.surjInv c₂.monoidMap_surj v.right) = v.right
      rw [Covering.extMap_coe, Function.surjInv_eq c₂.monoidMap_surj]
  equivariant := by
    rintro ⟨x, y⟩ ⟨w, hr, hl, hc⟩
    refine Prod.ext ?_ ?_
    · show S₁.act (c₁.stateMap x) (c₁.extMap (w.left (c₂.sect (c₂.stateMap y)))) =
        c₁.stateMap (T₁.act x (w.left y))
      rw [hc _ y (c₂.stateMap_sect (c₂.stateMap y))]
      exact c₁.act_extMap (hl y) x
    · show S₂.act (c₂.stateMap y) (c₂.extMap w.right) =
        c₂.stateMap (T₂.act y w.right)
      exact c₂.act_extMap hr y

/-- Monotonicity: strong division is preserved by wreath products —
`S₁ ≺ T₁` and `S₂ ≺ T₂` give `S₁ ≀ S₂ ≺ T₁ ≀ T₂`. Witnessed by
`Covering.wreath`. [DKS §2.3, blueprint `lem:wreath-mono`] -/
theorem StrongDivides.wreath {S₁ T₁ S₂ T₂ : TransMon}
    (h₁ : S₁ ≺ T₁) (h₂ : S₂ ≺ T₂) : S₁ ≀ S₂ ≺ T₁ ≀ T₂ := by
  obtain ⟨c₁⟩ := h₁; obtain ⟨c₂⟩ := h₂
  exact ⟨c₁.wreath c₂⟩

/-!
### Associativity of `≀` up to division
-/

/-- One-directional associativity: `(P ≀ Q) ≀ R ≺ P ≀ (Q ≀ R)`.
The underlying map is currying; the twisted multiplications correspond
exactly, so the covering is total (`⊤`) with a bijective monoid map. -/
theorem wreath_assoc_div (P Q R : TransMon) :
    (P ≀ Q) ≀ R ≺ P ≀ (Q ≀ R) :=
  ⟨{ toSubmonoid := ⊤
     stateMap := fun p => ((p.1, p.2.1), p.2.2)
     monoidMap :=
       { toFun := fun w =>
           ⟨fun z => ⟨fun y => (w : (P ≀ (Q ≀ R)).M).left (y, z),
              (w : (P ≀ (Q ≀ R)).M).right.left z⟩,
            (w : (P ≀ (Q ≀ R)).M).right.right⟩
         map_one' := rfl
         map_mul' := fun _ _ => rfl }
     stateMap_surj := fun p => ⟨(p.1.1, (p.1.2, p.2)), rfl⟩
     monoidMap_surj := fun v =>
       ⟨⟨⟨fun yz => (v.left yz.2).left yz.1, ⟨fun z => (v.left z).right, v.right⟩⟩, trivial⟩,
         rfl⟩
     equivariant := fun _ _ => rfl }⟩

-- Sanity checks (spec §6).
example {S₁ T₁ S₂ T₂ : TransMon} (h₁ : S₁ ≺ T₁) (h₂ : S₂ ≺ T₂) :
    S₁ ≀ S₂ ≺ T₁ ≀ T₂ := h₁.wreath h₂
example (T : TransMon) : T ≀ T ≺ T ≀ T :=
  (StrongDivides.refl T).wreath (.refl T)
example : trivialTM ≀ trivialTM ≺ trivialTM := trivial_wreath_div _
example : regular (ZMod 2) ≺ wreathList [regular (ZMod 2)] :=
  div_wreathList_singleton _
example (P Q R : TransMon) : (P ≀ Q) ≀ R ≺ P ≀ (Q ≀ R) := wreath_assoc_div P Q R

end TransMon
end KRTheory
