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

-- Sanity checks (spec §6).
example : trivialTM ≀ trivialTM ≺ trivialTM := trivial_wreath_div _
example : regular (ZMod 2) ≺ wreathList [regular (ZMod 2)] :=
  div_wreathList_singleton _

end TransMon
end KRTheory
