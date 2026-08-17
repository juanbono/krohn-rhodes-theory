import KRTheory.TransMon.Basic

/-!
# Wreath products of transformation monoids

The wreath product `S ≀ T` [DKS §2.2]: states `S.X × T.X`, monoid
`WreathMonoid S T` (functions `T.X → S.M` twisted by `T.M`). The monoid
is a fresh structure rather than the raw product type `(T.X → S.M) × T.M`
because the multiplication is twisted — defining it on the product type
would collide with Mathlib's componentwise `Prod.instMonoid` (instance
diamond). Same design as Mathlib's `RegularWreathProduct`.
-/

namespace KRTheory
namespace TransMon

/-- The monoid part of the wreath product `S ≀ T`: carrier
`(T.X → S.M) × T.M` as a fresh structure (see module docstring), with
multiplication `(f,n)(g,k) = (fun y => f y * g (y·n), n*k)`. [DKS §2.2] -/
@[ext]
structure WreathMonoid (S T : TransMon) : Type where
  /-- The front-machine component: an `S.M`-element for each `T`-state. -/
  left : T.X → S.M
  /-- The back-machine component. -/
  right : T.M

namespace WreathMonoid

variable {S T : TransMon}

/-- The twisted wreath product monoid structure: multiplying `w * w'`
twists `w'`'s `left` component by first letting `w.right` act on the
state before evaluating, while `right` just multiplies in `T.M`; the
identity is `⟨fun _ => 1, 1⟩`. -/
instance : Monoid (WreathMonoid S T) where
  mul w w' := ⟨fun y => w.left y * w'.left (T.act y w.right), w.right * w'.right⟩
  one := ⟨fun _ => 1, 1⟩
  mul_assoc w₁ w₂ w₃ := by
    ext y
    · show (w₁.left y * w₂.left (T.act y w₁.right)) * w₃.left (T.act y (w₁.right * w₂.right)) =
          w₁.left y * (w₂.left (T.act y w₁.right) * w₃.left (T.act (T.act y w₁.right) w₂.right))
      simp [mul_assoc, TransMon.act_mul]
    · show (w₁.right * w₂.right) * w₃.right = w₁.right * (w₂.right * w₃.right)
      simp [mul_assoc]
  one_mul w := by
    ext y
    · show (1 : S.M) * w.left (T.act y (1 : T.M)) = w.left y
      simp
    · show (1 : T.M) * w.right = w.right
      simp
  mul_one w := by
    ext y
    · show w.left y * (1 : S.M) = w.left y
      simp
    · show w.right * (1 : T.M) = w.right
      simp

/-- The `left` component of a product: `w`'s value at `y`, times `w'`'s
value at `y` after `w.right` acts on it. -/
@[simp] theorem mul_left (w w' : WreathMonoid S T) (y : T.X) :
    (w * w').left y = w.left y * w'.left (T.act y w.right) := rfl

/-- The `right` component of a product is just the product in `T.M`. -/
@[simp] theorem mul_right (w w' : WreathMonoid S T) :
    (w * w').right = w.right * w'.right := rfl

/-- The `left` component of the identity is constantly `1`. -/
@[simp] theorem one_left (y : T.X) : (1 : WreathMonoid S T).left y = 1 := rfl

/-- The `right` component of the identity is `1 : T.M`. -/
@[simp] theorem one_right : (1 : WreathMonoid S T).right = (1 : T.M) := rfl

/-- `WreathMonoid` is, as a type, the product `(T.X → S.M) × T.M`. -/
def equivProd : WreathMonoid S T ≃ (T.X → S.M) × T.M where
  toFun w := (w.left, w.right)
  invFun p := ⟨p.1, p.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- `WreathMonoid S T` is finite, via the equivalence `equivProd` with the
finite product `(T.X → S.M) × T.M`. -/
instance : Finite (WreathMonoid S T) := Finite.of_equiv _ equivProd.symm

/-- `|S ≀ T| = |S.M| ^ |T.X| * |T.M|` at the monoid level. -/
theorem natCard :
    Nat.card (WreathMonoid S T) =
      Nat.card S.M ^ Nat.card T.X * Nat.card T.M := by
  rw [Nat.card_congr (equivProd (S := S) (T := T)), Nat.card_prod, Nat.card_fun]

end WreathMonoid

-- Sanity checks (spec §6).
-- Twist guard: with w = ⟨const 1, 2⟩ and w' = ⟨id, 1⟩ over the regular
-- representation of ZMod 3, (w * w').left 1 = 1 * id (1 * 2) = 2.
-- The UNtwisted componentwise product would give 1 * id 1 = 1, and the
-- wrong-sided twist (evaluating w.left at y · w'.right) would give
-- 1 * id 1 = 1 as well: this example kills both wrong definitions.
example :
    ((⟨fun _ => (1 : ZMod 3), (2 : ZMod 3)⟩ :
        WreathMonoid (regular (ZMod 3)) (regular (ZMod 3))) *
      ⟨fun y => y, (1 : ZMod 3)⟩).left (1 : ZMod 3) = (2 : ZMod 3) := rfl
example :
    ((⟨fun _ => (1 : ZMod 3), (2 : ZMod 3)⟩ :
        WreathMonoid (regular (ZMod 3)) (regular (ZMod 3))) *
      ⟨fun y => y, (1 : ZMod 3)⟩).right = (2 : ZMod 3) := rfl
example :
    Nat.card (WreathMonoid (regular (ZMod 2)) (regular (ZMod 2))) = 8 := by
  simp only [WreathMonoid.natCard, Nat.card_eq_fintype_card]
  rfl

end TransMon
end KRTheory
