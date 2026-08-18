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

/-- The wreath product of transformation monoids [DKS §2.2]: the cascade
of `S` driven by `T`. `noncomputable` only because `Fintype` of the
function component needs `DecidableEq T.X`, which `TransMon` deliberately
does not carry (spec §4.1); the algebra itself is computable and `rfl`
still evaluates actions and products. -/
noncomputable def wreath (S T : TransMon) : TransMon where
  X := S.X × T.X
  M := WreathMonoid S T
  fintypeM := Fintype.ofFinite _
  act p w := (S.act p.1 (w.left p.2), T.act p.2 w.right)
  act_one p := by simp
  act_mul p w w' := by simp [TransMon.act_mul]

@[inherit_doc]
scoped infixr:60 " ≀ " => TransMon.wreath

/-- The action of `S ≀ T` unfolds componentwise: `S` acts on its state via
`w.left` evaluated at the *current* `T`-state `p.2`, while `T` acts on its
own state via `w.right`. -/
@[simp] theorem wreath_act {S T : TransMon} (p : (S ≀ T).X) (w : (S ≀ T).M) :
    (S ≀ T).act p w = (S.act p.1 (w.left p.2), T.act p.2 w.right) := rfl

/-!
### Mirror kit at the projected type `(S ≀ T).M`

`WreathMonoid.mul_left` and friends are stated at the bare type
`WreathMonoid S T`, but goals about elements of a wreath-product
transformation monoid live at the projected type `(S ≀ T).M` instead — the
two types are definitionally but not syntactically equal, since `(S ≀ T).M`
is a `TransMon.M` projection of the semireducible `wreath`. These four
lemmas are the identical `rfl`-reductions, restated at `(S ≀ T).M` so they
are available directly (`exact`, term-mode, or as rewrite targets once the
goal is already in this shape) without a manual `show`-restatement first.
`simp`/`rw` rewrite through them successfully on the natural goal shape —
`(w * w').left y` / `(1 : (S ≀ T).M).left y` with `y` a plain bound
variable of type `T.X` — even when `S`/`T` are themselves compound
`≀`-expressions. The one pattern that still stalls: supplying an explicit
pair literal `(y, z)` where a nested wreath's state type `(Q ≀ R).X` is
expected, forcing a `Q.X × R.X`-vs-`(Q ≀ R).X` defeq-unfold that trips
`simp`/`rw`'s restricted (`implicit`) transparency matching; `rfl`
(elaborated at default transparency) crosses that case too.
-/

/-- The `left` component of a product at `(S ≀ T).M`: mirrors
`WreathMonoid.mul_left` at the projected type. -/
@[simp] theorem wreath_mul_left {S T : TransMon} (w w' : (S ≀ T).M) (y : T.X) :
    (w * w').left y = w.left y * w'.left (T.act y w.right) := rfl

/-- The `right` component of a product at `(S ≀ T).M`: mirrors
`WreathMonoid.mul_right` at the projected type. -/
@[simp] theorem wreath_mul_right {S T : TransMon} (w w' : (S ≀ T).M) :
    (w * w').right = w.right * w'.right := rfl

/-- The `left` component of the identity at `(S ≀ T).M`: mirrors
`WreathMonoid.one_left` at the projected type. -/
@[simp] theorem wreath_one_left {S T : TransMon} (y : T.X) :
    (1 : (S ≀ T).M).left y = 1 := rfl

/-- The `right` component of the identity at `(S ≀ T).M`: mirrors
`WreathMonoid.one_right` at the projected type. -/
@[simp] theorem wreath_one_right {S T : TransMon} :
    (1 : (S ≀ T).M).right = (1 : T.M) := rfl

/-- Iterated wreath product over a list, right fold with base `trivialTM`:
`wreathList [T₁, T₂, T₃] = T₁ ≀ (T₂ ≀ (T₃ ≀ trivialTM))`. Fixing the
association once avoids an associativity isomorphism in every statement
(spec §3.3). -/
noncomputable def wreathList : List TransMon → TransMon :=
  fun L => L.foldr wreath trivialTM

/-- Folding over the empty list yields the trivial transformation monoid. -/
@[simp] theorem wreathList_nil : wreathList [] = trivialTM := rfl

/-- Unfolding one step of the right fold: `S` wreathed over the iterated
wreath product of the rest of the list. -/
@[simp] theorem wreathList_cons (S : TransMon) (L : List TransMon) :
    wreathList (S :: L) = S ≀ wreathList L := rfl

-- Sanity checks (spec §6). Action evaluation stays rfl-checkable even
-- though `wreath` is noncomputable (defeq is unaffected).
-- Guard: w.left must be evaluated at the CURRENT back-state p.2 = 2,
-- giving (1 * id 2, 2*2) = (2, 1). A wrong definition evaluating w.left
-- at the UPDATED state p.2·w.right = 4 = 1 would give (1 * id 1, 1) =
-- (1, 1) ≠ (2, 1): this example kills that transposition.
example :
    ((regular (ZMod 3)) ≀ (regular (ZMod 3))).act ((1, 2) : ZMod 3 × ZMod 3)
        ⟨fun y => y, (2 : ZMod 3)⟩ =
      ((2, 1) : ZMod 3 × ZMod 3) := rfl

end TransMon
end KRTheory
