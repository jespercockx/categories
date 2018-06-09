
open import Agda.Primitive

record Structure {A : Set₁} (P : A → Prop) : Set₁ where
  no-eta-equality
  field
    raw      : A
    {{laws}} : P raw

open Structure

Relation : Set → Set₁
Relation X = X → X → Prop

record IsEquivalence {A : Set} (R : Relation A) : Prop where
  no-eta-equality
  field
    reflexive  : ∀ {x} → R x x
    symmetric  : ∀ {x y} → R x y → R y x
    transitive : ∀ {x y z} → R x y → R y z → R x z

open IsEquivalence {{...}}

record RawCategory : Set₁ where
  no-eta-equality

  infix  4 _≡_ _⇒_
  infixr 9 _>>>_

  field
    Obj : Set
    _⇒_ : Obj → Obj → Set
    _≡_ : ∀ {A B} → Relation (A ⇒ B)

    id    : ∀ {A} → A ⇒ A
    _>>>_ : ∀ {A B C} → (A ⇒ B) → (B ⇒ C) → (A ⇒ C)


open RawCategory {{...}}

record IsCategory (C : RawCategory) : Prop where
  no-eta-equality
  instance _ = C
  field
    {{is-equiv}} : ∀ {A B} → IsEquivalence (_≡_ {A} {B})

    assoc     : ∀ {A B C D} {f : A ⇒ B} {g : B ⇒ C} {h : C ⇒ D} → f >>> (g >>> h) ≡ (f >>> g) >>> h
    identityˡ : ∀ {A B} {f : A ⇒ B} → id >>> f ≡ f
    identityʳ : ∀ {A B} {f : A ⇒ B} → f >>> id ≡ f

    ∘-resp-≡  : ∀ {A B C} {f h : A ⇒ B} {g i : B ⇒ C} → f ≡ h → g ≡ i → f >>> g ≡ h >>> i


Category = Structure IsCategory

record RawFunctor (C D : RawCategory) : Set where
  no-eta-equality
  instance
    _ = C
    _ = D
  field
    F₀ : Obj {{C}} → Obj {{D}}
    F₁ : ∀ {A B} → A ⇒ B → F₀ A ⇒ F₀ B

open RawFunctor {{...}}

record IsFunctor {C D : Category} (F : RawFunctor (C .raw) (D .raw)) : Set where
  no-eta-equality
  instance
    _ = C .raw
    _ = D .raw
    _ = F
  field
    identity     : ∀ {A} → F₁ (id {A}) ≡ id {F₀ A}
    homomorphism : ∀ {X Y Z} {f : X ⇒ Y} {g : Y ⇒ Z}
                 → F₁ (f >>> g) ≡ F₁ f >>> F₁ g
    F-resp-≡     : ∀ {A B} {f g : A ⇒ B}
                 → f ≡ g → F₁ f ≡ F₁ g
