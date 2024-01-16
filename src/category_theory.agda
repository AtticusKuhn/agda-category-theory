
{-# OPTIONS --cubical #-}
open import Level using (Level; _⊔_; suc)
module category_theory
       where
open import Cubical.Foundations.Prelude
-- open import Cubical.Foundations.
open import Cubical.Foundations.Isomorphism


open import Function using (const ; flip  ; _∘_) renaming (id to id′)

-- ;; open import Felix.Object public

variable
  o ℓ o₁ ℓ₁ o₂ ℓ₂ o₃ ℓ₃ : Level
  obj : Type o
  a b c d e s : obj
  a′ b′ c′ d′ e′ : obj


record Category {obj : Type o} (_⇨_ : obj → obj → Type ℓ) : Type (o ⊔ ℓ) where
  infixr 9 _≫_
  field
    id  : a ⇨ a
    _≫_ : a ⇨ b → b ⇨ c → a ⇨ c
    id-right : (f : a ⇨ b) → f ≫ id ≡ f
    id-left : (f : a ⇨ b) → id ≫ f ≡ f
    assoc : (f : a ⇨ b) (g : b ⇨ c) (h : c ⇨ d) → (f ≫ g) ≫ h ≡ f ≫ (g ≫ h)

open Category


oppositeCategory : (_⇨_ : obj → obj → Type ℓ) → Category _⇨_ → Category (flip _⇨_)
oppositeCategory arr cat = record {
  id = id cat
  ; _≫_ = flip (_≫_ cat)
  ; id-right = id-left cat
  ; id-left = id-right cat
  ; assoc = λ f g h  → sym (assoc cat h g f)}
functionCat : {ℓ : Agda.Primitive.Level} → Category {ℓ = ℓ} (λ A B → A → B)
functionCat = record
  { id = λ x → x
  ; _≫_ = λ f g x → g (f x)
  ; id-right = λ f i x → f x
  ; id-left = λ f i x → f x
  ; assoc = λ f g h  → refl}

record isTerminal {obj : Type o} {_⇨_ : obj → obj → Type ℓ} (c : Category _⇨_ ) (⊤ : obj) : Type (o ⊔ ℓ) where
  field
    bang : (x  : obj) → x ⇨ ⊤
    unique : {x : obj} (f : x ⇨ ⊤) → f ≡ bang x

record isomorphism {obj : Type o} {_⇨_ : obj → obj → Type ℓ} (c : Category _⇨_ ) (a b : obj) : Type (o ⊔ ℓ) where
  private infix 0 _≫'_; _≫'_ = _≫_ c
  field
    from : a ⇨ b
    to : b ⇨ a
    fromto :  (from ≫' to) ≡  id c
    tofrom :  (to ≫' from) ≡ id c
-- isoeq : {obj : Type o} {_⇨_ : obj → obj → Type ℓ} (c : Category _⇨_ ) (a b : obj) → isomorphism c a b → a ≡ b
-- isoeq   c a b x  i = {!!}
uniqueTerminal : {obj : Type o} {_⇨_ : obj → obj → Type ℓ}
  (c : Category _⇨_ ) (⊤₁ ⊤₂ : obj ) → isTerminal c ⊤₁ → isTerminal c ⊤₂ → isomorphism c ⊤₁ ⊤₂
uniqueTerminal c ⊤₁ ⊤₂ record { bang = bang1 ; unique = unique1 } record { bang = bang2 ; unique = unique2 }
  = record {
    from = bang2 ⊤₁
    ; to = bang1 ⊤₂
    ; fromto = unique1 ( (c ≫ bang2 ⊤₁) (bang1 ⊤₂)) ∙ sym (unique1 (id c))
    ; tofrom =  unique2 ((c ≫ bang1 ⊤₂) (bang2 ⊤₁)) ∙ sym {!unique!} }

variable
  obj₁ : Set o₁
  obj₂ : Set o₂
  obj₃ : Set o₃
  _⇨₁_ : obj₁ → obj₁ → Set ℓ₁
  _⇨₂_ : obj₂ → obj₂ → Set ℓ₂
  _⇨₃_ : obj₃ → obj₃ → Set ℓ₃
  a₁ b₁ : obj₁
  C : Category _⇨₁_
  D : Category _⇨₂_
  E : Category _⇨₃_

data Maybe (x : Type) : Type where
  Nothing : Maybe x
  Just : x → Maybe x


maybeBind : {A B C : Type} →  (A → Maybe B) → (B → Maybe C) → (A → Maybe C)
maybeBind  x y z with (x z)
...    | Just a = y a
...    | Nothing = Nothing
errorCat :  Category {ℓ = Agda.Primitive.lzero} (λ A B → (A → Maybe B))
errorCat = record
            {
            id = Just
            ; _≫_ = maybeBind
            ; id-right = λ f i x → {!!}
            ; id-left = {!!}
            ; assoc = {!!} }

record Functor  {obj₁ : Set o₁} {obj₂ : Set o₂} {_⇨₁_ : obj₁ → obj₁ → Set ℓ₁} {_⇨₂_ : obj₂ → obj₂ → Set ℓ₂}  (C : Category _⇨₁_) (D : Category _⇨₂_) : Set (o₁ ⊔ o₂ ⊔ ℓ₁ ⊔ ℓ₂) where
  field
    Fₒ : obj₁ → obj₂
    Fₐ :     (a₁ ⇨₁ b₁) → ( Fₒ a₁ ⇨₂ Fₒ b₁)
    F-id : {a : obj₁} →  Fₐ {a₁ = a} (id C) ≡ id D
    F-∘ : {a b c : obj₁} {f : a ⇨₁ b} {g : b ⇨₁ c} →   Fₐ (_≫_ C f g) ≡ _≫_ D (Fₐ f) (Fₐ g)



open Functor


Endofunctor : {obj₁ : Set o₁}  {_⇨₁_ : obj₁ → obj₁ → Set ℓ₁} → Category _⇨₁_  → Set (o₁ ⊔  ℓ₁)
Endofunctor C =  Functor C C


identityfunctor : Endofunctor  C
identityfunctor = record {
  Fₒ = λ x → x
  ; Fₐ = λ x → x
  ; F-id = refl
  ; F-∘ = refl
  }

fmapMaybe : (a → b) → Maybe a → Maybe b
fmapMaybe f Nothing = Nothing
fmapMaybe f (Just x) = Just (f x)

fmapId : {a : Type} → fmapMaybe {a = a} {b = a} (λ x → x) ≡ (λ x → x)
fmapId i Nothing = Nothing
fmapId i (Just x) = Just x

∘maybe :  {a b c : Type} {f : a → b} {g : b → c} →
    fmapMaybe ((functionCat ≫ f) g) ≡
    (functionCat ≫ fmapMaybe f) (fmapMaybe g)
∘maybe i Nothing = Nothing
∘maybe {f = f} {g = g} i (Just x) = Just (g (f x))
maybeFunctor : Functor functionCat functionCat
maybeFunctor = record
  { Fₒ = Maybe
  ; Fₐ = fmapMaybe
  ; F-id = fmapId
  ; F-∘ = ∘maybe }

composeFunctors : {A : Category _⇨₁_} {B : Category _⇨₂_} {C : Category _⇨₃_}→ Functor A B → Functor B C → Functor A C
composeFunctors a b = record {
  Fₒ = Fₒ b ∘ Fₒ a
  ; Fₐ  =  Fₐ b ∘ Fₐ a
  ; F-id = {!!}
  ; F-∘ = {!!} }

data List (x : Type) : Type where
  [] : List x
  Cons : x → List x → List x

fmapList : (a → b) → List a → List b
fmapList f [] = []
fmapList f (Cons x xs) = Cons (f x) (fmapList f xs)

fmapLID : {a : Type} →  fmapList {a = a} {b = a} (λ x → x) ≡ λ x → x
fmapLID _ [] = []
fmapLID i (Cons x xs) = Cons x (fmapLID i xs)

∘List :  {a b c : Type} {f : a → b} {g : b → c} →
    fmapList ((functionCat ≫ f) g) ≡
    (functionCat ≫ fmapList f) (fmapList g)
∘List i [] = []
∘List {f = f} {g = g} i (Cons x xs) = Cons (g (f x)) (∘List {f = f} {g = g} i xs)
listFunctor : Functor functionCat functionCat
listFunctor = record
  { Fₒ = List
  ; Fₐ = fmapList
  ; F-id = fmapLID
  ; F-∘ = ∘List }

record NaturalTransformation  {obj₁ : Set o₁} {obj₂ : Set o₂} {_⇨₁_ : obj₁ → obj₁ → Set ℓ₁} {_⇨₂_ : obj₂ → obj₂ → Set ℓ₂} {C : Category _⇨₁_} {D : Category _⇨₂_} (F₁ : Functor C D) (F₂ : Functor C D) : Set (o₁ ⊔ o₂ ⊔ ℓ₁ ⊔ ℓ₂) where
  field
    τ : (c : obj₁) → (Fₒ F₁ c ⇨₂ Fₒ F₂ c)
    τ-natural : {c c' : obj₁} {f : c ⇨₁ c'} → (_≫_ D (τ c) (Fₐ F₂ f)) ≡ (_≫_ D (Fₐ F₁ f) (τ c'))

open NaturalTransformation
variable
  F : Functor C D
  G : Functor D E
  H : Functor C E
id-nattrans : (a : Functor C D) → NaturalTransformation a a
id-nattrans {C = C} {D = D} a  = record {
  τ = λ c → id D
  ; τ-natural = λ {_} {_} {f3}   → (id-left D (Fₐ a f3) ∙ sym (id-right D (Fₐ a f3)))
  }

vertical-comp : NaturalTransformation F G → NaturalTransformation G H → NaturalTransformation F H
vertical-comp {_} {_} {_} {D} {E} {_} {L} {_} {I} {J} a b = record {
  τ = λ c → (J ≫ (τ a c)) (τ b c)
  ; τ-natural = {!!}
  }

idaux : {a : Functor C C} → NaturalTransformation a a
idaux {a = a} = id-nattrans a
endofunctorcategory : (C : Category _⇨₁_) → Category (NaturalTransformation {C = C} {D = C})
endofunctorcategory {q} {b} {c} {d}   C  = record {
  id = idaux
  ; _≫_ = vertical-comp
  ; id-right = {!!}
  ; id-left = {!!}
  ; assoc = {!!}}

shead : List a → Maybe a
shead [] = Nothing
shead (Cons x _) = Just x
-- fmap f (head xs) ≡ head (fmap f xs)
sheadnatural  : {c c' : Type} {f : c → c'} → (functionCat ≫ shead) (Fₐ maybeFunctor f) ≡ (functionCat ≫ Fₐ listFunctor f) shead
sheadnatural _ [] = Nothing
sheadnatural {f = f} _ (Cons x _) = Just (f x)

safeHead : NaturalTransformation  (listFunctor) (maybeFunctor)
safeHead = record
  { τ = λ c → shead {a = c}
  ; τ-natural = sheadnatural }


record Products (obj : Set o) : Set o where
  -- infixr 2 _×_
  field
    ⊤ : obj
    prod : obj → obj → obj
open Products public

record Coproducts (obj : Set o) : Set o where
  infixr 2 _⊎_
  field
    ⊥ : obj
    _⊎_ : obj → obj → obj
open Coproducts ⦃ … ⦄ public

record Exponentials (obj : Set o) : Set o where
  infixr 1 _⇛_
  field
    _⇛_ : obj → obj → obj
open Exponentials ⦃ … ⦄ public

record Monoidal
       {obj : Set o}
       (p : Products obj)
       {_⇨_ : obj → obj → Set ℓ}
         (cat  : Category _⇨_ )
    : Set (o ⊔ ℓ) where
  infixr 7 _⊗_
  field
    unitor : prod p a (⊤ p) ≡ a
    unitol : prod p (⊤ p) a ≡ a
    _⊗_ : (a ⇨ c) → (b ⇨ d) → (prod p a b ⇨ prod p  c d)
    assoc : prod p a (prod p b c) ≡ prod p (prod p a b) c


-- monoidalendo : (C : Category _⇨₁_) → Monoidal ( endofunctorcategory C)

record Monoid { obj : Set o} {p : Products obj} {_⇨_  : obj → obj → Set ℓ} {cat : Category _⇨_} (m : Monoidal p  cat)  : Set (o ⊔ ℓ) where
  field
    M : obj
    μ : prod p M M ⇨ M
    η : ⊤ p ⇨ M


-- Monad : (C : Category _⇨₁_) → Monoid

append : {A : Set} → List A → List A → List A
append [] x = x
append (Cons a b) c = Cons a (append b c)


data Pair (A B : Set) : Set where
  mkPair : (a : A) (b : B) → Pair A B

left : {A B : Set} →  Pair A B → A
left (mkPair a b) = a

right : {A B : Set} →  Pair A B → B
right (mkPair a b) = b
data Unit : Set where
  u : Unit


unitContractable : (a b : Unit) → a ≡ b
unitContractable u u = refl
unitTerminal : isTerminal functionCat Unit
unitTerminal = record {
  bang = λ _ _ → u
  ; unique = λ f  → funExt λ x → unitContractable (f x) u }
bimap :  {a c b d : Type} → (a → c) → (b → d) → Pair a b → Pair c d
bimap f g (mkPair a b) = mkPair (f a) (g b)

ret : {B : Set} → retract { B = B } (λ z → left z) (λ x → mkPair x u)
ret (mkPair a u)= refl
unitorPair : {a : Set} → (Pair a Unit ≡ a)
unitorPair =  isoToPath (iso left (λ x → mkPair x u) (λ b → refl) ret)

ret2 : {B : Set} → retract { B = B } (right) (mkPair u)
ret2 (mkPair u a)= refl
unitolPair : {a : Set} → (Pair Unit a ≡ a)
unitolPair =  isoToPath (iso right ( mkPair u) (λ b i → b) ret2)

pairassocl : {a b c : Set} →  Pair a (Pair b c) → Pair (Pair a b) c
pairassocl (mkPair a (mkPair b c)) = mkPair (mkPair a b) c

pairassocr : {a b c : Set} →  Pair (Pair a b) c →  Pair a (Pair b c)
pairassocr (mkPair (mkPair a b) c) =  (mkPair a (mkPair b c))

setPair :{a b c : Set} →  section (pairassocl {a} {b} {c}) pairassocr
setPair (mkPair (mkPair a b) d) = refl

retPair :{a b c : Set} →  retract (pairassocl {a} {b} {c}) pairassocr
retPair (mkPair a (mkPair b c)) = refl
assocPair :  {a b c : Type} → Pair a (Pair b c) ≡ Pair (Pair a b) c
assocPair  =  isoToPath (iso pairassocl pairassocr (setPair) retPair)
productsFun  : Products Set
productsFun = record {
  ⊤ = Unit
  ; prod = Pair }
monoidFun : Monoidal productsFun functionCat
monoidFun = record {
  unitor = unitorPair
  ; unitol = unitolPair
  ; _⊗_ = bimap
  ; assoc = assocPair }

uncurry : {A B C  : Set} → (A → B → C) → (Pair A B → C)
uncurry f (mkPair a b) = f a b
appendMonoid : Set →  Monoid monoidFun
appendMonoid A = record {
  M = List A
  ; μ = uncurry append
  ; η = const [] }


-- record Monad1 (C : Category _⇨₁_) : Type where
--   field
--     T : Endofunctor C
--     eta : NaturalTransformation identityfunctor {!T!}
