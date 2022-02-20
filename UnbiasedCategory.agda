{-# OPTIONS --without-K --type-in-type #-}

module UnbiasedCategory where

open import Agda.Builtin.Equality

module TypedLists where
  data TypedList (index : Set) (type : index -> index -> Set) : index -> index -> Set where
    empty : {a : index} -> TypedList index type a a
    fby : {a b c : index} -> type a b -> TypedList index type b c -> TypedList index type a c
  open TypedList public

  append : forall {index : Set} {type : index -> index -> Set} {a b c : index} ->
    TypedList index type a b -> TypedList index type b c -> TypedList index type a c
  append empty s = s
  append (fby x l) s = fby x (append l s)

  concat : forall {index : Set} {type : index -> index -> Set} {a b : index} ->
    TypedList index (TypedList index type) a b -> TypedList index type a b
  concat empty = empty
  concat (fby l s) = append l (concat s)

  map : forall {index : Set} {p : index -> index -> Set} {q : index -> index -> Set} {a b : index} ->
    (forall {a b : index} -> p a b -> q a b) ->
    TypedList index p a b -> TypedList index q a b
  map transform empty = empty
  map transform (fby x l) = fby (transform x) (map transform l)

  fold : forall {index : Set} {type : index -> index -> Set} {p : index -> index -> Set} {a b : index} ->
    (f : forall {a} {b} {c} -> type a b -> p b c -> p a c) -> (z : forall {a} -> p a a) -> TypedList index type a b -> p a b
  fold f z empty = z
  fold f z (fby x l) = f x (fold f z l)
open TypedLists public

module Equality where
  cong : {A B : Set} {x y : A} -> (f : A -> B) -> (x ≡ y) -> f x ≡ f y
  cong f refl = refl

  app : {A B : Set} {f g : A -> B} -> (f ≡ g) -> (a : A) -> f a ≡ g a
  app {A} {B} {f} {g} refl a = refl

  symm : {A : Set} {x y : A} -> (x ≡ y) -> (y ≡ x)
  symm refl = refl

  infixr 2 _≡⟨_⟩_
  _≡⟨_⟩_ : {A : Set} (x : A) {y z : A} → x ≡ y → y ≡ z → x ≡ z
  _ ≡⟨ refl ⟩ p2 = p2

  infix  3 _∎
  _∎ : {A : Set} (x : A) → x ≡ x
  x ∎ = refl

  postulate
    funext : {A B : Set} {f g : A -> B} -> ({a : A} -> f a ≡ g a) -> (f ≡ g)
open Equality public

record Category : Set where
  field
    object : Set
    hom : object -> object -> Set
    compose : {a b : object} -> TypedList object hom a b -> hom a b
    associativity : {a b : object} -> (l : TypedList object (TypedList object hom) a b) ->
      compose (concat l) ≡ compose (map compose l)
open Category {{...}} public

record CategoryConstructor : Set where
  field
    object : Set
    hom : object -> object -> Set
    _>>_ : {a b c : object} -> hom a b -> hom b c -> hom a c
    id : {a : object} -> hom a a
    left-unital : {a b : object} {f : hom a b} -> (id >> f) ≡ f
    right-unital : {a b : object} {f : hom a b} -> (id >> f) ≡ f
    associative : {a b c d : object} {f : hom a b} {g : hom b c} {h : hom c d} ->
      (f >> g) >> h ≡ f >> (g >> h)
open CategoryConstructor public

mkCategory : CategoryConstructor -> Category
mkCategory record
  { object = object
  ; hom = hom
  ; _>>_ = _>>_
  ; id = id
  ; left-unital = left-unital
  ; right-unital = right-unital
  ; associative = associative
  } = record
  { object = object
  ; hom = hom
  ; compose = byFolding
  ; associativity = associativityTotal
  }
 where
   byFolding : {a b : object} -> TypedList object hom a b -> hom a b
   byFolding = fold _>>_ id

   lemma-fold-append : forall {a b c : object} ->
     (p : TypedList object hom a b) -> (q : TypedList object hom b c) ->
     byFolding (append p q) ≡ byFolding (fby (byFolding p) q)
   lemma-fold-append empty q = symm left-unital
   lemma-fold-append (fby f p) q =
     byFolding (fby f (append p q))
       ≡⟨ refl ⟩
     f >> byFolding (append p q)
       ≡⟨ cong (_>>_ f) (lemma-fold-append p q) ⟩
     f >> byFolding (fby (byFolding p) q)
       ≡⟨ refl ⟩
     f >> (byFolding p >> byFolding q)
       ≡⟨ symm associative ⟩
     byFolding (fby f p) >> byFolding q
       ≡⟨ refl ⟩
     byFolding (fby (byFolding (fby f p)) q) ∎

   associativityTotal : {a b : object}
      (l : TypedList object (TypedList object hom) a b) →
      byFolding (concat l) ≡ byFolding (map byFolding l)
   associativityTotal {a} {a} empty = refl
   associativityTotal {a} {b} (fby l s) =
     byFolding (append l (concat s))
       ≡⟨ lemma-fold-append l (concat s) ⟩
     byFolding (fby (byFolding l) (concat s))
       ≡⟨ refl ⟩
     byFolding l >> byFolding (concat s)
       ≡⟨ cong (_>>_ (byFolding l)) (associativityTotal s) ⟩
     byFolding l >> byFolding (map byFolding s)
       ≡⟨ refl ⟩
     byFolding (fby (byFolding l) (map byFolding s)) ∎


categoryOfSets : Category
categoryOfSets = mkCategory
  ( record
  { object = Set
  ; hom = λ A B -> (A -> B)
  ; _>>_ = λ f g a -> g (f a)
  ; id = λ x -> x
  ; left-unital = refl
  ; right-unital = refl
  ; associative = refl
  })
