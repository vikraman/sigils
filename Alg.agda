{-# OPTIONS --cubical --guardedness --safe #-}

module Alg where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Data.Sigma
open import Cubical.Data.Sum
open import Cubical.Data.Unit
open import Cubical.Data.Empty

record Sig : Type₁ where
  constructor [_,_]
  field
    op : Type
    ar : op → Type
open Sig

SigF : Sig → Type → Type
SigF σ X = Σ (σ .op) (\o → σ .ar o → X)

record Alg (σ : Sig) : Type₁ where
  constructor <_,_>
  field
    car : Type
    alg : SigF σ car → car
open Alg

data Tree (σ : Sig) (V : Type) : Type where
  var : V → Tree σ V
  node : SigF σ (Tree σ V) → Tree σ V

indTree : (σ : Sig) (V : Type) (P : Tree σ V → Type)
       → (var* : (v : V) → P (var v))
       → (node* : ((o , f) : SigF σ (Tree σ V)) → ((a : σ .ar o) → P (f a)) → P (node (o , f)))
       → (t : Tree σ V) → P t
indTree σ V P var* node* (var x) = var* x
indTree σ V P var* node* (node (o , g)) = node* (o , g) (indTree σ V P var* node* ∘ g)

recTree : (σ : Sig) (V : Type) (P : Type)
       → (var* : (v : V) → P)
       → (node* : ((o , f) : SigF σ (Tree σ V)) → ((a : σ .ar o) → P) → P)
       → (t : Tree σ V) → P
recTree σ V P = indTree σ V (λ _ → P)

TreeAlg : ∀ σ V → Alg σ
TreeAlg σ V .car = Tree σ V
TreeAlg σ V .alg = node

eval : ∀ {σ V} → (𝔛 : Alg σ) → (f : V → 𝔛 .car) → Tree σ V → 𝔛 .car
eval {σ} {V} 𝔛 f = recTree σ V (𝔛 .car) f \(o , f) r → 𝔛 .alg (o , r)

record EqSig : Type₁ where
  constructor [_,_]
  field
    eq : Type
    fv : eq → Type
open EqSig

SysEq : (σ : Sig) (ε : EqSig) → Type
SysEq σ ε = (e : ε .eq) → Tree σ (ε .fv e) × Tree σ (ε .fv e)

_⊨_ : ∀ {σ ε} → (𝔛 : Alg σ) (τ : SysEq σ ε) → Type
_⊨_ {σ} {ε} 𝔛 τ = (e : ε .eq) (ρ : ε .fv e → 𝔛 .car) → eval 𝔛 ρ (τ e .fst) ≡ eval 𝔛 ρ (τ e .snd)

data Free (σ : Sig) (ε : EqSig) (τ : SysEq σ ε) (A : Type) : Type where
  var : A → Free σ ε τ A
  node : SigF σ (Free σ ε τ A) → Free σ ε τ A
  sat : (e : ε .eq) (ρ : ε .fv e → Free σ ε τ A)
    → recTree σ (ε .fv e) (Free σ ε τ A) ρ (λ { (o , g) r → node (o , r) }) (τ e .fst)
     ≡ recTree σ (ε .fv e) (Free σ ε τ A) ρ (λ { (o , g) r → node (o , r) }) (τ e .snd)

data MonOp : Type where
  `unit `mult : MonOp

MonAr : MonOp → Type
MonAr `unit = ⊥
MonAr `mult = Unit ⊎ Unit

MonSig : Sig
MonSig = [ MonOp , MonAr ]

data MonEq : Type where
  `assoc `unitl `unitr : MonEq

MonFv : MonEq → Type
MonFv `assoc = Unit ⊎ (Unit ⊎ Unit)
MonFv `unitl = Unit
MonFv `unitr = Unit

MonEqSig : EqSig
MonEqSig = [ MonEq , MonFv ]

MonSysEq : SysEq MonSig MonEqSig
MonSysEq `assoc =
    node (`mult , λ { (inl _) → node (`mult , λ { (inl _) → var (inl tt) ; (inr _) → var (inr (inl tt)) }) ; (inr _) → var (inr (inr tt)) })
  , node (`mult , λ { (inl _) → var (inl tt) ; (inr _) → node (`mult , λ { (inl _) → var (inr (inl tt)) ; (inr _) → var (inr (inr tt)) }) })
MonSysEq `unitr = 
    node (`mult , λ { (inl _) → var tt ; (inr _) → node (`unit , λ ()) }) 
  , var tt
MonSysEq `unitl = 
    node (`mult , λ { (inl _) → node (`unit , λ ()) ; (inr _) → var tt }) 
  , var tt

FreeMon : Type → Type
FreeMon A = Free MonSig MonEqSig MonSysEq A

variable
  A : Type

η : A → FreeMon A
η = var

ϵ : FreeMon A
ϵ = node (`unit , λ ())

_⊗_ : FreeMon A → FreeMon A → FreeMon A
m ⊗ n = node (`mult , λ { (inl _) → m ; (inr _) → n })

unitr : (m : FreeMon A) → m ⊗ ϵ ≡ m
unitr m =
    congS (λ z → node (`mult , z)) (funExt λ { (inl _) → refl ; (inr _) → congS (λ z → node (`unit , z)) (funExt λ ()) })
  ∙ sat `unitr (λ _ → m)

unitl : (m : FreeMon A) → ϵ ⊗ m ≡ m
unitl m =
    congS (λ z → node (`mult , z)) (funExt λ { (inl _) → congS (λ z → node (`unit , z)) (funExt λ ()) ; (inr _) → refl })
  ∙ sat `unitl λ _ → m

assoc : (m n o : FreeMon A) → (m ⊗ n) ⊗ o ≡ m ⊗ (n ⊗ o)
assoc m n o =
    congS (λ z → node (`mult , z)) (funExt λ { (inl _) → congS (λ z → node (`mult , z)) (funExt λ { (inl _) → refl ; (inr _) → refl }) ; (inr _) → refl })
  ∙ sat `assoc (λ { (inl _) → m ; (inr (inl _)) → n ; (inr (inr _)) → o })
  ∙ congS (λ z → node (`mult , z)) (funExt λ { (inl x) → refl ; (inr x) → congS (λ z → node (`mult , z)) (funExt (λ { (inl _) → refl ; (inr _) → refl })) })
