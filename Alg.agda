{-# OPTIONS --cubical --guardedness --safe #-}

module Alg where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

record Sig : Type₁ where
  field
    op : Type
    ar : op → Type
open Sig

SigF : Sig → Type → Type
SigF σ X = Σ (σ .op) (\o → σ .ar o → X)

record Alg (σ : Sig) : Type₁ where
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

TreeAlg : ∀ σ V → Alg σ
TreeAlg σ V .car = Tree σ V
TreeAlg σ V .alg = node 

_♯ : ∀ {σ V} → {{𝔛 : Alg σ}} → (f : V → 𝔛 .car) → Tree σ V → 𝔛 .car
_♯ {σ} {V} {{𝔛}} f = indTree σ V (\_ → 𝔛 .car) f \(o , f) r → 𝔛 .alg (o , r)
