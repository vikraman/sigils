{-# OPTIONS --cubical --guardedness -WnoUnsupportedIndexedMatch #-}

module Alg2 where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Data.Sigma

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
    alg : (o : σ .op) → (σ .ar o → car) → car
open Alg

record EqSig : Type₁ where
  constructor [_,_]
  field
    eq : Type
    fv : eq → Type
open EqSig

data Tree (σ : Sig) (V : Type) : Type where
  var : V → Tree σ V
  node : (o : σ .op) → (g : σ .ar o → Tree σ V) → Tree σ V

recTree : (σ : Sig) (V : Type) (P : Type)
       → (var* : (v : V) → P)
       → (node* : (o : σ .op) → ((a : σ .ar o) → P) → P)
       → (Tree σ V) → P
recTree σ V P var* node* (var v) = var* v
recTree σ V P var* node* (node o g) = node* o (recTree σ V P var* node* ∘ g)

eval : ∀ {σ V} → (𝔛 : Alg σ) → (f : V → 𝔛 .car) → Tree σ V → 𝔛 .car
eval {σ} {V} 𝔛 f = recTree σ V (𝔛 .car) f (𝔛 .alg)

SysEq : (σ : Sig) (ε : EqSig) → Type
SysEq σ ε = (e : ε .eq) → Tree σ (ε .fv e) × Tree σ (ε .fv e)

data Free (σ : Sig) (ε : EqSig) (τ : SysEq σ ε) (A : Type) : Type where
  var : A → Free σ ε τ A
  node : (o : σ .op) → (g : σ .ar o → Free σ ε τ A) → Free σ ε τ A
  sat : (e : ε .eq) (ρ : ε .fv e → Free σ ε τ A)
     → recTree σ (ε .fv e) (Free σ ε τ A) ρ node (τ e .fst) ≡ recTree σ (ε .fv e) (Free σ ε τ A) ρ node (τ e .snd) 

mutual
  {-# TERMINATING #-}
  recFree : (σ : Sig) (ε : EqSig) (τ : SysEq σ ε) (V : Type) (P : Type)
          → (var* : (v : V) → P)
          → (node* : (o : σ .op) → ((a : σ .ar o) → P) → P)
          → (sat* : (e : ε .eq) (ρ : ε .fv e → P) → recTree σ (ε .fv e) P ρ node* (τ e .fst) ≡ recTree σ (ε .fv e) P ρ node* (τ e .snd))
          → Free σ ε τ V → P 
  recFree σ ε τ V P var* node* sat* (var v) = var* v
  recFree σ ε τ V P var* node* sat* (node o g) = node* o (recFree σ ε τ V P var* node* sat* ∘ g)
  recFree σ ε τ V P var* node* sat* (sat e ρ i) = 
    hcomp (λ j → λ { (i = i0) → nat σ ε τ V P var* node* sat* e ρ (τ e .fst) (~ j) 
                     ; (i = i1) → nat σ ε τ V P var* node* sat* e ρ (τ e .snd) (~ j) })
          (sat* e (recFree σ ε τ V P var* node* sat* ∘ ρ) i)

  nat : (σ : Sig) (ε : EqSig) (τ : SysEq σ ε) (V : Type) (P : Type)
     → (var* : (v : V) → P)
     → (node* : (o : σ .op) → ((a : σ .ar o) → P) → P)
     → (sat* : (e : ε .eq) (ρ : ε .fv e → P) → recTree σ (ε .fv e) P ρ node* (τ e .fst) ≡ recTree σ (ε .fv e) P ρ node* (τ e .snd))
     → (e : ε .eq) (ρ : ε .fv e → (Free σ ε τ V)) (t : Tree σ (ε .fv e))
     → recFree σ ε τ V P var* node* sat* (recTree σ (ε .fv e) (Free σ ε τ V) ρ node t)
      ≡ recTree σ (ε .fv e) P (recFree σ ε τ V P var* node* sat* ∘ ρ) node* t
  nat σ ε τ V P var* node* sat* e ρ (var v) = refl
  nat σ ε τ V P var* node* sat* e ρ (node o g) = congS (node* o) (funExt (λ a → nat σ ε τ V P var* node* sat* e ρ (g a)))
