{-# OPTIONS --cubical --guardedness -WnoUnsupportedIndexedMatch #-}

module Alg where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Data.Sigma
open import Cubical.Data.Sum as S
open import Cubical.Data.Unit
open import Cubical.Data.Empty
open import Cubical.Induction.WellFounded
open import Cubical.Data.FinData as F hiding (eq) 
open import Cubical.Data.Vec renaming (Vec→FinVec to vec ; FinVec→Vec to fin)
open VecPath renaming (decode to vec≡)

elim0
  : ∀ {ℓ} {P : Fin 0 → Type ℓ}
  → (f0 : Fin 0) → P f0
elim0 ()

pelim0
  : ∀ {ℓ} {P : Type ℓ} {l r : Fin 0 → P}
  → l ≡ r
pelim0 = funExt elim0

elim1
  : ∀ {ℓ} {P : Fin 1 → Type ℓ}
  → P zero
  → (f1 : Fin 1) → P f1
elim1 p0 zero = p0

pelim1
  : ∀ {ℓ} {P : Type ℓ} {l r : Fin 1 → P}
  → l zero ≡ r zero
  → l ≡ r
pelim1 p0 = funExt (elim1 p0)

elim2
  : ∀ {ℓ} {P : Fin 2 → Type ℓ}
  → P zero
  → P one
  → (f2 : Fin 2) → P f2
elim2 p0 p1 zero = p0
elim2 p0 p1 one = p1

pelim2
  : ∀ {ℓ} {P : Type ℓ} {l r : Fin 2 → P}
  → l zero ≡ r zero
  → l one ≡ r one
  → l ≡ r
pelim2 p0 p1 = funExt (elim2 p0 p1)

elim3
  : ∀ {ℓ} {P : Fin 3 → Type ℓ}
  → P zero
  → P one
  → P two
  → (f3 : Fin 3) → P f3
elim3 p0 p1 p2 zero = p0
elim3 p0 p1 p2 one = p1
elim3 p0 p1 p2 two = p2

pelim3
  : ∀ {ℓ} {P : Type ℓ} {l r : Fin 3 → P}
  → l zero ≡ r zero
  → l one ≡ r one
  → l two ≡ r two
  → l ≡ r
pelim3 p0 p1 p2 = funExt (elim3 p0 p1 p2)

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
       → (Tree σ V) → P
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

-- indFree : {A : Type} {σ : Sig} {ε : EqSig} {τ : SysEq σ ε} (𝔅 : Alg σ) (P : Free σ ε τ A → Type)
--     → (var* : (a : A) → P (var a))
--     → (node* : ((o , f) : SigF σ (Free σ ε τ A)) → ((a : σ .ar o) → P (f a)) → P (node (o , f)))
--     → (sat* : (e : ε .eq) → (ρ : ε .fv e → Free σ ε τ A)
--         → PathP (λ i → P (sat e ρ i))
--                 (recTree σ (ε .fv e) (P {!   !}) {!   !} {!   !} {!   !})
--                 (recTree σ (ε .fv e) (P {!   !}) {!   !} {!   !} {!   !}))
--     → (t : Free σ ε τ A) → P t
-- indFree = {!   !}

algHomNat : {A : Type} {σ : Sig} (P : Type)
    → (varP : (a : A) → P)
    → (nodeP : (SigF σ P) → P)
    (Q : Type)
    → (varQ : (a : A) → Q)
    → (nodeQ : (SigF σ Q) → Q)
    → (f : Q → P) → (((o , g) : SigF σ Q) → f (nodeQ (o , g)) ≡ nodeP ((o , λ y → f (g y) )) )
    → (X : Type) → (ρ : X → Q) → (t : Tree σ X)
    → f (recTree σ X Q ρ (λ { (o , g) r → nodeQ (o , r) }) t)
    ≡ recTree σ X P (λ x → f (ρ x)) (λ { (o , g) r → nodeP (o , r) }) t
algHomNat P varP nodeP Q varQ nodeQ f hom X ρ (var x) = refl
algHomNat {σ = σ} P varP nodeP Q varQ nodeQ f hom X ρ (node x)
    = hom (x .fst , (λ x₁ → recTree σ X Q ρ (λ { (o , g) r → nodeQ (o , r) })
        (x .snd x₁))) ∙ cong (λ z → nodeP (x .fst , z)) (funExt (λ y → algHomNat P varP nodeP Q varQ nodeQ f hom X ρ (x .snd y)))




-- recFree : {A : Type} {σ : Sig} {ε : EqSig} {τ : SysEq σ ε} (P : Type)
--     → (var* : (a : A) → P)
--     → (node* : ((o , f) : SigF σ P) → P)
--     → (sat* : (e : ε .eq) → (ρ : ε .fv e → P)
--         → recTree σ (ε .fv e) P ρ (λ { (o , g) r → node* (o , r)}) (τ e .fst)
--         ≡ recTree σ (ε .fv e) P ρ (λ { (o , g) r → node* (o , r)}) (τ e .snd))
--     → (Free σ ε τ A) → P
-- recFree P var* node* sat* (var x) = var* x
-- recFree P var* node* sat* (node (o , g)) = node* (o , λ x → recFree P var* node* sat* (g x))
-- recFree {A = A} {σ = σ} {ε = ε} {τ = τ} P var* node* sat* (sat e ρ i)
--     = (algHomNat P var* node* (Free σ ε τ A) var node
--         (recFree P var* node* sat*) (λ y → {!  !}) (ε .fv e) ρ (τ e .fst)
--         ∙ sat* e (λ y → recFree P var* node* sat* (ρ y))
--         ∙ sym (algHomNat P var* node* (Free σ ε τ A) var node
--         (recFree P var* node* sat*) (λ y → {!  !}) (ε .fv e) ρ (τ e .snd))) i

-- module _ {A : Type} {σ : Sig} {ε : EqSig} {τ : SysEq σ ε} where

--     data Subtree : Free σ ε τ A → Free σ ε τ A → Type where
--         subtree : ∀ {o} {g} → ∀ x → Subtree (g x) (node (o , g))

--     -- varSubtree : ∀ {x} {y} → Subtree y (var x) → ⊥
--     -- varSubtree t = 

--     isAcc : (t : Free σ ε τ A) → Acc Subtree t
--     isAcc (var x) = acc λ y → {!   !}
--     isAcc (node x) = {!   !}
--     isAcc (sat e ρ i) = {!   !}



-- mutual
    -- recFree : {A : Type} {σ : Sig} {ε : EqSig} {τ : SysEq σ ε} (P : Type)
    --     → (var* : (a : A) → P)
    --     → (node* : ((o , f) : SigF σ P) → P)
    --     → (sat* : (e : ε .eq) → (ρ : ε .fv e → P)
    --         → recTree σ (ε .fv e) P ρ (λ { (o , g) r → node* (o , r)}) (τ e .fst)
    --         ≡ recTree σ (ε .fv e) P ρ (λ { (o , g) r → node* (o , r)}) (τ e .snd))
    --     → (Free σ ε τ A) → P
    -- recFree P var* node* sat* (var x) = var* x
    -- recFree P var* node* sat* (node (o , g)) = node* (o , λ x → recFree P var* node* sat* (g x))
    -- recFree {A = A} {σ = σ} {ε = ε} {τ = τ} P var* node* sat* (sat e ρ i)
    --     = (algHomNat P var* node* (Free σ ε τ A) var node
    --         (recFree P var* node* sat*) (λ y → {!  !}) (ε .fv e) ρ (τ e .fst)
    --         ∙ sat* e (λ y → recFree P var* node* sat* (ρ y))
    --         ∙ sym (algHomNat P var* node* (Free σ ε τ A) var node
    --         (recFree P var* node* sat*) (λ y → {!  !}) (ε .fv e) ρ (τ e .snd))) i
        -- = (lemma P var* node* sat* (ε .fv e) ρ (τ e .fst)
        --     ∙ sat* e (λ y → recFree P var* node* sat* (ρ y))
            -- ∙ sym (lemma P var* node* sat* (ε .fv e) ρ (τ e .snd))) i


    -- lemma : {A : Type} {σ : Sig} {ε : EqSig} {τ : SysEq σ ε} (P : Type)
    --     → (var* : (a : A) → P)
    --     → (node* : (SigF σ P) → P)
    --     → (sat* : (e : ε .eq) → (ρ : ε .fv e → P)
    --         → recTree σ (ε .fv e) P ρ (λ { (o , g) r → node* (o , r)}) (τ e .fst)
    --         ≡ recTree σ (ε .fv e) P ρ (λ { (o , g) r → node* (o , r)}) (τ e .snd))
    --     → (X : Type) → (ρ : X → Free σ ε τ A) → (y : Tree σ X)
    --     → recFree P var* node* sat* (recTree σ X (Free σ ε τ A) ρ (λ { (o , g) r → node (o , r) }) y)
    --     ≡ recTree σ X P (λ x → recFree P var* node* sat* (ρ x)) (λ { (o , g) r → node* (o , r) }) y
    -- lemma P var* node* sat* X ρ (var x) = refl
    -- lemma P var* node* sat* X ρ (node x) = cong (λ z → node* (x .fst , z)) (funExt (λ y → lemma P var* node* sat* X ρ (x .snd y)))

{-

-- _♯ : {A : Type} {σ : Sig} {ε : EqSig} {τ : SysEq σ ε} (𝔅 : Alg σ) (p : 𝔅 ⊨ τ) → (A → 𝔅 .car) → (Free σ ε τ A → 𝔅 .car)
-- _♯ 𝔅 p f (var x) = f x
-- _♯ 𝔅 p f (node (o , g)) = 𝔅 .alg (o , λ x → (_♯ 𝔅 p f) (g x))
-- _♯ 𝔅 p f (sat e ρ i) = {! p e (λ x → (_♯ 𝔅 p f) (ρ x)) !}


-}

-- -----------------------------------------------------------------------------
-- Monoid example
-- -----------------------------------------------------------------------------

data MonOp : Type where
  `unit `mult : MonOp

MonAr : MonOp → Type
MonAr `unit = Fin 0
MonAr `mult = Fin 2

MonSig : Sig
MonSig = [ MonOp , MonAr ]

data MonEq : Type where
  `assoc `unitl `unitr : MonEq

MonFv : MonEq → Type
MonFv `assoc = Fin 3
MonFv `unitl = Fin 1
MonFv `unitr = Fin 1

MonEqSig : EqSig
MonEqSig = [ MonEq , MonFv ]

MonSysEq : SysEq MonSig MonEqSig
MonSysEq `assoc =
    node (`mult , vec (node (`mult , vec (var zero ∷ var one ∷ [])) ∷ var two ∷ []))
  , node (`mult , vec (var zero ∷ node (`mult , vec (var one ∷ var two ∷ [])) ∷ []))
MonSysEq `unitr = 
    node (`mult , vec (var zero ∷ node (`unit , vec []) ∷ []))
  , var zero
MonSysEq `unitl = 
    node (`mult , vec (node (`unit , vec []) ∷ var zero ∷ []))
  , var zero

FreeMon : Type → Type
FreeMon A = Free MonSig MonEqSig MonSysEq A

variable
  A : Type

η : A → FreeMon A
η = var

ϵ : FreeMon A
ϵ = node (`unit , vec [])

_⊗_ : FreeMon A → FreeMon A → FreeMon A
m ⊗ n = node (`mult , vec (m ∷ n ∷ []))

unitr : (m : FreeMon A) → m ⊗ ϵ ≡ m
unitr {A = A} m = 
    congS (λ z → node (`mult , z)) (pelim2 refl (congS (λ z → node (`unit , z)) pelim0))
  ∙ sat `unitr (vec (m ∷ []))

unitl : (m : FreeMon A) → ϵ ⊗ m ≡ m
unitl m =
    congS (λ z → node (`mult , z)) (pelim2 (congS (λ z → node (`unit , z)) pelim0) refl)
  ∙ sat `unitl (vec (m ∷ []))

assoc : (m n o : FreeMon A) → (m ⊗ n) ⊗ o ≡ m ⊗ (n ⊗ o)
assoc m n o =
    congS (λ z → node (`mult , z)) (pelim2 (congS (λ z → node (`mult , z)) (pelim2 refl refl)) refl)
  ∙ sat `assoc (vec (m ∷ n ∷ o ∷ []))
  ∙ congS (λ z → node (`mult , z)) (pelim2 refl (congS (λ z → node (`mult , z)) (pelim2 refl refl)))

postulate
  TODO : ∀ {ℓ} (A : Type ℓ) → A

evalFreeMon : {A : Type} (𝔅 : Alg MonSig) → (𝔅 ⊨ MonSysEq) → (A → 𝔅 .car) → FreeMon A → 𝔅 .car
evalFreeMon 𝔅 s f (var x) = f x
evalFreeMon 𝔅 s f (node (o , g)) = 𝔅 .alg (o , λ y → evalFreeMon 𝔅 s f (g y))
evalFreeMon {A = A} 𝔅 s f (sat `assoc ρ i) = 
  {!!}
evalFreeMon {A = A} 𝔅 s f (sat `unitl ρ i) =
  hcomp (λ j → λ { (i = i0) → {!!} ; (i = i1) → s `unitl (λ _ → evalFreeMon 𝔅 s f (ρ zero)) j }) 
        (𝔅 .alg (`mult , {!!}))

  -- ( congS {x = λ y → evalFreeMon 𝔅 s f (indTree MonSig (MonEqSig .fv `unitl) {!!} {!!} {!!} {!!})} (λ z → 𝔅 .alg (`mult , z)) (funExt λ { zero → congS (λ z → 𝔅 .alg (`unit , z)) refl ; one → refl }) 
  -- ∙ s `unitl λ _ → evalFreeMon 𝔅 s f (ρ zero)
  -- ) i

-- i = i0 ⊢ 𝔅 .alg
--          (`mult ,
--           (λ y →
--              evalFreeMon 𝔅 s f
--              (indTree MonSig (MonEqSig .fv `unitl)
--               (λ _ → Free MonSig MonEqSig MonSysEq A) ρ
--               (λ { (o , g) r → node (o , r) })
--               (vec (node (`unit , vec []) ∷ var zero ∷ []) y))))
-- i = i1 ⊢ evalFreeMon 𝔅 s f (ρ zero)

  -- hcomp (λ j → λ { (i = i0) → 𝔅 .alg (`mult , {!!}) ; (i = i1) → evalFreeMon 𝔅 s f (ρ zero) }) 
  --       (s `unitl (λ _ → evalFreeMon 𝔅 s f (ρ zero)) i)

evalFreeMon {A = A} 𝔅 s f (sat `unitr ρ i) = 
  {!!}

  -- hcomp (λ j → λ { (i = i0) → {!!} ; (i = i1) → s `unitl (λ _ → evalFreeMon 𝔅 s f (ρ tt)) j }) 
  --       (𝔅 .alg (`mult , (funExt
  --                          (λ { (inl y) → congS (λ x → 𝔅 .alg (`unit , x)) (funExt λ ())
  --                             ; (inr y) → refl
  --                             }))
  --                         i))

-- -- funExt λ {(inl y) → congS (λ x → 𝔅 .alg (`unit , x)) (funExt λ ()) ; (inr y) → refl}) i

--    hcomp (λ j → λ { (i = i0) → 𝔅 .alg (`mult , λ y → (λ {(inl y) → congS (λ x → 𝔅 .alg (`unit , x)) (funExt λ ()) ; (inr y) → refl}) y (~ j)) -- 
--                     ; (i = i1) → evalFreeMon 𝔅 s f (ρ tt) }) 
--          (s `unitl (λ _ → evalFreeMon 𝔅 s f (ρ tt)) i)

--   -- (𝔅 .alg
--   --        (`mult ,
--   --         (λ y →
--   --            evalFreeMon 𝔅 s f
--   --            (indTree MonSig (MonEqSig .fv `unitl)
--   --             (λ _ → Free MonSig MonEqSig MonSysEq A) ρ
--   --             (λ { (o , g) r → node (o , r) })
--   --             (S.rec (λ z → node (`unit , (λ ()))) (λ _ → var tt) y))))

--   --  ≡⟨ {!!} ⟩ 
  
--   --  {!!}

--   --  ≡⟨ {!s `unitl (λ _ → evalFreeMon 𝔅 s f (ρ tt))!} ⟩ 
  
--   --    evalFreeMon 𝔅 s f (ρ tt)

--   --  ∎) i

--   -- (? ≡⟨  ⟩
--   --  ? ≡⟨  ⟩
--   --  ? ∎)

-- evalFreeMon 𝔅 s f (sat `unitr ρ i) = {!   !}


-- -- algHomNat

-- test : ∀ {A : Type} (a b c : A) → (p : a ≡ b) → (q : b ≡ c) → a ≡ c
-- test a b c p q i = 
--   hcomp (λ j → λ { (i = i0) → a ; (i = i1) → q j })
--         (p i)

-- test2 : ∀ {A : Type} (a b c : A) → (p : a ≡ b) → (q : b ≡ c) → a ≡ c
-- test2 a b c p q i = 
--   hcomp (λ j → λ { (i = i0) → p (~ j) ; (i = i1) → c })
--         (q i)
