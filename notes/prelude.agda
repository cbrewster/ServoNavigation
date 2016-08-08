module prelude where

Subset : Set → Set₁
Subset(X) = X → Set

_∈_ : ∀ {X} → X → Subset(X) → Set
(x ∈ A) = A(x)

_⊆_ : ∀ {X} → Subset(X) → Subset(X) → Set
(A ⊆ B) = ∀ x → (x ∈ A) → (x ∈ B)

record Inhabited {X} (S : Subset(X)) : Set where
  constructor _,_
  field witness : X
  field witness-in : (witness ∈ S)
  
Rel : Set → Set₁
Rel(X) = X → X → Set

data ℕ : Set where
  zero : ℕ
  succ : ℕ → ℕ

data ℤ : Set where
  succ : ℕ → ℤ
  -ve : ℕ → ℤ

sucz : ℤ → ℤ
sucz (succ x) = succ (succ x)
sucz (-ve zero) = succ zero
sucz (-ve (succ x)) = -ve x

pred : ℤ → ℤ
pred (succ zero) = -ve zero
pred (succ (succ x)) = succ x
pred (-ve x) = -ve (succ x)

_+_ : ℤ → ℤ → ℤ
succ zero + y = sucz y
succ (succ x) + y = sucz (succ x + y)
-ve zero + y = y
-ve (succ x) + y = pred (-ve x + y)

data _^_ (X : Set) : ℕ → Set where
  nil : (X ^ zero)
  _∷_ : ∀ {n} → X → (X ^ n) → (X ^ succ(n))

data _≡_ {D : Set} (d : D) : D → Set where
  refl : (d ≡ d)

sym : ∀ {D} {d e : D} → (d ≡ e) → (e ≡ d)
sym refl = refl

trans : ∀ {D} {d e f : D} → (d ≡ e) → (e ≡ f) → (d ≡ f)
trans refl refl = refl

record ⊤ : Set where
  constructor tt

data ⊥ : Set where

¬ : Set → Set
¬(X) = (X → ⊥)

contradiction : ∀ {X : Set} → ⊥ → X
contradiction ()

data _∨_ (X Y : Set) : Set where
  in₁ : X → (X ∨ Y)
  in₂ : Y → (X ∨ Y)

_∪_ : ∀ {X} → Subset(X) → Subset(X) → Subset(X)
(A ∪ B) x = (x ∈ A) ∨ (x ∈ B)

record _∧_ (X Y : Set) : Set where
  constructor _,_
  field proj₁ : X
  field proj₂ : Y
  
_∩_ : ∀ {X} → Subset(X) → Subset(X) → Subset(X)
(A ∩ B) x = (x ∈ A) ∧ (x ∈ B)

All : ∀ {X n} → Subset(X) → Subset(X ^ n)
All(S) nil = ⊤
All(S) (x ∷ xs) = (x ∈ S) ∧ (xs ∈ All(S))

All-resp-⊆ : ∀ {X} {A B : Subset(X)} {n} → (A ⊆ B) → (All {n = n} (A) ⊆ All(B))
All-resp-⊆ A⊆B nil tt = tt
All-resp-⊆ A⊆B (x ∷ xs) (x∈A , xs∈A) = (A⊆B x x∈A , All-resp-⊆ A⊆B xs xs∈A)

All-resp-∩ : ∀ {X} {A B : Subset(X)} {n} → ((All {n = n} (A) ∩ All(B)) ⊆ All(A ∩ B))
All-resp-∩ nil (tt , tt) = tt
All-resp-∩ (d ∷ ds) ((d∈A , ds∈A) , (d∈B , ds∈B)) = ((d∈A , d∈B) , (All-resp-∩ ds (ds∈A , ds∈B)))

record DirectedGraph(D : Set) : Set₁ where

  field _⇒_ : Rel(D)

  data _⇒+_ (d e : D) : Set where
    ⇒-impl-⇒+ : (d ⇒ e) → (d ⇒+ e)
    ⇒⇒+-impl-⇒+ : ∀ {f} → (d ⇒ f) → (f ⇒+ e) → (d ⇒+ e)

record Forest(D : Set) : Set₁ where

  field DG : DirectedGraph(D)
  open DirectedGraph DG public

  field ⇒-parent-uniq : ∀ {d e f} → (d ⇒ f) → (e ⇒ f) → (d ≡ e)
  field ⇒-acyclic : ∀ {d} → (d ⇒+ d) → ⊥
  
record PartialOrder(D : Set) : Set₁ where

  field _≤_ : Rel(D)
  field ≤-refl : ∀ {d} → (d ≤ d)
  field ≤-trans : ∀ {d e f} → (d ≤ e) → (e ≤ f) → (d ≤ f)
  field ≤-asym : ∀ {d e} → (d ≤ e) → (e ≤ d) → (d ≡ e)

  field _≤?_ : ∀ d e → ((d ≤ e) ∨ ¬(d ≤ e))
  
  _<_ : Rel(D)
  d < e = (d ≤ e) ∧ ¬(d ≡ e)

  ≡-impl-≤ : ∀ {d e} → (d ≡ e) → (d ≤ e)
  ≡-impl-≤ refl = ≤-refl

  <-trans-≤ : ∀ {d e f} → (d < e) → (e ≤ f) → (d < f)
  <-trans-≤ (d≤e , d≠e) e≤f = (≤-trans d≤e e≤f , (λ d≡f → d≠e (trans d≡f (≤-asym (≤-trans (≡-impl-≤ (sym d≡f)) d≤e) e≤f))))

  <-trans : ∀ {d e f} → (d < e) → (e < f) → (d < f)
  <-trans d<e (e≤f , e≠f) = <-trans-≤ d<e e≤f

  <-impl-≤ : ∀ {d e} → (d < e) → (d ≤ e)
  <-impl-≤ (d≤e , d≠e) = d≤e
  
  <-impl-≱ : ∀ {d e} → (d < e) → ¬(e ≤ d)
  <-impl-≱ (d≤e , d≠e) e≤d = d≠e (≤-asym d≤e e≤d)
  
  Past : D → Subset(D)
  Past(d) e = (e < d)

  Decreasing : ∀ {n} → Subset(D ^ n)
  Decreasing nil = ⊤
  Decreasing (d ∷ ds) = (ds ∈ (All(Past(d)) ∩  Decreasing))

  _≤*_ : ∀ {n} → Rel(D ^ n)
  nil ≤* nil = ⊤
  (d ∷ ds) ≤* (e ∷ es) = (d ≤ e) ∧ (ds ≤* es)

  Min : Subset(D) → Subset(D)
  Min(S) d = (d ∈ S) ∧ (∀ e → (e ∈ S) → (d ≤ e))

  Max : Subset(D) → Subset(D)
  Max(S) d = (d ∈ S) ∧ (∀ e → (e ∈ S) → (e ≤ d))

  Min* : ∀ {n} → Subset(D ^ n) → Subset(D ^ n)
  Min*(S) ds = (ds ∈ S) ∧ (∀ es → (es ∈ S) → (ds ≤* es))

  Max* : ∀ {n} → Subset(D ^ n) → Subset(D ^ n)
  Max*(S) ds = (ds ∈ S) ∧ (∀ es → (es ∈ S) → (es ≤* ds))

record FiniteTotalOrder(D : Set) : Set₁ where

  field PO : PartialOrder(D)
  open PartialOrder PO public

  field min_∵_ : ∀ (S : Subset(D)) → Inhabited(S) → Inhabited(Min(S))
  field max_∵_ : ∀ (S : Subset(D)) → Inhabited(S) → Inhabited(Max(S))

  ≤-total : ∀ d e → (d ≤ e) ∨ (e < d)
  ≤-total d e with d ≤? e
  ≤-total d e | in₁ d≤e = in₁ d≤e
  ≤-total d e | in₂ d≰e with max (λ f → (d ≡ f) ∨ (e ≡ f)) ∵ (d , in₁ refl)
  ≤-total d e | in₂ d≰e | .d , (in₁ refl , d-max) = in₂ (e≤d , e≠d) where

    e≤d = d-max e (in₂ refl)
    e≠d = λ e=d → d≰e (≡-impl-≤ (sym e=d))
    
  ≤-total d e | in₂ d≰e | .e , (in₂ refl , e-max) = contradiction (d≰e (e-max d (in₁ refl)))
  
  Max-hd : ∀ S {n} d (ds : D ^ n) →
    ((d ∷ ds) ∈ Max*(Decreasing ∩ All(S))) →
    (d ∈ Max(S))
  Max-hd S d ds (((d>ds , ds↓) , (d∈S , ds∈S)) , d∷ds-max) = (d∈S , d-max) where

    d-max : ∀ e → (e ∈ S) → (e ≤ d)
    d-max e e∈S with ≤-total e d
    d-max e e∈S | in₁ e≤d = e≤d
    d-max e e∈S | in₂ d<e with d∷ds-max (e ∷ ds) ((All-resp-⊆ (λ f d<f → <-trans d<f d<e) ds d>ds , ds↓) , (e∈S , ds∈S))
    d-max e e∈S | in₂ d<e | (e≤d , ds≤ds) = e≤d

  Max-tl : ∀ S {n} d (ds : D ^ n) →
    ((d ∷ ds) ∈ Max*(Decreasing ∩ All(S))) →
    (ds ∈ Max*(All(Past(d)) ∩ (Decreasing ∩ All(S))))
  Max-tl S d ds (((d>ds , ds↓) , (d∈S , ds∈S)) , d∷ds-max) = ((d>ds , (ds↓ , ds∈S)) , ds-max) where

    ds-max : ∀ es → (es ∈ (All(Past(d)) ∩ (Decreasing ∩ All(S)))) → (es ≤* ds)
    ds-max es (d>es , (es↓ , es∈S)) with d∷ds-max (d ∷ es) ((d>es , es↓) , (d∈S , es∈S)) 
    ds-max es (d>es , (es↓ , es∈S)) | (d≤d , es≤ds) = es≤ds
  
record Equivalence(D : Set) : Set₁ where

  field _~_ : Rel(D)
  field ~-refl : ∀ {d} → (d ~ d)
  field ~-trans : ∀ {d e f} → (d ~ e) → (e ~ f) → (d ~ f)
  field ~-sym : ∀ {d e} → (d ~ e) → (e ~ d)

  field _~?_ : ∀ d e → ((d ~ e) ∨ ¬(d ~ e))

  ≡-impl-~ : ∀ {d e} → (d ≡ e) → (d ~ e)
  ≡-impl-~ refl = ~-refl
