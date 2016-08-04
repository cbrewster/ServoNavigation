module notes where

Subset : Set → Set₁
Subset(X) = X → Set

_∈_ : ∀ {X} → X → Subset(X) → Set
(x ∈ A) = A(x)

Rel : Set → Set₁
Rel(X) = X → X → Set

data ℕ : Set where
  zero : ℕ
  succ : ℕ → ℕ

_+_ : ℕ → ℕ → ℕ
(zero + n) = n
(succ m + n) = succ(m + n)

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

record _∧_ (X Y : Set) : Set where
  constructor _,_
  field proj₁ : X
  field proj₂ : Y
  
⟦_⟧ : ∀ {X n} → (X ^ n) → Subset(X)
⟦ nil    ⟧ y = ⊥
⟦ x ∷ xs ⟧ y = (x ≡ y) ∨ (⟦ xs ⟧ y)

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
  
record TotalOrder(D : Set) : Set₁ where

  field _≤_ : Rel(D)
  field ≤-refl : ∀ {d} → (d ≤ d)
  field ≤-trans : ∀ {d e f} → (d ≤ e) → (e ≤ f) → (d ≤ f)
  field ≤-asym : ∀ {d e} → (d ≤ e) → (e ≤ d) → (d ≡ e)
  field ≤-total : ∀ {d e} → (d ≤ e) ∨ ((e ≤ d) ∧ ¬(e ≡ d))

  _<_ : Rel(D)
  d < e = (d ≤ e) ∧ ¬(d ≡ e)

  <-impl-≤ : ∀ d e → (d < e) → (d ≤ e)
  <-impl-≤ d e (d≤e , d≠e) = d≤e
  
  <-impl-≠ : ∀ d e → (d < e) → ¬(d ≡ e)
  <-impl-≠ d e (d≤e , d≠e) = d≠e

  ≡-impl-≤ : ∀ {d e} → (d ≡ e) → (d ≤ e)
  ≡-impl-≤ refl = ≤-refl

  <-trans-≤ : ∀ {d e f} → (d < e) → (e ≤ f) → (d < f)
  <-trans-≤ (d≤e , d≠e) e≤f = (≤-trans d≤e e≤f , (λ d≡f → d≠e (trans d≡f (≤-asym (≤-trans (≡-impl-≤ (sym d≡f)) d≤e) e≤f))))
  
record Equivalence(D : Set) : Set₁ where

  field _~_ : Rel(D)
  field ~-refl : ∀ {d} → (d ~ d)
  field ~-trans : ∀ {d e f} → (d ~ e) → (e ~ f) → (d ~ f)
  field ~-sym : ∀ {d e} → (d ~ e) → (e ~ d)

  field _~?_ : ∀ d e → ((d ~ e) ∨ ¬(d ~ e))

  ≡-impl-~ : ∀ {d e} → (d ≡ e) → (d ~ e)
  ≡-impl-~ refl = ~-refl
  
record NavigationHistory(D : Set) : Set₁ where

  field A : Subset(D)
  field Fo : Forest(D)
  field TO : TotalOrder(D)
  field Eq : Equivalence(D)

  open TotalOrder TO public
  open Forest Fo public
  open Equivalence Eq public

  field active : D → D
  field active-A : ∀ d → A(active d)
  field active-~ : ∀ d → (active d ~ d)
  field active-uniq : ∀ d e → A(e) → (d ~ e) → (e ≡ active d)

  field ⇒-trans-~ : ∀ {d e f} → (d ⇒ e) → (e ~ f) → (d ⇒ f)

  field ⇒-impl-≤ : ∀ {d e} → (d ⇒ e) → (d ≤ e)
  
_traverse-to_ : ∀ {D} → NavigationHistory(D) → D → NavigationHistory(D)
H traverse-to d = H′ where

  D = _
  open NavigationHistory H

  A′ : Subset(D)
  A′(e) = (¬(d ~ e) ∧ A(e)) ∨ (d ≡ e)

  active′ : D → D
  active′ e with (d ~? e)
  active′ e | in₁ d~e = d
  active′ e | in₂ ¬d~e = active e

  active′-A′ :  ∀ d → A′(active′ d)
  active′-A′ e with (d ~? e)
  active′-A′ e | in₁ d~e = in₂ refl
  active′-A′ e | in₂ ¬d~e = in₁ ((λ d~ae → ¬d~e (~-trans d~ae (active-~ e))) , active-A e)

  active′-~ :  ∀ d → (active′ d ~ d)
  active′-~ e with (d ~? e)
  active′-~ e | in₁ d~e = d~e
  active′-~ e | in₂ ¬d~e = active-~ e

  active′-uniq : ∀ d e → A′ e → (d ~ e) → (e ≡ active′ d)
  active′-uniq e f (in₁ (¬d~f , f∈A)) e~f with (d ~? e)
  active′-uniq e f (in₁ (¬d~f , f∈A)) e~f | in₁ d~e = contradiction (¬d~f (~-trans d~e e~f))
  active′-uniq e f (in₁ (¬d~f , f∈A)) e~f | in₂ ¬d~e = active-uniq e f f∈A e~f
  active′-uniq e .d (in₂ refl) e~d with (d ~? e)
  active′-uniq e .d (in₂ refl) e~d | in₁ d~e = refl
  active′-uniq e .d (in₂ refl) e~d | in₂ ¬d~e = contradiction (¬d~e (~-sym e~d))
  
  H′ = record { A = A′ ; Fo = Fo ; TO = TO ; Eq = Eq
              ; active = active′ ; active-A = active′-A′ ; active-~ = active′-~ ; active-uniq = active′-uniq
              ; ⇒-trans-~ = ⇒-trans-~ ; ⇒-impl-≤ = ⇒-impl-≤ }

_traverses-to_ : ∀ {D n} → NavigationHistory(D) → (D ^ n) → NavigationHistory(D)
(H traverses-to nil) = H
(H traverses-to (d ∷ ds)) = (H traverse-to d) traverses-to ds

record JSF {D} (H : NavigationHistory(D)) (d : D) : Set where

  open NavigationHistory H
  
  field a : D
  field a∈A : (a ∈ A)
  field a<d : (a < d)
  field a~d : (a ~ d)

JSFs : ∀ {D} (H : NavigationHistory(D)) {n} → Subset(D ^ n)
JSFs(H) ds = ∀ d → (d ∈ ⟦ ds ⟧) → (d ∈ JSF(H))

JSF-Downclosed : ∀ {D} (H : NavigationHistory(D)) {n} → Subset(D ^ n)
JSF-Downclosed(H) ds = ∀ d e → (d ≤ e) → (d ∈ JSF(H)) → (e ∈ ⟦ ds ⟧) → (d ∈ ⟦ ds ⟧) where open NavigationHistory H

Sorted : ∀ {D n} → TotalOrder(D) → Subset(D ^ n)
Sorted(TO) nil = ⊤
Sorted(TO) (d ∷ ds) = (∀ e → (e ∈ ⟦ ds ⟧) → (d < e)) ∧ (ds ∈ Sorted(TO)) where open TotalOrder TO

record μJSF {D} (H : NavigationHistory(D)) (d : D) : Set where

  open NavigationHistory H
  
  field d∈JSF : (d ∈ JSF(H))
  field minimal : ∀ e → (e ∈ JSF(H)) → (d ≤ e)

record μJSFs {D} (H : NavigationHistory(D)) {n} (ds : D ^ n) : Set where

  open NavigationHistory H

  field ds∈JSF : ds ∈ JSFs(H)
  field ds∈JSF↓ : ds ∈ JSF-Downclosed(H)
  field ds∈Sorted : ds ∈ Sorted(TO)

data _traverses-fwd-by_to_ {D} (H : NavigationHistory(D)) (δ : ℕ) : NavigationHistory(D) → Set where
  μjsf : ∀ (ds : D ^ δ) → (ds ∈ μJSFs(H)) → (H traverses-fwd-by δ to (H traverses-to ds))

JSF-refl-traverse : ∀ {D} (H : NavigationHistory(D)) d e →
  (d ∈ JSF(H)) →
  (e ∈ JSF(H traverse-to d)) →
  (e ∈ JSF(H))
JSF-refl-traverse {D} H d e d∈JSF e∈JSF′ = record { a = c ; a∈A = c∈A ; a<d = c<e ; a~d = c~e } where

  open NavigationHistory H
  open JSF d∈JSF
  open JSF e∈JSF′ using () renaming (a to b ; a∈A to b∈A′ ; a<d to b<e ; a~d to b~e)

  c : D
  c with b∈A′
  c | in₁ _ = b
  c | in₂ _ = a
  
  c∈A : (c ∈ A)
  c∈A with b∈A′
  c∈A | in₁ (_ , b∈A) = b∈A
  c∈A | in₂ _ = a∈A

  c<e : (c < e)
  c<e with b∈A′
  c<e | in₁ _ = b<e
  c<e | in₂ d≡b = <-trans-≤ a<d (≤-trans (≡-impl-≤ d≡b) (<-impl-≤ b e b<e)) 
 
  c~e : (c ~ e)
  c~e with b∈A′
  c~e | in₁ _ = b~e
  c~e | in₂ d≡b = ~-trans (~-trans a~d (≡-impl-~ d≡b)) b~e 
  
JSF-resp-traverse : ∀ {D} (H : NavigationHistory(D)) d e →
  let open NavigationHistory H in
  (d < e) →
  (d ∈ JSF(H)) →
  (e ∈ JSF(H)) →
  (e ∈ JSF(H traverse-to d))
JSF-resp-traverse {D} H d e d<e d∈JSF e∈JSF = record { a = c ; a∈A = c∈A′ ; a<d = c<e ; a~d = c~e } where

  open NavigationHistory H
  open NavigationHistory (H traverse-to d) using () renaming (A to A′)
  open JSF d∈JSF
  open JSF e∈JSF using () renaming (a to b ; a∈A to b∈A ; a<d to b<e ; a~d to b~e)

  c : D
  c with d ~? e
  c | in₁ _ = d
  c | in₂ _ = b

  c∈A′ : (c ∈ A′)
  c∈A′ with d ~? e
  c∈A′ | in₁ _ = in₂ refl
  c∈A′ | in₂ d≁e = in₁ ((λ d~b → d≁e (~-trans d~b b~e)) , b∈A)

  c<e : (c < e)
  c<e with d ~? e
  c<e | in₁ _ = d<e
  c<e | in₂ _ = b<e

  c~e : (c ~ e)
  c~e with d ~? e
  c~e | in₁ d~e = d~e
  c~e | in₂ _ = b~e

JSF-traverse-∉ : ∀ {D} (H : NavigationHistory(D)) d e →
  (e ∈ JSF(H traverse-to d)) →
  ¬(d ≡ e)
JSF-traverse-∉ H d .d d∈JSF′ refl = wrong where

  open NavigationHistory H
  open JSF d∈JSF′ renaming (a∈A to a∈A′)

  wrong : ⊥
  wrong with a∈A′
  wrong | in₁ (d≁a , a∈A) = d≁a (~-sym a~d)
  wrong | in₂ d≡a = <-impl-≠ a d a<d (sym d≡a)

μJSFs-head : ∀ {D} (H : NavigationHistory(D)) {n} d (ds : D ^ n) →
  ((d ∷ ds) ∈ μJSFs(H)) →
  (d ∈ μJSF(H))
μJSFs-head H d ds d∷ds∈μJSF = record { d∈JSF = d∷ds∈JSF d (in₁ refl) ; minimal = minimal } where

  open NavigationHistory H
  open μJSFs d∷ds∈μJSF using () renaming ( ds∈JSF to d∷ds∈JSF ; ds∈Sorted to d∷ds∈Sorted ; ds∈JSF↓ to d∷ds∈JSF↓ )

  minimal : ∀ e → (e ∈ JSF(H)) → (d ≤ e)
  minimal e e∈JSF with ≤-total
  minimal e e∈JSF | in₁ d≤e = d≤e
  minimal e e∈JSF | in₂ e<d with d∷ds∈JSF↓ e d (<-impl-≤ e d e<d) e∈JSF (in₁ refl)
  minimal .d d∈JSF | in₂ d<d | in₁ refl = contradiction (<-impl-≠ d d d<d refl)
  minimal e e∈JSF | in₂ e<d | in₂ e∈ds with d∷ds∈Sorted
  minimal e e∈JSF | in₂ e<d | in₂ e∈ds | (d-min , _) = <-impl-≤ d e (d-min e e∈ds)
  
μJSFs-tail : ∀ {D} (H : NavigationHistory(D)) {n} d (ds : D ^ n) →
  ((d ∷ ds) ∈ μJSFs(H)) →
  (ds ∈ μJSFs(H traverse-to d))
μJSFs-tail H d ds d∷ds∈μJSF = record { ds∈JSF = ds∈JSF′ ; ds∈JSF↓ = ds∈JSF′↓ ; ds∈Sorted = ds∈Sorted } where

  open NavigationHistory H
  open μJSF (μJSFs-head H d ds d∷ds∈μJSF)
  open μJSFs d∷ds∈μJSF using () renaming ( ds∈JSF to d∷ds∈JSF ; ds∈Sorted to d∷ds∈Sorted ; ds∈JSF↓ to d∷ds∈JSF↓ )
  
  H′ = (H traverse-to d)
  
  ds∈JSF′ : (ds ∈ JSFs(H′))
  ds∈JSF′ e e∈ds with d∷ds∈Sorted
  ds∈JSF′ e e∈ds | (d-min , _) = JSF-resp-traverse H d e (d-min e e∈ds) (d∷ds∈JSF d (in₁ refl)) (d∷ds∈JSF e (in₂ e∈ds))

  ds∈JSF′↓ : (ds ∈ JSF-Downclosed(H′))
  ds∈JSF′↓ e f e≤f e∈JSF′ f∈ds with d∷ds∈JSF↓ e f e≤f (JSF-refl-traverse H d e (d∷ds∈JSF d (in₁ refl)) e∈JSF′) (in₂ f∈ds)
  ds∈JSF′↓ e f d≤f d∈JSF′ f∈ds | in₁ d≡e = contradiction (JSF-traverse-∉ H d e d∈JSF′ d≡e)
  ds∈JSF′↓ e f e≤f e∈JSF′ f∈ds | in₂ e∈ds = e∈ds

  ds∈Sorted : (ds ∈ Sorted(TO))
  ds∈Sorted with d∷ds∈Sorted
  ds∈Sorted | (_ , ds∈Sorted) = ds∈Sorted

μJSFs-cons : ∀ {D} (H : NavigationHistory(D)) {n} d (ds : D ^ n) →
  (d ∈ μJSF(H)) →
  (ds ∈ μJSFs(H traverse-to d)) →
  ((d ∷ ds) ∈ μJSFs(H))
μJSFs-cons {D} H d ds d∈μJSF ds∈μJSF = record { ds∈JSF = d∷ds∈JSF ; ds∈JSF↓ = d∷ds∈JSF↓ ; ds∈Sorted = d∷ds∈Sorted } where

  open NavigationHistory H
  open μJSF d∈μJSF
  open μJSFs ds∈μJSF

  d∷ds∈JSF : (d ∷ ds) ∈ JSFs(H)
  d∷ds∈JSF .d (in₁ refl) = d∈JSF
  d∷ds∈JSF e (in₂ e∈ds) = JSF-refl-traverse H d e d∈JSF (ds∈JSF e e∈ds)

  d∷ds∈JSF↓ : (d ∷ ds) ∈ JSF-Downclosed(H)
  d∷ds∈JSF↓ e .d e≤d e∈JSF (in₁ refl) = in₁ (≤-asym (minimal e e∈JSF) e≤d)
  d∷ds∈JSF↓ e f e≤f e∈JSF (in₂ f∈ds) with ≤-total
  d∷ds∈JSF↓ e f e≤f e∈JSF (in₂ f∈ds) | in₁ e≤d = in₁ (≤-asym (minimal e e∈JSF) e≤d)
  d∷ds∈JSF↓ e f e≤f e∈JSF (in₂ f∈ds) | in₂ d<e = in₂ (ds∈JSF↓ e f e≤f (JSF-resp-traverse H d e d<e d∈JSF e∈JSF) f∈ds)
  
  d∷ds∈Sorted : (d ∷ ds) ∈ Sorted(TO)
  d∷ds∈Sorted = ((λ e e∈ds → (minimal e (JSF-refl-traverse H d e d∈JSF (ds∈JSF e e∈ds)) , JSF-traverse-∉ H d e (ds∈JSF e e∈ds))) , ds∈Sorted)

Theorem : ∀ {D} {H H′ H″ : NavigationHistory(D)} {δ δ′ : ℕ} →
  (H traverses-fwd-by δ to H′) →
  (H′ traverses-fwd-by δ′ to H″) →
  (H traverses-fwd-by (δ + δ′) to H″)
Theorem {D} (μjsf ds ds∈μJSF) = Lemma ds ds∈μJSF where

  Lemma : ∀ {H δ δ′ H″} (ds : D ^ δ) →
    (ds ∈ μJSFs(H)) → 
    ((H traverses-to ds) traverses-fwd-by δ′ to H″) →
    (H traverses-fwd-by (δ + δ′) to H″)
  Lemma nil _ H′-to-H″ = H′-to-H″
  Lemma (d ∷ ds) d∷ds∈μJSF H′-to-H″ with Lemma ds (μJSFs-tail _ d ds d∷ds∈μJSF) H′-to-H″
  Lemma (d ∷ ds) d∷ds∈μJSF H′-to-H″ | μjsf ds′ ds′∈μJSF′ = μjsf (d ∷ ds′) (μJSFs-cons _ d ds′ (μJSFs-head _ d ds d∷ds∈μJSF) ds′∈μJSF′)
