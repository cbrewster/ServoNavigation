module main where

open import prelude
open import defns
open import lemmas

data _≣_ {X : Set₁} (x : X) : X → Set₁ where
  REFL : (x ≣ x)

SUBST : ∀ {X L R} (P : X → Set) →
  (L ≣ R) →
  (P R) →
  (P L)
SUBST P REFL p = p

FT-hd : ∀ {D} {H : NavigationHistory(D)} {n} d (ds : D ^ n) →
  ((d ∷ ds) ∈ FwdTarget*(H)) →
  (d ∈ FwdTarget(H))
FT-hd = {! STILL TO DO !}

FT-tl : ∀ {D} {H : NavigationHistory(D)} {n} d (ds : D ^ n) →
  ((d ∷ ds) ∈ FwdTarget*(H)) →
  (ds ∈ FwdTarget*(H traverse-to d))
FT-tl = {! STILL TO DO !}

postulate NH-CONG : ∀ {D} (H H′ : NavigationHistory(D)) → let open NavigationHistory H in let open NavigationHistory H′ using () renaming ( A to A′ ; Fo to Fo′ ; Eq to Eq′ ; FTO to FTO′ ) in (A ⊆ A′) → (A′ ⊆ A) → (Fo ≣ Fo′) → (Eq ≣ Eq′) → (FTO ≣ FTO′) → (H ≣ H′)
  
from-to : ∀ {D} {H : NavigationHistory(D)} d e d∈CGB →
  (d ∈ BackTarget(H)) →
  (e ∈ FwdTarget(H traverse-from d ∵ d∈CGB)) →
  (H ≣ ((H traverse-from d ∵ d∈CGB) traverse-to e))
from-to {D} {H} d e d∈CGB ((d∈A , _) , d-max) e∈FT′ with lemma e∈FT′ where

  H′ = (H traverse-from d ∵ d∈CGB)

  open NavigationHistory H
  open NavigationHistory H′ using () renaming (JointSessionFuture to JointSessionFuture′ ; FwdTarget to FwdTarget′)
   
  lemma : (e ∈ FwdTarget′) → (d ≡ e)
  lemma (e∈JSP′ , e-min) with max(SessionPast(d)) ∵ d∈CGB | ≤-total d e
  lemma (e∈JSP′ , e-min) | (c , ((c<d , c~d) , c-max)) | in₁ d≤e = ≤-asym d≤e (e-min d (c , (in₂ refl , (c<d , c~d))))
  lemma ((a  , (in₁ (c≁a , a∈A) , (a<e , a~e))) , e-min) | c , ((c<d , c~d) , c-max) | in₂ e<d = contradiction (<-impl-≱ e<d (PATCH a∈A d∈A a~e c~d a<e c<d))
  lemma ((.c , (in₂ refl , (c<e , c~e))) , e-min) | c , ((c<d , c~d) , c-max) | in₂ e<d = contradiction (<-impl-≱ c<e (c-max e (e<d , ~-trans (~-sym c~e) c~d)))
  
from-to {D} {H} d .d d∈CGB ((d∈A , _) , d-max) e∈FT′ | refl = H=H″ where

  H′ = (H traverse-from d ∵ d∈CGB)
  H″ = (H′ traverse-to d)
  
  open NavigationHistory H
  open NavigationHistory H″ using () renaming (A to A″)

  A⊆A″ : (A ⊆ A″)
  A⊆A″ f f∈A with d ~? f
  A⊆A″ f f∈A | in₁ d~f with trans (active-uniq d f f∈A d~f) (sym (active-uniq d d d∈A ~-refl))
  A⊆A″ .d  _ | in₁ d~f | refl = in₂ refl
  A⊆A″ f f∈A | in₂ d≁f with max(SessionPast(d)) ∵ d∈CGB
  A⊆A″ f f∈A | in₂ d≁f | (c , ((c<d , c~d) , c-max)) = in₁ (d≁f , (in₁ ((λ c~f → d≁f (~-trans (~-sym c~d) c~f)) , f∈A)))
  
  A″⊆A : (A″ ⊆ A)
  A″⊆A f (in₁ (d≁f , in₁ (c≁f , f∈A))) = f∈A
  A″⊆A ._ (in₁ (d≁c , in₂ refl)) with max(SessionPast(d)) ∵ d∈CGB
  A″⊆A ._ (in₁ (d≁c , in₂ refl)) | (c , ((c<d , c~d) , c-max)) = contradiction (d≁c (~-sym c~d))
  A″⊆A ._ (in₂ refl) = d∈A

  H=H″ : (H ≣ H″)
  H=H″ = NH-CONG H H″ A⊆A″ A″⊆A REFL REFL REFL

Theorem : ∀ {D} {H H′ H″ : NavigationHistory(D)} {δ δ′} →
  (H traverses-by (-ve δ) to H′) → 
  (H′ traverses-by δ′ to H″) → 
  (H traverses-by (-ve δ + δ′) to H″)
Theorem {δ = zero} (back nil ds∈CGB ds∈BT) H′-to-H″ = H′-to-H″
Theorem {D} {H} {._} {δ = succ δ} {δ′} (back (d ∷ ds) (d∈CGB , ds∈CGB) d∷ds∈BT) H′-to-H″ = Lemma (-ve δ + δ′) H₁-to-H″ where

  H₁ = (H traverse-from d ∵ d∈CGB)
  H′ = (H₁ traverses-from ds ∵ ds∈CGB)

  d∈BT : (d ∈ BackTarget(H))
  d∈BT = BT-hd {H = H} d ds d∷ds∈BT

  ds∈BT₁ : (ds ∈ BackTarget*(H₁))
  ds∈BT₁ = BT-tl {H = H} d d∈CGB ds d∷ds∈BT

  H₁-to-H″ = Theorem (back ds ds∈CGB ds∈BT₁) H′-to-H″
  
  Lemma : ∀ {H″} n →
    (H₁ traverses-by n to H″) →
    (H traverses-by pred n to H″)
  Lemma (succ zero) (fwd (e ∷ nil) e∷es∈FT₁) = H-to-H₀ where

    H₀ = (H₁ traverse-to e)

    e∈FT₁ : (e ∈ FwdTarget(H₁))
    e∈FT₁ = FT-hd {H = H₁} e nil e∷es∈FT₁

    H=H₀ : H ≣ H₀
    H=H₀ = from-to d e d∈CGB d∈BT e∈FT₁
    
    H₀-to-H₀ : (H₀ traverses-by (-ve zero) to H₀)
    H₀-to-H₀ = back nil tt (BT-nil {H = H₀})
    
    H-to-H₀ : H traverses-by (-ve zero) to H₀
    H-to-H₀ = SUBST (λ ∙ → ∙ traverses-by (-ve zero) to H₀) H=H₀ H₀-to-H₀

  Lemma (succ (succ n)) (fwd (e ∷ es) e∷es∈FT₁) = H-to-H″ where

    H₀ = (H₁ traverse-to e)
    H″ = (H₁ traverses-to (e ∷ es))

    e∈FT₁ : (e ∈ FwdTarget(H₁))
    e∈FT₁ = FT-hd {H = H₁} e es e∷es∈FT₁

    es∈FT₀ : (es ∈ FwdTarget*(H₀))
    es∈FT₀ = FT-tl {H = H₁} e es e∷es∈FT₁

    H=H₀ : H ≣ H₀
    H=H₀ = from-to d e d∈CGB d∈BT e∈FT₁
    
    H₀-to-H″ : H₀ traverses-by (succ n) to H″
    H₀-to-H″ = fwd es es∈FT₀
    
    H-to-H″ : H traverses-by (succ n) to H″
    H-to-H″ = SUBST (λ ∙ → ∙ traverses-by succ n to H″) H=H₀ H₀-to-H″
    
  Lemma (-ve n) (back es es∈CGB es∈BT₁) = back (d ∷ es) (d∈CGB , es∈CGB) (BT-cons {H = H} d d∈CGB es d∈BT es∈BT₁)
  
