module lemmas where

open import prelude
open import defns

BT-hd : ∀ {D} {H : NavigationHistory(D)} {n} d (ds : D ^ n) →
  ((d ∷ ds) ∈ BackTarget*(H)) →
  (d ∈ BackTarget(H))
BT-hd {D} {H} {n} d ds d∷ds∈BT with Max-hd ((A ∪ JointSessionPast) ∩ CanGoBack) d ds d∷ds∈BT where open NavigationHistory H
BT-hd {D} {H} {n} d ds d∷ds∈BT | ((in₁ d∈A , d∈CGB), d-max′) = ((d∈A , d∈CGB) , d-max) where

  open NavigationHistory H

  d-max : ∀ e → (e ∈ (A ∩ CanGoBack) → (e ≤ d))
  d-max e (e∈A , e∈CGB) = d-max′ e ((in₁ e∈A) , e∈CGB)

BT-hd {D} {H} {n} d ds d∷ds∈BT | ((in₂ (a , (a∈A , (d<a , d~a))) , d∈CGB), d-max) = contradiction (<-impl-≱ d<a (d-max a ((in₁ a∈A) , (d , (d<a , d~a))))) where open NavigationHistory H

BT-tl : ∀ {D} {H : NavigationHistory(D)} {n} d d∈CGB (ds : D ^ n) →
  ((d ∷ ds) ∈ BackTarget*(H)) →
  (ds ∈ BackTarget*(H traverse-from d ∵ d∈CGB))
BT-tl {D} {H} {n} d d∈CGB ds d∷ds∈BT with Max-tl ((A ∪ JointSessionPast) ∩ CanGoBack) d ds d∷ds∈BT where open NavigationHistory H
BT-tl {D} {H} {n} d d∈CGB ds d∷ds∈BT | ((d>ds , (ds↓ , ds∈BT′)) , ds-max′) with max(SessionPast(d)) ∵ d∈CGB where open NavigationHistory H 
BT-tl {D} {H} {n} d d∈CGB ds d∷ds∈BT | ((d>ds , (ds↓ , ds∈BT′)) , ds-max′) | (c , ((c<d , c~d) , c-max)) = ((ds↓ , ds∈BT) , ds-max) where

  open NavigationHistory H
  open NavigationHistory (H traverse-to c) using () renaming (A to A′ ; JointSessionPast to JointSessionPast′)

  d∈A : (d ∈ A)
  d∈A with BT-hd {H = H} d ds d∷ds∈BT
  d∈A | ((d∈A , _) , _) = d∈A

  d-max : ∀ e → (e ∈ (A ∩ CanGoBack) → (e ≤ d))
  d-max with BT-hd {H = H} d ds d∷ds∈BT
  d-max | ((_ , _) , d-max) = d-max

  lemma : (Past(d) ∩ ((A ∪ JointSessionPast) ∩ CanGoBack)) ⊆ ((A′ ∪ JointSessionPast′) ∩ CanGoBack)
  lemma e  (e<d , (_                              , e∈CGB)) with c ~? e
  lemma e  (e<d , (_                              , e∈CGB)) | in₁ c~e with ≤-total c e
  lemma e  (e<d , (_                              , e∈CGB)) | in₁ c~e | in₁ c≤e with ≤-asym c≤e (c-max e (e<d , ~-trans (~-sym c~e) c~d))
  lemma ._ (e<d , (_                              , e∈CGB)) | in₁ c~e | in₁ c≤e | refl = ((in₁ (in₂ refl)) , e∈CGB)
  lemma e  (e<d , (_                              , e∈CGB)) | in₁ c~e | in₂ e<c = (in₂ (_ , (in₂ refl , (e<c , ~-sym c~e))) , e∈CGB)
  lemma e  (e<d , (in₁ e∈A                        , e∈CGB)) | in₂ c≁e = ((in₁ (in₁ (c≁e , e∈A))) , e∈CGB)
  lemma e  (e<d , (in₂ (a , (a∈A ,  (e<a , e~a))) , e∈CGB)) | in₂ c≁e = (in₂ (a , (in₁ ((λ c~a → c≁e (~-trans c~a (~-sym e~a))) , a∈A) , (e<a , e~a))) , e∈CGB)
  
  lemma′ : ((A′ ∪ JointSessionPast′) ∩ CanGoBack) ⊆ ((A ∪ JointSessionPast) ∩ CanGoBack)
  lemma′ e  (in₁ (in₁ (c≁e , e∈A)) , e∈CGB) = ((in₁ e∈A) , e∈CGB)
  lemma′ ._ (in₁ (in₂ refl) , c∈CGB) = ((in₂ (d , (d∈A , (c<d , c~d)))) , c∈CGB)
  lemma′ e (in₂ (a , (in₁ (c≁a , a∈A) , e≲a)) , e∈CGB) = (in₂ (a , (a∈A , e≲a)) , e∈CGB)
  lemma′ e (in₂ (._ , (in₂ refl , e≲c)) , e∈CGB) = ((in₂ (d , (d∈A , ≲-trans e≲c (c<d , c~d)))) , e∈CGB)
  
  lemma″ : ((A′ ∪ JointSessionPast′) ∩ CanGoBack) ⊆ (Past(d))
  lemma″ e  (in₁ (in₁ (c≁e , e∈A)) , e∈CGB) = (d-max e (e∈A , e∈CGB) , (λ e≡d → c≁e (~-trans c~d (≡-impl-~ (sym e≡d)))))
  lemma″ ._ (in₁ (in₂ refl) , c∈CGB) = c<d
  lemma″ e (in₂ (a , (in₁ (c≁a , a∈A) , e≲a)) , e∈CGB) = <-trans-≤ (≲-impl-< e≲a) (d-max a (a∈A , (e , e≲a)))
  lemma″ e (in₂ (._ , (in₂ refl , (e<c , e~c))) , e∈CGB) = <-trans e<c c<d
  
  ds∈BT : ds ∈ All((A′ ∪ JointSessionPast′) ∩ CanGoBack)
  ds∈BT = All-resp-⊆ lemma ds (All-resp-∩ ds (d>ds , ds∈BT′))
  
  ds-max : ∀ es → (es ∈ (Decreasing ∩ All((A′ ∪ JointSessionPast′) ∩ CanGoBack))) → (es ≤* ds)
  ds-max es (es↓ , es∈BT′) = ds-max′ es (All-resp-⊆ lemma″ es es∈BT′ , (es↓ , All-resp-⊆ lemma′ es es∈BT′))
  
BT-cons : ∀ {D} {H : NavigationHistory(D)} {n} d d∈CGB (ds : D ^ n) →
  (d ∈ BackTarget(H)) →
  (ds ∈ BackTarget*(H traverse-from d ∵ d∈CGB)) →
  ((d ∷ ds) ∈ BackTarget*(H))
BT-cons {D} {H} d d∈CGB ds ((d∈A , _) , d-max) ((ds↓ , ds∈JSP′∩CGB) , ds-max) with max(SessionPast(d)) ∵ d∈CGB where open NavigationHistory H
BT-cons {D} {H} d d∈CGB ds ((d∈A , _) , d-max) ((ds↓ , ds∈JSP′∩CGB) , ds-max) | (c , ((c<d , c~d) , c-max)) = (((d<ds , ds↓) , (((in₁ d∈A) , d∈CGB) , All-resp-⊆ lemma′ ds ds∈JSP′∩CGB)) , d∷ds-max) where

  open NavigationHistory H
  open NavigationHistory (H traverse-to c) using () renaming (A to A′ ; JointSessionPast to JointSessionPast′)
  

  lemma : (Past(d) ∩ ((A ∪ JointSessionPast) ∩ CanGoBack)) ⊆ ((A′ ∪ JointSessionPast′) ∩ CanGoBack)
  lemma e  (e<d , (_                              , e∈CGB)) with c ~? e
  lemma e  (e<d , (_                              , e∈CGB)) | in₁ c~e with ≤-total c e
  lemma e  (e<d , (_                              , e∈CGB)) | in₁ c~e | in₁ c≤e with ≤-asym c≤e (c-max e (e<d , ~-trans (~-sym c~e) c~d))
  lemma ._ (e<d , (_                              , e∈CGB)) | in₁ c~e | in₁ c≤e | refl = ((in₁ (in₂ refl)) , e∈CGB)
  lemma e  (e<d , (_                              , e∈CGB)) | in₁ c~e | in₂ e<c = (in₂ (_ , (in₂ refl , (e<c , ~-sym c~e))) , e∈CGB)
  lemma e  (e<d , (in₁ e∈A                        , e∈CGB)) | in₂ c≁e = ((in₁ (in₁ (c≁e , e∈A))) , e∈CGB)
  lemma e  (e<d , (in₂ (a , (a∈A ,  (e<a , e~a))) , e∈CGB)) | in₂ c≁e = (in₂ (a , (in₁ ((λ c~a → c≁e (~-trans c~a (~-sym e~a))) , a∈A) , (e<a , e~a))) , e∈CGB)
  
  lemma′ : ((A′ ∪ JointSessionPast′) ∩ CanGoBack) ⊆ ((A ∪ JointSessionPast) ∩ CanGoBack)
  lemma′ e  (in₁ (in₁ (c≁e , e∈A)) , e∈CGB) = ((in₁ e∈A) , e∈CGB)
  lemma′ ._ (in₁ (in₂ refl) , c∈CGB) = ((in₂ (d , (d∈A , (c<d , c~d)))) , c∈CGB)
  lemma′ e (in₂ (a , (in₁ (c≁a , a∈A) , e≲a)) , e∈CGB) = (in₂ (a , (a∈A , e≲a)) , e∈CGB)
  lemma′ e (in₂ (._ , (in₂ refl , e≲c)) , e∈CGB) = ((in₂ (d , (d∈A , ≲-trans e≲c (c<d , c~d)))) , e∈CGB)
  
  lemma″ : ((A′ ∪ JointSessionPast′) ∩ CanGoBack) ⊆ (Past(d))
  lemma″ e  (in₁ (in₁ (c≁e , e∈A)) , e∈CGB) = (d-max e (e∈A , e∈CGB) , (λ e≡d → c≁e (~-trans c~d (≡-impl-~ (sym e≡d)))))
  lemma″ ._ (in₁ (in₂ refl) , c∈CGB) = c<d
  lemma″ e (in₂ (a , (in₁ (c≁a , a∈A) , e≲a)) , e∈CGB) = <-trans-≤ (≲-impl-< e≲a) (d-max a (a∈A , (e , e≲a)))
  lemma″ e (in₂ (._ , (in₂ refl , (e<c , e~c))) , e∈CGB) = <-trans e<c c<d

  d<ds : (ds ∈ All(Past(d)))
  d<ds = All-resp-⊆ lemma″ ds ds∈JSP′∩CGB

  d∷ds-max : ∀ es → es ∈ (Decreasing ∩ All ((A ∪ JointSessionPast) ∩ CanGoBack)) → (es ≤* (d ∷ ds))
  d∷ds-max (e ∷ es) ((es<e , es↓) , ((e∈A∪JSP , e∈CGB) , es∈A∪JSP∩CGB)) = (e≤d , es≤ds) where

    lemma‴ : ∀ f → (f ∈ ((A ∪ JointSessionPast) ∩ CanGoBack)) → (f ≤ d)
    lemma‴ f (in₁ f∈A , f∈CGB) = d-max f (f∈A , f∈CGB)
    lemma‴ f (in₂ (a , (a∈A , ((f≤a , f≠a) , f~a))) , f∈CGB) = ≤-trans f≤a (d-max a (a∈A , (f , ((f≤a , f≠a) , f~a))))
    
    e≤d : (e ≤ d)
    e≤d = lemma‴ e (e∈A∪JSP , e∈CGB)
    
    es<d : es ∈ All(Past(d))
    es<d = All-resp-⊆ (λ f f<e → <-trans-≤ f<e e≤d) es es<e

    es≤ds : es ≤* ds
    es≤ds = ds-max es (es↓ , All-resp-⊆ lemma es (All-resp-∩ es (es<d , es∈A∪JSP∩CGB)))
