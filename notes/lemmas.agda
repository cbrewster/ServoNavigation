module lemmas where

open import prelude
open import defns

postulate NH-CONG : ∀ {D} (H H′ : NavigationHistory(D)) → let open NavigationHistory H in let open NavigationHistory H′ using () renaming ( A to A′ ; Fo to Fo′ ; Eq to Eq′ ; FTO to FTO′ ) in (A ⊆ A′) → (A′ ⊆ A) → (Fo ≣ Fo′) → (Eq ≣ Eq′) → (FTO ≣ FTO′) → (H ≣ H′)

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

BT-nil :  ∀ {D} {H : NavigationHistory(D)} →
  (nil ∈ BackTarget*(H))
BT-nil = ((tt , tt) , λ { nil (tt , tt) → tt })

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

fwd? : ∀ {D} {H : NavigationHistory(D)} {δ} (ds : D ^ δ) →
  (ds ∈ FwdTarget*(H)) →
  (H traverses-by (+ve δ) to (H traverses-to ds))
fwd? {D} {H} {δ = zero} nil nil∈FT = back nil tt (BT-nil {H = H})
fwd? {D} {H} {δ = succ δ} ds ds∈FT = fwd ds ds∈FT

FT-hd : ∀ {D} {H : NavigationHistory(D)} {n} d (ds : D ^ n) →
  ((d ∷ ds) ∈ FwdTarget*(H)) →
  (d ∈ FwdTarget(H))
FT-hd {D} {H} d ds (((d<ds , ds↑) , (d∈JSF , ds∈JSF)) , d∷ds-min) = (d∈JSF , d-min) where

  open NavigationHistory H
  
  d-min : ∀ e → (e ∈ JointSessionFuture) → (d ≤ e)
  d-min e e∈JSF with ≤-total d e
  d-min e e∈JSF | in₁ d≤e = d≤e
  d-min e e∈JSF | in₂ e<d with d∷ds-min (e ∷ ds) (((All-resp-⊆ (λ f → <-trans e<d) ds d<ds) , ds↑) , (e∈JSF , ds∈JSF))
  d-min e e∈JSF | in₂ e<d | (d≤e , ds≤ds) = d≤e

FT-tl : ∀ {D} {H : NavigationHistory(D)} {n} d (ds : D ^ n) →
  ((d ∷ ds) ∈ FwdTarget*(H)) →
  (ds ∈ FwdTarget*(H traverse-to d))
FT-tl {D} {H} d ds (((d<ds , ds↑) , ((a , (a∈A , (a<d , a~d))) , ds∈JSF)) , d∷ds-min) = ((ds↑ , ds∈JSF′) , ds-min) where

  H′ = (H traverse-to d)

  open NavigationHistory H
  open NavigationHistory H′ using () renaming (JointSessionFuture to JointSessionFuture′)

  lemma : ((Future(d) ∩ JointSessionFuture) ⊆ JointSessionFuture′)
  lemma e (d<e , (b , (b∈A , (b<e , b~e)))) with d ~? b
  lemma e (d<e , (b , (b∈A , (b<e , b~e)))) | in₁ d~b = (d , (in₂ refl , (d<e , (~-trans d~b b~e))))
  lemma e (d<e , (b , (b∈A , (b<e , b~e)))) | in₂ d≁b = (b , (in₁ (d≁b , b∈A) , (b<e , b~e)))

  lemma′ : (JointSessionFuture′ ⊆ Future(d))
  lemma′ e (b  , (in₁ (d≁b , b∈A) , (b<e , b~e))) with ≤-total e d 
  lemma′ e (b  , (in₁ (d≁b , b∈A) , (b<e , b~e))) | in₁ e≤d with d∷ds-min (e ∷ ds) (((All-resp-⊆ (λ f → ≤-trans-< e≤d) ds d<ds) , ds↑) , ((b , (b∈A , (b<e , b~e))) , ds∈JSF))
  lemma′ e (b  , (in₁ (d≁b , b∈A) , (b<e , b~e))) | in₁ e≤d | (d≤e , ds≤ds) = contradiction (d≁b (~-trans (≡-impl-~ (≤-asym d≤e e≤d)) (~-sym b~e)))
  lemma′ e (b  , (in₁ (d≁b , b∈A) , (b<e , b~e))) | in₂ d<e = d<e
  lemma′ e (.d , (in₂ refl        , (d<e , d~e))) = d<e
  
  lemma″ : (JointSessionFuture′ ⊆ JointSessionFuture)
  lemma″ e (b  , (in₁ (d≁b , b∈A) , (b<e , b~e))) = (b , (b∈A , (b<e , b~e)))
  lemma″ e (.d , (in₂ refl        , (d<e , d~e))) = a , (a∈A , (<-trans a<d d<e , ~-trans a~d d~e))
 
  ds∈JSF′ : (ds ∈ All(JointSessionFuture′))
  ds∈JSF′ = All-resp-⊆ lemma ds (All-resp-∩ ds (d<ds , ds∈JSF))

  ds-min : ∀ es → (es ∈ (Increasing ∩ All(JointSessionFuture′))) → (ds ≤* es)
  ds-min es (es↑ , es∈JSF′) with d∷ds-min (d ∷ es) ((d<es , es↑) , ((a , (a∈A , (a<d , a~d))) , es∈JSF)) where

    d<es : es ∈ All(Future(d))
    d<es = All-resp-⊆ lemma′ es es∈JSF′

    es∈JSF : es ∈ All(JointSessionFuture)
    es∈JSF = All-resp-⊆ lemma″ es es∈JSF′
    
  ds-min es (es↑ , es∈JSF′) | (d≤d , ds≤es) = ds≤es
  
FT-nil :  ∀ {D} {H : NavigationHistory(D)} →
  (nil ∈ FwdTarget*(H))
FT-nil = ((tt , tt) , λ { nil (tt , tt) → tt })

FT-cons : ∀ {D} {H : NavigationHistory(D)} {n} d (ds : D ^ n) →
  (d ∈ FwdTarget(H)) →
  (ds ∈ FwdTarget*(H traverse-to d)) →
  ((d ∷ ds) ∈ FwdTarget*(H))
FT-cons {D} {H} d ds ((a , (a∈A , (a<d , a~d))) , d-min) ((ds↑ , ds∈JSF′) , ds-min) = (((d<ds , ds↑) , ((a , (a∈A , (a<d , a~d))) , ds∈JSF)) , d∷ds-min) where

  H′ = (H traverse-to d)

  open NavigationHistory H
  open NavigationHistory H′ using () renaming (JointSessionFuture to JointSessionFuture′)

  lemma : ((Future(d) ∩ JointSessionFuture) ⊆ JointSessionFuture′)
  lemma e (d<e , (b , (b∈A , (b<e , b~e)))) with d ~? b
  lemma e (d<e , (b , (b∈A , (b<e , b~e)))) | in₁ d~b = (d , (in₂ refl , (d<e , (~-trans d~b b~e))))
  lemma e (d<e , (b , (b∈A , (b<e , b~e)))) | in₂ d≁b = (b , (in₁ (d≁b , b∈A) , (b<e , b~e)))

  lemma′ : (JointSessionFuture′ ⊆ Future(d))
  lemma′ e (b  , (in₁ (d≁b , b∈A) , (b<e , b~e))) with ≤-total e d 
  lemma′ e (b  , (in₁ (d≁b , b∈A) , (b<e , b~e))) | in₁ e≤d with d-min e (b , (b∈A , (b<e , b~e)))
  lemma′ e (b  , (in₁ (d≁b , b∈A) , (b<e , b~e))) | in₁ e≤d | d≤e = contradiction (d≁b (~-trans (≡-impl-~ (≤-asym d≤e e≤d)) (~-sym b~e)))
  lemma′ e (b  , (in₁ (d≁b , b∈A) , (b<e , b~e))) | in₂ d<e = d<e
  lemma′ e (.d , (in₂ refl        , (d<e , d~e))) = d<e

  lemma″ : (JointSessionFuture′ ⊆ JointSessionFuture)
  lemma″ e (b  , (in₁ (d≁b , b∈A) , (b<e , b~e))) = (b , (b∈A , (b<e , b~e)))
  lemma″ e (.d , (in₂ refl        , (d<e , d~e))) = (a , (a∈A , (<-trans a<d d<e , ~-trans a~d d~e)))

  d<ds : ds ∈ All(Future(d))
  d<ds = All-resp-⊆ lemma′ ds ds∈JSF′

  ds∈JSF : ds ∈ All(JointSessionFuture)
  ds∈JSF = All-resp-⊆ lemma″ ds ds∈JSF′
  
  d∷ds-min : ∀ es → (es ∈ (Increasing ∩ All(JointSessionFuture))) → ((d ∷ ds) ≤* es)
  d∷ds-min (e ∷ es) ((e<es , es↑) , (e∈JSF , es∈JSF)) = (d≤e , ds≤es) where

    d≤e : (d ≤ e)
    d≤e = d-min e e∈JSF

    d<es : es ∈ All(Future(d))
    d<es = All-resp-⊆ (λ f → ≤-trans-< d≤e) es e<es
    
    es∈JSF′ : (es ∈ All(JointSessionFuture′))
    es∈JSF′ = All-resp-⊆ lemma es (All-resp-∩ es (d<es , es∈JSF))
    
    ds≤es : (ds ≤* es)
    ds≤es = ds-min es (es↑ , es∈JSF′)

    
from-to : ∀ {D} {H : NavigationHistory(D)} d e d∈CGB →
  (WellFormed(H)) →
  (d ∈ BackTarget(H)) →
  (e ∈ FwdTarget(H traverse-from d ∵ d∈CGB)) →
  (H ≣ ((H traverse-from d ∵ d∈CGB) traverse-to e))
from-to {D} {H} d e d∈CGB H∈WF ((d∈A , _) , d-max) e∈FT′ with lemma e∈FT′ where

  H′ = (H traverse-from d ∵ d∈CGB)

  open NavigationHistory H
  open NavigationHistory H′ using () renaming (JointSessionFuture to JointSessionFuture′ ; FwdTarget to FwdTarget′)
   
  lemma : (e ∈ FwdTarget′) → (d ≡ e)
  lemma (e∈JSP′ , e-min) with max(SessionPast(d)) ∵ d∈CGB | ≤-total d e
  lemma (e∈JSP′ , e-min) | (c , ((c<d , c~d) , c-max)) | in₁ d≤e = ≤-asym d≤e (e-min d (c , (in₂ refl , (c<d , c~d))))
  lemma ((a  , (in₁ (c≁a , a∈A) , (a<e , a~e))) , e-min) | c , ((c<d , c~d) , c-max) | in₂ e<d = contradiction (<-impl-≱ e<d (H∈WF (a<e , a~e) (c<d , c~d) a∈A d∈A))
  lemma ((.c , (in₂ refl , (c<e , c~e))) , e-min) | c , ((c<d , c~d) , c-max) | in₂ e<d = contradiction (<-impl-≱ c<e (c-max e (e<d , ~-trans (~-sym c~e) c~d)))
  
from-to {D} {H} d .d d∈CGB H∈WF ((d∈A , _) , d-max) e∈FT′ | refl = H=H″ where

  H′ = (H traverse-from d ∵ d∈CGB)
  H″ = (H′ traverse-to d)
  
  open NavigationHistory H
  open NavigationHistory H″ using () renaming (A to A″)

  A⊆A″ : (A ⊆ A″)
  A⊆A″ f f∈A with d ~? f
  A⊆A″ f f∈A | in₁ d~f with active-~-impl-≡ d∈A f∈A d~f
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


to-from : ∀ {D} {H : NavigationHistory(D)} d e e∈CGB →
  (WellFormed(H)) →
  (d ∈ FwdTarget(H)) →
  (e ∈ BackTarget(H traverse-to d)) →
  (H ≣ ((H traverse-to d) traverse-from e ∵ e∈CGB))
to-from {D} {H} d e e∈CGB H∈WF ((a , (a∈A , (a<d , a~d))) , d-min) e∈BT′ with lemma e∈BT′ | max(SessionPast(e)) ∵ e∈CGB where

  H′ = (H traverse-to d)

  open NavigationHistory H
  open NavigationHistory H′ using () renaming (BackTarget to BackTarget′)
   
  lemma : (e ∈ BackTarget′) → (d ≡ e)
  lemma ((in₁ (d≁e , e∈A) , (b , (b<e , b~e))) , e-max) = ≤-asym d≤e e≤d where

    d≤e : (d ≤ e)
    d≤e = e-max d (in₂ refl , (a , (a<d , a~d)))

    e≤d : (e ≤ d)
    e≤d = H∈WF (a<d , a~d) (b<e , b~e) a∈A e∈A 
    
  lemma ((in₂ d≡e , _) , _) = d≡e

to-from {D} {H} d .d d∈CGB H∈WF ((a , (a∈A , (a<d , a~d))) , d-min) (_ , d-max) | refl | (c , ((c<d , c~d) , c-max)) with ≤-asym a≤c c≤a where

  open NavigationHistory H

  c≤a : (c ≤ a)
  c≤a with ≤-total c a
  c≤a | in₁ c≤a = c≤a
  c≤a | in₂ a<c = contradiction (<-impl-≱ (<-trans-≤ c<d (d-min c (a , (a∈A , (a<c , (~-trans a~d (~-sym c~d))))))) ≤-refl)
  
  a≤c : (a ≤ c)
  a≤c = c-max a (a<d , a~d)

to-from {D} {H} d .d d∈CGB H∈WF ((a , (a∈A , (a<d , a~d))) , d-min) (_ , d-max) | refl | (.a , ((_ , _) , a-max)) | refl = H=H″ where

  H′ = (H traverse-to d)
  H″ = (H′ traverse-to a)
  
  open NavigationHistory H
  open NavigationHistory H″ using () renaming (A to A″)

  A⊆A″ : (A ⊆ A″)
  A⊆A″ f f∈A with a ~? f
  A⊆A″ f f∈A | in₁ a~f = in₂ (active-~-impl-≡ a∈A f∈A (~-trans (~-trans a~d (~-sym a~d)) a~f))
  A⊆A″ f f∈A | in₂ a≁f = in₁ (a≁f , (in₁ ((λ d~f → a≁f (~-trans a~d d~f)) , f∈A)))
  
  A″⊆A : (A″ ⊆ A)
  A″⊆A f  (in₁ (_ , in₁ (_ , f∈A))) = f∈A
  A″⊆A .d (in₁ (a≁d , in₂ refl)) = contradiction (a≁d a~d)
  A″⊆A .a (in₂ refl) = a∈A

  H=H″ : (H ≣ H″)
  H=H″ = NH-CONG H H″ A⊆A″ A″⊆A REFL REFL REFL

fwd-WF : ∀ {D} (H : NavigationHistory(D)) e →
  WellFormed(H) →
  (e ∈ FwdTarget(H)) →
  WellFormed(H traverse-to e)
fwd-WF H e H∈WF ((f , (f∈A , f≲e)) , e-min) a≲b c≲d (in₁ (e≁a , a∈A)) (in₁ (e≁d , d∈A)) = H∈WF a≲b c≲d a∈A d∈A
fwd-WF H e H∈WF ((f , (f∈A , f≲e)) , e-min) a≲b c≲e (in₁ (e≁a , a∈A)) (in₂ refl)        = e-min _ (_ , (a∈A , a≲b))
fwd-WF H e H∈WF ((f , (f∈A , f≲e)) , e-min) e≲b c≲d (in₂ refl)        (in₁ (e≁d , d∈A)) = H∈WF (≲-trans f≲e e≲b) c≲d f∈A d∈A where open NavigationHistory H
fwd-WF H e H∈WF ((f , (f∈A , f≲e)) , e-min) e≲b c≲e (in₂ refl)        (in₂ refl)        = e-min _ (f , (f∈A , ≲-trans f≲e e≲b)) where open NavigationHistory H

back-WF : ∀ {D} (H : NavigationHistory(D)) e e∈CGB →
  WellFormed(H) →
  (e ∈ BackTarget(H)) →
  WellFormed(H traverse-from e ∵ e∈CGB)
back-WF H e e∈CGB H∈WF ((e∈A , _) , e-max)         (a<b , a~b) c≲d a∈A′              d∈A′              with max(SessionPast(e)) ∵ e∈CGB where open NavigationHistory H
back-WF H e e∈CGB H∈WF ((e∈A , _) , e-max)         (a<b , a~b) c≲d (in₁ (f≁a , a∈A)) (in₁ (f≁d , d∈A)) | (f , ((f<e , f~e) , f-max)) = H∈WF (a<b , a~b) c≲d a∈A d∈A
back-WF H e e∈CGB H∈WF ((e∈A , _) , e-max)         (a<b , a~b) c≲f (in₁ (f≁a , a∈A)) (in₂ refl)        | (f , ((f<e , f~e) , f-max)) = ≤-trans (<-impl-≤ f<e) (H∈WF (a<b , a~b) (f<e , f~e) a∈A e∈A) where open NavigationHistory H
back-WF H e e∈CGB H∈WF ((e∈A , _) , e-max) {b = b} (f<b , f~b) c≲d (in₂ refl)        (in₁ (f≁d , d∈A)) | (f , ((f<e , f~e) , f-max)) with ≤-total b e | ≤-total e b where open NavigationHistory H
back-WF H e e∈CGB H∈WF ((e∈A , _) , e-max)         (f<b , f~b) c≲d (in₂ refl)        (in₁ (f≁d , d∈A)) | (f , ((f<e , f~e) , f-max)) | in₁ b≤e | in₁ e≤b with ≤-asym b≤e e≤b where open NavigationHistory H
back-WF H e e∈CGB H∈WF ((e∈A , _) , e-max)         (f<b , f~b) c≲d (in₂ refl)        (in₁ (f≁d , d∈A)) | (f , ((f<e , f~e) , f-max)) | in₁ b≤e | in₁ e≤b | refl = e-max _ (d∈A , (_ , c≲d))
back-WF H e e∈CGB H∈WF ((e∈A , _) , e-max)         (f<b , f~b) c≲d (in₂ refl)        (in₁ (f≁d , d∈A)) | (f , ((f<e , f~e) , f-max)) | in₁ b≤e | in₂ b<e = contradiction (<-impl-≱ f<b (f-max _ (b<e , ~-trans (~-sym f~b) f~e))) where open NavigationHistory H
back-WF H e e∈CGB H∈WF ((e∈A , _) , e-max)         (f<b , f~b) c≲d (in₂ refl)        (in₁ (f≁d , d∈A)) | (f , ((f<e , f~e) , f-max)) | in₂ e<b | _ = H∈WF (e<b , ~-trans (~-sym f~e) f~b) c≲d e∈A d∈A where open NavigationHistory H
back-WF H e e∈CGB H∈WF ((e∈A , _) , e-max)         (f<b , f~b) c≲f (in₂ refl)        (in₂ refl)        | (f , ((f<e , f~e) , f-max)) = <-impl-≤ f<b where open NavigationHistory H

