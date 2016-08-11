module main where

open import prelude
open import defns
open import lemmas

BackTheorem : ∀ {D} {H H′ H″ : NavigationHistory(D)} {δ δ′} →
  (WellFormed(H)) →
  (H traverses-by (-ve δ) to H′) → 
  (H′ traverses-by δ′ to H″) → 
  (H traverses-by (-ve δ + δ′) to H″)

BackTheorem {δ = zero} H∈WF (back nil ds∈CGB ds∈BT) H′-to-H″ = H′-to-H″
BackTheorem {D} {H} {._} {H″} {δ = succ δ} {δ′} H∈WF (back (d ∷ ds) (d∈CGB , ds∈CGB) d∷ds∈BT) H′-to-H″ = H-to-H″ where

  H₁ = (H traverse-from d ∵ d∈CGB)
  H′ = (H₁ traverses-from ds ∵ ds∈CGB)

  d∈BT : (d ∈ BackTarget(H))
  d∈BT = BT-hd {H = H} d ds d∷ds∈BT

  ds∈BT₁ : (ds ∈ BackTarget*(H₁))
  ds∈BT₁ = BT-tl {H = H} d d∈CGB ds d∷ds∈BT

  H₁∈WF : WellFormed(H₁)
  H₁∈WF = back-WF H d d∈CGB H∈WF d∈BT
  
  H₁-to-H″ : H₁ traverses-by (-ve δ + δ′) to H″
  H₁-to-H″ = BackTheorem H₁∈WF (back ds ds∈CGB ds∈BT₁) H′-to-H″
  
  Lemma : ∀ {H″} n →
    (H₁ traverses-by n to H″) →
    (H traverses-by pred n to H″)
  Lemma (succ zero) (fwd (e ∷ nil) e∷es∈FT₁) = H-to-H₀ where

    H₀ = (H₁ traverse-to e)

    e∈FT₁ : (e ∈ FwdTarget(H₁))
    e∈FT₁ = FT-hd {H = H₁} e nil e∷es∈FT₁

    H=H₀ : H ≣ H₀
    H=H₀ = from-to d e d∈CGB H∈WF d∈BT e∈FT₁
    
    H₀-to-H₀ : (H₀ traverses-by (-ve zero) to H₀)
    H₀-to-H₀ = back nil tt (BT-nil {H = H₀})
    
    H-to-H₀ : H traverses-by (-ve zero) to H₀
    H-to-H₀ = SUBST (λ ∙ → ∙ traverses-by (-ve zero) to H₀) H=H₀ H₀-to-H₀

  Lemma (succ (succ n)) (fwd (e ∷ es) e∷es∈FT₁) = H-to-Hₙ where

    H₀ = (H₁ traverse-to e)
    Hₙ = (H₁ traverses-to (e ∷ es))

    e∈FT₁ : (e ∈ FwdTarget(H₁))
    e∈FT₁ = FT-hd {H = H₁} e es e∷es∈FT₁

    es∈FT₀ : (es ∈ FwdTarget*(H₀))
    es∈FT₀ = FT-tl {H = H₁} e es e∷es∈FT₁

    H=H₀ : H ≣ H₀
    H=H₀ = from-to d e d∈CGB H∈WF d∈BT e∈FT₁
    
    H₀-to-Hₙ : H₀ traverses-by (succ n) to Hₙ
    H₀-to-Hₙ = fwd es es∈FT₀
    
    H-to-Hₙ : H traverses-by (succ n) to Hₙ
    H-to-Hₙ = SUBST (λ ∙ → ∙ traverses-by succ n to Hₙ) H=H₀ H₀-to-Hₙ
    
  Lemma (-ve n) (back es es∈CGB es∈BT₁) = back (d ∷ es) (d∈CGB , es∈CGB) (BT-cons {H = H} d d∈CGB es d∈BT es∈BT₁)

  H-to-H″ : H traverses-by (-ve (succ δ) + δ′) to H″
  H-to-H″ = Lemma (-ve δ + δ′) H₁-to-H″
  
FwdTheorem : ∀ {D} {H H′ H″ : NavigationHistory(D)} {δ δ′} →
  (WellFormed(H)) →
  (H traverses-by (succ δ) to H′) → 
  (H′ traverses-by δ′ to H″) → 
  (H traverses-by (succ δ + δ′) to H″)

FwdTheorem {D} {H} {._} {H″} {δ = δ} {δ′} H∈WF (fwd (d ∷ ds) d∷ds∈FT) H′-to-H″ with Lemma where

  H₁ = (H traverse-to d)
  H′ = (H₁ traverses-to ds)
  
  d∈FT : (d ∈ FwdTarget(H))
  d∈FT = FT-hd {H = H} d ds d∷ds∈FT

  Lemma : ∀ {H″} n →
    (H₁ traverses-by n to H″) →
    (H traverses-by sucz n to H″)
  Lemma (succ n) (fwd es es∈FT₁) = fwd (d ∷ es) (FT-cons {H = H} d es d∈FT es∈FT₁)

  Lemma (-ve zero) (back nil _ _) = fwd (d ∷ nil) (FT-cons {H = H} d nil d∈FT (FT-nil {H = H₁}))
  
  Lemma (-ve (succ n)) (back (e ∷ es) (e∈CGB , es∈CGB) e∷es∈BT₁) = H-to-Hₙ where
  
    H₀ = (H₁ traverse-from e ∵ e∈CGB)
    Hₙ = (H₁ traverses-from (e ∷ es) ∵ (e∈CGB , es∈CGB))

    e∈BT₁ : (e ∈ BackTarget(H₁))
    e∈BT₁ = BT-hd {H = H₁} e es e∷es∈BT₁

    es∈BT₀ : (es ∈ BackTarget*(H₀))
    es∈BT₀ = BT-tl {H = H₁} e e∈CGB es e∷es∈BT₁

    H=H₀ : H ≣ H₀
    H=H₀ = to-from d e e∈CGB H∈WF d∈FT e∈BT₁
    
    H₀-to-Hₙ : H₀ traverses-by (-ve n) to Hₙ
    H₀-to-Hₙ = back es es∈CGB es∈BT₀
    
    H-to-Hₙ : H traverses-by (-ve n) to Hₙ
    H-to-Hₙ = SUBST (λ ∙ → ∙ traverses-by (-ve n) to Hₙ) H=H₀ H₀-to-Hₙ

FwdTheorem {D} {H} {._} {H″} {δ = zero} {δ′} H∈WF (fwd (d ∷ nil) d∷nil∈FT) H′-to-H″ | Lemma = Lemma δ′ H′-to-H″

FwdTheorem {D} {H} {._} {H″} {δ = succ δ} {δ′} H∈WF (fwd (d ∷ ds) d∷ds∈FT) H′-to-H″ | Lemma = H-to-H″ where

  H₁ = (H traverse-to d)

  d∈FT : (d ∈ FwdTarget(H))
  d∈FT = FT-hd {H = H} d ds d∷ds∈FT

  ds∈FT₁ : (ds ∈ FwdTarget*(H₁))
  ds∈FT₁ = FT-tl {H = H} d ds d∷ds∈FT

  H₁∈WF : WellFormed(H₁)
  H₁∈WF = fwd-WF H d H∈WF d∈FT
  
  H₁-to-H″ : H₁ traverses-by (succ δ + δ′) to H″
  H₁-to-H″ = FwdTheorem H₁∈WF (fwd ds ds∈FT₁) H′-to-H″

  H-to-H″ : H traverses-by sucz (succ δ + δ′) to H″
  H-to-H″ = subst (λ ∙ → H traverses-by ∙ to H″) (succ-dist-+ (succ δ) δ′) (Lemma (succ δ + δ′) H₁-to-H″)

Theorem : ∀ {D} {H H′ H″ : NavigationHistory(D)} {δ δ′} →
  (WellFormed(H)) →
  (H traverses-by δ to H′) → 
  (H′ traverses-by δ′ to H″) → 
  (H traverses-by (δ + δ′) to H″)

Theorem {δ = succ δ} = FwdTheorem
Theorem {δ = -ve δ} = BackTheorem
