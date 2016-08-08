module main where

open import prelude
open import defns
open import lemmas

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
  
