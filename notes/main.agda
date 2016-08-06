module main where

open import prelude
open import defns
open import lemmas

Theorem : ∀ {D} {H H′ H″ : NavigationHistory(D)} {δ δ′} →
  (H traverses-back-by δ to H′) → 
  (H′ traverses-back-by δ′ to H″) → 
  (H traverses-back-by (δ + δ′) to H″)
Theorem {D} (back ds ds∈CGB ds∈BT) = Lemma ds ds∈CGB ds∈BT where

  Lemma : ∀ {H δ δ′ H″} (ds : D ^ δ) ds∈CGB →
    (ds ∈ BackTarget*(H)) → 
    ((H traverses-from ds ∵ ds∈CGB) traverses-back-by δ′ to H″) →
    (H traverses-back-by (δ + δ′) to H″)
  Lemma {H} nil _ _ H′-to-H″ = H′-to-H″
  Lemma {H} (d ∷ ds) (d∈CGB , ds∈CGB) d∷ds∈BT H′-to-H″ with Lemma ds ds∈CGB (BT-tl {H = H} d d∈CGB ds d∷ds∈BT) H′-to-H″
  Lemma {H} (d ∷ ds) (d∈CGB , ds∈CGB) d∷ds∈BT H′-to-H″ | back ds′ ds′∈CGB ds′∈BT = back (d ∷ ds′) (d∈CGB , ds′∈CGB) (BT-cons {H = H} d d∈CGB ds′ (BT-hd {H = H} d ds d∷ds∈BT) ds′∈BT)

