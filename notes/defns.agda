module defns where

open import prelude

record NavigationHistory(D : Set) : Set₁ where

  field A : Subset(D)
  field Fo : Forest(D)
  field FTO : FiniteTotalOrder(D)
  field Eq : Equivalence(D)

  open FiniteTotalOrder FTO public
  open Forest Fo public
  open Equivalence Eq public

  field active : D → D
  field active-A : ∀ d → A(active d)
  field active-~ : ∀ d → (active d ~ d)
  field active-uniq : ∀ d e → A(e) → (d ~ e) → (e ≡ active d)

  field PATCH : ∀ {a b c d} → (a ∈ A) → (d ∈ A) → (a ~ b) → (c ~ d) → (a < b) → (c < d) → (d ≤ b)

  _≲_ : Rel(D)
  (d ≲ e) = (d < e) ∧ (d ~ e)
  
  ≲-trans : ∀ {d e f} → (d ≲ e) → (e ≲ f) → (d ≲ f)
  ≲-trans (d<e , d~e) (e<f , e~f) = ((<-trans d<e e<f) , (~-trans d~e e~f))

  ≲-impl-< : ∀ {d e} → (d ≲ e) → (d < e)
  ≲-impl-< (d<e , d~e) = d<e

  ≲-impl-~ : ∀ {d e} → (d ≲ e) → (d ~ e)
  ≲-impl-~ (d<e , d~e) = d~e

  active-~-impl-≡ : ∀ {d e} → (d ∈ A) → (e ∈ A) → (d ~ e) → (d ≡ e)
  active-~-impl-≡ {d} {e} d∈A e∈A d~e = trans (active-uniq d d d∈A ~-refl) (sym (active-uniq d e e∈A d~e))
  
  SessionPast : D → Subset(D)
  SessionPast(d) e = (e ≲ d)

  SessionFuture : D → Subset(D)
  SessionFuture(d) e = (d ≲ e)

  JointSessionPast : Subset(D)
  JointSessionPast d = Inhabited (A ∩ SessionFuture(d))

  JointSessionFuture : Subset(D)
  JointSessionFuture d = Inhabited (A ∩ SessionPast(d))

  CanGoBack : Subset(D)
  CanGoBack d = Inhabited(SessionPast(d))
  
  FwdTarget : Subset(D)
  FwdTarget = Min(JointSessionFuture)

  BackTarget : Subset(D)
  BackTarget = Max(A ∩ CanGoBack)

  FwdTarget* : ∀ {n} → Subset(D ^ n)
  FwdTarget* = Min*(Increasing ∩ All(JointSessionFuture))

  BackTarget* : ∀ {n} → Subset(D ^ n)
  BackTarget* = Max*(Decreasing ∩ All((A ∪ JointSessionPast) ∩ CanGoBack))
  
open NavigationHistory public using (FwdTarget ; BackTarget ; FwdTarget* ; BackTarget*)

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

  postulate PATCH′ : ∀ {a b c d} → (a ∈ A′) → (d ∈ A′) → (a ~ b) → (c ~ d) → (a < b) → (c < d) → (d ≤ b)
  
  H′ = record { A = A′ ; Fo = Fo ; FTO = FTO ; Eq = Eq
              ; active = active′ ; active-A = active′-A′ ; active-~ = active′-~ ; active-uniq = active′-uniq
              ; PATCH = PATCH′ }

_traverses-to_ : ∀ {D n} → NavigationHistory(D) → (D ^ n) → NavigationHistory(D)
(H traverses-to nil) = H
(H traverses-to (d ∷ ds)) = (H traverse-to d) traverses-to ds

_traverse-from_∵_ : ∀ {D} (H : NavigationHistory(D)) d →
  let open NavigationHistory H in 
  (d ∈ CanGoBack) →
  NavigationHistory(D)
(H traverse-from d ∵ d∈CGB) with max(SessionPast(d)) ∵ d∈CGB where open NavigationHistory H
(H traverse-from d ∵ d∈CGB) | (c , _) = (H traverse-to c)

_traverses-from_∵_ : ∀ {D n} (H : NavigationHistory(D)) (ds : D ^ n) →
  let open NavigationHistory H in 
  (ds ∈ All(CanGoBack)) →
  NavigationHistory(D)
(H traverses-from nil ∵ tt) = H
(H traverses-from (d ∷ ds) ∵ (d∈CGB , ds∈CGB)) = (H traverse-from d ∵ d∈CGB) traverses-from ds ∵ ds∈CGB

data _traverses-by_to_ {D} (H : NavigationHistory(D)) : ℤ → (H : NavigationHistory(D)) → Set where
  fwd : ∀ {δ} (ds : D ^ (succ δ)) → (ds ∈ FwdTarget*(H)) → (H traverses-by (succ δ) to (H traverses-to ds))
  back : ∀ {δ} (ds : D ^ δ) ds∈CGB → (ds ∈ BackTarget*(H)) → (H traverses-by (-ve δ) to (H traverses-from ds ∵ ds∈CGB))
