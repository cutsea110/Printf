module Printf3 where

open import Level
open import Data.Nat
open import Data.Nat.Show renaming (show to showℕ)
open import Data.Char
open import Data.String
open import Data.List hiding (_++_)
open import Function using (_∘_)

data Format : Set where
  FInt : Format → Format
  FString : Format → Format
  FLit : Char → Format → Format
  FEnd : Format

--        [end, int, str, lit]     FEnd   FInt    FString     FLit
--   X <------------------------- 1    +   X  +     X     + C x X
--   |                            |
-- u |                            |   1 + u + u + c x u
--   |                            |
--   v <------------------------- v
--   A    [e, i , s, l]           1     +   A  +     A     + C x A
--
--
--
-- u = (|[e, i, s, l]|) = cata e i s l
--
-- u (end) = e
-- u (int x) = i (u x)
-- u (str x) = s (u x)
-- u (lit c x) = l c (u x)
--
-- Catamorphism
cata : {ℓ : Level} {A : Set ℓ} → A → (A → A) → (A → A) → (Char → A → A) → Format → A
cata e i s l FEnd = e
cata e i s l (FInt f) = i (cata e i s l f)
cata e i s l (FString f) = s (cata e i s l f)
cata e i s l (FLit c f) = l c (cata e i s l f)

parse : List Char → Format
parse [] = FEnd
parse ('%' ∷ 'd' ∷ cs) = FInt (parse cs)
parse ('%' ∷ 's' ∷ cs) = FString (parse cs)
parse (c ∷ cs) = FLit c (parse cs)

toFormat : String → Format
toFormat = parse ∘ toList

{--
interpFormat : Format → Set
interpFormat (FInt f) = ℕ → interpFormat f
interpFormat (FString f) = String → interpFormat f
interpFormat (FLit x f) = interpFormat f
interpFormat FEnd = String
--}

interpFormat : Format → Set
interpFormat = cata String (λ f → ℕ → f) (λ f → String → f) (λ _ f → f)

toFunction : (fmt : Format) → String → interpFormat fmt
toFunction = {!!} -- How?
{--
toFunction : (fmt : Format) → String → interpFormat fmt
toFunction (FInt f) r = λ n → toFunction f (r ++ showℕ n)
toFunction (FString f) r = λ s → toFunction f (r ++ s)
toFunction (FLit c f) r = toFunction f (r ++ fromList [ c ])
toFunction FEnd r = r
--}

printf : (fmt : String) → interpFormat (toFormat fmt)
printf fmt = toFunction (toFormat fmt) ""
