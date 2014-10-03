module Printf4 where

open import Data.Char
open import Data.String
open import Data.List hiding (_++_)
open import Function using (_∘_)
open import Data.Nat
open import Data.Nat.Show renaming (show to showℕ)

data Format : Set where
  FNat : Format → Format
  FStr : Format → Format
  FLit : Char → Format → Format
  FEnd : Format

toFormat : List Char → Format
toFormat [] = FEnd
toFormat ('%' ∷ 'd' ∷ cs) = FNat (toFormat cs)
toFormat ('%' ∷ 's' ∷ cs) = FStr (toFormat cs)
toFormat (c ∷ cs) = FLit c (toFormat cs)

strToFormat : String → Format
strToFormat = toFormat ∘ toList

interpFormat : Format → Set
interpFormat (FNat f) = ℕ → interpFormat f
interpFormat (FStr f) = String → interpFormat f
interpFormat (FLit x f) = interpFormat f
interpFormat FEnd = String

toFunction : (fmt : Format) → String → interpFormat fmt
toFunction (FNat f) a = λ n → toFunction f (a ++ showℕ n)
toFunction (FStr f) a = λ s → toFunction f (a ++ s)
toFunction (FLit c f) a = toFunction f (a ++ fromList [ c ])
toFunction FEnd a = a

-- "hello %s(%d) san" => String → ℕ → String
printf : (fmt : String) → interpFormat (strToFormat fmt)
printf f = toFunction (strToFormat f) ""
