module Printf2 where

open import Data.List hiding (_++_)
open import Data.String
open import Data.Char
open import Data.Nat.Show renaming (show to showℕ)
open import Data.Nat
open import Function using (_∘_)

data Format : Set where
  FInt : Format → Format -- %d
  FString : Format → Format -- %s
  FOther : Char → Format → Format -- [a-zA-Z0-9]
  FEnd : Format

format : List Char → Format
format [] = FEnd
format ('%' ∷ 'd' ∷ cs) = FInt (format cs)
format ('%' ∷ 's' ∷ cs) = FString (format cs)
format (c ∷ cs) = FOther c (format cs)

interpFormat : Format → Set
interpFormat (FInt f) = ℕ → interpFormat f
interpFormat (FString f) = String → interpFormat f
interpFormat (FOther x f) = interpFormat f
interpFormat FEnd = String

formatString : String → Format
formatString = format ∘ toList

toFunction : (fmt : Format) → String → interpFormat fmt
toFunction (FInt f) a = λ i → toFunction f (a ++ showℕ i)
toFunction (FString f) a = λ s → toFunction f (a ++ s)
toFunction (FOther x f) a = toFunction f (a ++ (fromList [ x ]))
toFunction FEnd a = a

printf : (fmt : String) → interpFormat (formatString fmt)
printf fmt = toFunction (formatString fmt) ""
