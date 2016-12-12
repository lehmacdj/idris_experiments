using (k : Nat)
  mutual
    ||| Even n is a type for which any element is a proof that n is even
    data Even : Nat -> Type where
      ||| Either the number is zero
      IsZero : Even Z
      ||| Or the number is the successor of an even number
      IsEven : Odd k -> Even (S k)

    ||| Odd n is a type for which any element is a proof that n is odd
    data Odd : Nat -> Type where
      ||| Either the number is one
      IsOne : Odd (S Z)
      ||| or it is the successor of an even number
      IsOdd : Even k -> Odd (S k)

||| Z is not an odd number
Uninhabited (Odd Z) where
  uninhabited IsOne impossible

||| (S Z) is not an even number
Uninhabited (Even (S Z)) where
  uninhabited IsZero impossible
  uninhabited (IsEven x) = uninhabited x

||| Finds half of a number
||| won't compile if the number isn't Even
||| Evaluation of the auto ok takes a very long time and sometimes fails if
||| n is too large
halveEvenNumber : (n:Nat) -> {auto ok: Even n} -> Nat
halveEvenNumber n = n `div` 2
