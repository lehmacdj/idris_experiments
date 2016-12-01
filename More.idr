module More

-- The IO monad
-- Pretty much just like haskell
greet : IO ()
greet = do putStr "What is your name? "
           name <- getLine
           putStrLn ("Hello " ++ name)

-- Lazyness
ifThenElse' : Bool -> Lazy a -> Lazy a -> a
ifThenElse' True t e = Force t
ifThenElse' False t e = Force e

main : IO ()
main = do
  let x : Integer = head [1,2,3]
  print x
  putStrLn ""

-- Useful for defining infinite data structures
codata Stream' : Type -> Type where
  (::) : (e : a) -> Stream' a -> Stream' a

-- Codata doesn't work for mutually recursive
-- Instead this has to be done the manual way
mutual
  data Blue : Type -> Type where
    B : a -> Inf (Red a) -> Blue a

  data Red : Type -> Type where
    R : a -> Inf (Blue a) -> Red a

mutual
  blue : Blue Nat
  blue = B 1 red

  red : Red Nat
  red = R 2 blue

mutual
  findB : (a -> Bool) -> Blue a -> a
  findB f (B x r) = if f x then x else findR f r

  findR : (a -> Bool) -> Red a -> a
  findR f (R x b) = if f x then x else findB f b
