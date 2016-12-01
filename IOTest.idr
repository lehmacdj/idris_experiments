module IOTest

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
  print r
