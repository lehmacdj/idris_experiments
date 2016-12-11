import Data.Fin
import Data.Vect

data Ty = TyInt | TyBool | TyFun Ty Ty

interpTy : Ty -> Type
interpTy TyInt       = Integer
interpTy TyBool      = Bool
interpTy (TyFun D C) = interpTy D -> interpTy C

using (G : Vect n Ty)
  data HasType : (i : Fin n) -> Vect n Ty -> Ty -> Type where
    Stop : HasType FZ (t :: G) t
    Pop  : HasType k G t -> HasType (FS k) (u :: G) t

  data Expr : Vect n Ty -> Ty -> Type where
    Var : HasType i G t -> Expr G t
    Val : (x : Integer) -> Expr G TyInt
    Lam : Expr (a :: G) t -> Expr G (TyFun a t)
    App : Expr G (TyFun a t) -> Expr G a -> Expr G t
    Op  : (interpTy a -> interpTy b -> interpTy c) ->
          Expr G a -> Expr G b -> Expr G c
    If : Expr G TyBool -> Lazy (Expr G a) -> Lazy (Expr G a) -> Expr G a

  data Env : Vect n Ty -> Type where
    Nil : Env Nil
    (::) : interpTy a -> Env G -> Env (a :: G)

  lookup : HasType i G t -> Env G -> interpTy t
  lookup Stop    (x :: xs) = x
  lookup (Pop k) (x :: xs) = lookup k xs

  interp : Env G -> Expr G t -> interpTy t
  interp env (Var i) = lookup i env
  interp env (Val v) = v
  interp env (Lam s) = \x => interp (x :: env) s
  interp env (App f e) = (interp env f) (interp env e)
  interp env (Op op x y) = op (interp env x) (interp env y)
  interp env (If g t e) = if interp env g
                            then interp env t
                            else interp env e

  -- λx.λy.y + x
  add : Expr G (TyFun TyInt (TyFun TyInt TyInt))
  add = Lam (Lam (Op (+) (Var Stop) (Var (Pop Stop))))

  -- λx. if (x == 0) then 1 else (fact (x - 1) * x)
  fact : Expr G (TyFun TyInt TyInt)
  fact = Lam (If (Op (==) (Var Stop) (Val 0))
                 (Val 1)
                 (Op (*)
                     (App fact (Op (-) (Var Stop) (Val 1)))
                     (Var Stop)))

main : IO ()
main = do
    putStr "Enver a number: "
    x <- getLine
    printLn (interp [] fact (cast x))
