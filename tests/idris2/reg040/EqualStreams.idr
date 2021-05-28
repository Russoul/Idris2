%default total

r1 : a -> Stream a
r1 x = xs where
  xs : Stream a
  xs = x :: xs

r2 : a -> Stream a
r2 x = x :: r2 x

repeatsTheSame_fail : (x : a) -> r1 x === r2 x
repeatsTheSame_fail x = Refl

data Bisimilarity : (s1, s2 : Stream a) -> Type where
  Bisimilar : (x === y)
           -> (xs === ys)
           -> Bisimilarity (x :: xs) (y :: ys)

onTail : Bisimilarity (x :: Delay xs) (y :: Delay ys) -> xs === ys
onTail (Bisimilar _ tail) = tail

repeatsBisimilar : (x : a) -> Bisimilarity (r1 x) (r2 x)
repeatsBisimilar x = Bisimilar Refl (?t $ onTail $ repeatsBisimilar x)

------------

InfList : Type -> Type
InfList ty = Either () (ty, Inf (InfList ty))

Nil : InfList ty
Nil = Left ()

infixr 5 ::
(::) : ty -> InfList ty -> InfList ty
(::) head tail = Right (head, delay tail)

-- %logging "elab" 10
-- -- %logging "unify" 10
-- test : InfList Nat
-- test = 1 :: 2 `Main.(::)` 3 `Main.(::)` Main.Nil
-- %logging "elab" 0
