module P

%access export

data Tree : Type -> Type where
  Leaf : a -> Tree a
  Branch : a -> Tree a -> Tree a -> Tree a

flipTree : Tree a -> Tree a
flipTree (Leaf x) = Leaf x
flipTree (Branch x l r) = Branch x (flipTree r) (flipTree l)

%default total

flipTreeSym : (t : Tree a) -> t = flipTree (flipTree t)
flipTreeSym (Leaf x) = Refl
flipTreeSym (Branch x y z) =
            rewrite flipTreeSym y in
            rewrite flipTreeSym z in
            Refl

