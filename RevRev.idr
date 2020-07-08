module RevRev


%access export
%default total


rev : List x -> List x
rev [] = []
rev (y :: xs) = rev xs ++ [y]

reverseAppend : (xs : List a) -> (ys : List a) -> rev (xs ++ ys) = rev ys ++ rev xs
reverseAppend [] ys = rewrite appendNilRightNeutral (rev ys) in Refl
reverseAppend (x :: xs) ys =
              rewrite reverseAppend xs ys in
              rewrite appendAssociative (rev ys) (rev xs) [x] in
              Refl

revrevid : (xs : List a) -> rev (rev xs) = xs
revrevid [] = Refl
revrevid (x :: xs) =
         rewrite reverseAppend (rev xs) [x] in
         rewrite revrevid xs in
         Refl
