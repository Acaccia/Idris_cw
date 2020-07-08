module AppendInjective

%access export
%default total

consInjectiveLeft : {x, y : a} -> {xs, ys : List a} -> x :: xs = y :: ys -> x = y
consInjectiveLeft Refl = Refl

consInjectiveRight : {x, y : a} -> {xs, ys : List a} -> x :: xs = y :: ys -> xs = ys
consInjectiveRight Refl = Refl

cong2 : {a, b, c : Type} -> {f : a -> b -> c}  -> {x1, x2 : a} -> {y1, y2 : b}
      -> x1 = x2 -> y1 = y2 -> f x1 y1 = f x2 y2
cong2 Refl Refl = Refl

appendInjectiveRight : (a, b, c : List x) -> a ++ b = a ++ c -> b = c
appendInjectiveRight [] c c Refl = Refl
appendInjectiveRight (y :: xs) b c prf =
                     rewrite appendInjectiveRight xs b c (lemma prf) in Refl
                     where lemma = snd . consInjective

appendInjectiveLeft : (a, b, c : List x) -> a ++ c = b ++ c -> a = b
appendInjectiveLeft [] [] c prf =  Refl
appendInjectiveLeft [] (y :: ys) c prf = ?appendInjectiveLeft_rhs_4
appendInjectiveLeft (x :: xs) [] c prf =  ?appendInjectiveLeft_rhs_1
appendInjectiveLeft (x :: xs) (y :: ys) c prf =
                    cong2 (consInjectiveLeft prf) (appendInjectiveLeft xs ys c (consInjectiveRight prf))
