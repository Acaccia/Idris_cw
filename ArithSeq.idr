module ArithSeq


%access export
%default total

arithSum : Nat -> Nat
arithSum Z = Z
arithSum (S n) = S n + arithSum n

-- We define our own function for dividing a natural
-- number by 2.
-- The existing Idris function divNatNZ
-- is not a good choice because it is impossible (correct
-- me if I my wrong) to prove many useful properties of
-- divNatNZ.
half : Nat -> Nat
half (S (S n)) = S (half n)
half _ = Z

arithFormula : Nat -> Nat
arithFormula n = half $ n * (n + 1)

arithEq : (n : Nat) -> arithFormula n = arithSum n
arithEq Z = Refl
arithEq (S k) = rewrite sym (arithEq k) in
                rewrite plusCommutative k 1 in
                rewrite multCommutative k (S (S k)) in
                ?lemma
