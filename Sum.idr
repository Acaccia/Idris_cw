module Sum

%access export
%default total

sumSimple : (Nat -> Nat) -> Nat -> Nat
sumSimple _ Z = Z
sumSimple f (S n) = f (S n) + sumSimple f n

sumAux : Nat -> (Nat -> Nat) -> Nat -> Nat
sumAux acc _ Z = acc
sumAux acc f (S n) = sumAux (f (S n) + acc) f n

sumTail : (Nat -> Nat) -> Nat -> Nat
sumTail = sumAux 0

sumEq : (f : Nat -> Nat) -> (n : Nat) -> sumTail f n = sumSimple f n
sumEq f Z = Refl
sumEq f (S k) = ?write_a_proof_2
