module Proof

%default total
%access export


zeroIsNotSucc : (k : Nat) -> (prf : (1 + 1) = ((S (S k)) + (S (S k)))) -> 0 = S (plus k (S k))
zeroIsNotSucc Z Refl impossible
zeroIsNotSucc (S _) Refl impossible


succIsNotZero : (k : Nat) -> (prf : ((S (S k)) + (S (S k))) = (1 + 1)) -> S (plus k (S k)) = 0
succIsNotZero Z Refl impossible
succIsNotZero (S _) Refl impossible

lemma : (k : Nat) -> (j : Nat) -> (prf : (S (k + S k)) = (S (j + S j))) -> (k + k) = (j + j)
lemma Z Z Refl = Refl
lemma Z (S k) prf = zeroIsNotSucc k prf
lemma (S k) Z prf = succIsNotZero k prf
lemma (S k) (S j) prf = rewrite succInjective k (S k) _ in ?lemma_rhs_3

invert : (a : Nat) -> (b : Nat) -> (a + a = b + b) -> a = b
invert Z Z Refl = Refl
invert Z (S _) Refl impossible
invert (S _) Z Refl impossible
invert (S k) (S j) prf = rewrite invert k j (lemma k j prf) in Refl
