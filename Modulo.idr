module Modulo

import Data.Fin

%access export
%default total

negate : Fin k -> Fin k
negate FZ = FZ
negate (FS FZ) = last
negate (FS (FS x)) = ?what_3

subt : Fin k -> Fin k -> Fin k
subt n m = ?subt

add : Fin k -> Fin k -> Fin k
add n m = subt n (negate m)

mult : Fin k -> Fin k -> Fin k
mult n m = ?mult

zero : Fin 5
zero = FZ
one : Fin 5
one = FS FZ
two : Fin 5
two = FS (FS FZ)
three : Fin 5
three = FS (FS (FS FZ))
four : Fin 5
four = FS (FS (FS (FS FZ)))
