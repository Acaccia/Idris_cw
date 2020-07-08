module PlusComm

%access public export

codata Conat : Type where
       Coz : Conat
       Cos : Inf Conat -> Conat

codata Bisimulation : Conat -> Conat -> Type where
       Biz : Bisimulation Coz Coz
       Bis : {a : Conat} -> {b : Conat} -> (Bisimulation a b) -> (Bisimulation (Cos a) (Cos b))

MuGen : Conat
MuGen = Cos MuGen

muGenSucc : Bisimulation (Cos MuGen) MuGen
muGenSucc = Bis (Delay muGenSucc)

Add : Conat -> Conat -> Conat
Add Coz y = y
Add (Cos x) y = Cos (Add x y)

BisimulationRefl : (x : Conat) -> Bisimulation x x
BisimulationRefl Coz = Biz
BisimulationRefl (Cos x) = Bis (Delay (BisimulationRefl x))

BisimulationTrans : Bisimulation x y -> Bisimulation y z -> Bisimulation x z
BisimulationTrans Biz Biz = Biz
BisimulationTrans (Bis x) (Bis y) = Bis (Delay (BisimulationTrans x y))

AddCozRightNeutral : (x : Conat) -> Add x Coz = x
AddCozRightNeutral Coz = Refl
AddCozRightNeutral (Cos x) = rewrite AddCozRightNeutral x in Refl

AddCosRightCos : (x : Conat) -> (y : Conat) -> Bisimulation (Cos (Add x y)) (Add x (Cos y))
AddCosRightCos Coz y = Bis (BisimulationRefl y)
AddCosRightCos (Cos x) y = Bis (AddCosRightCos x y)

-- Idris weak weak, partial implementation is allowed but there's random test
plusCommutative : (a : Conat) -> (b : Conat) -> Bisimulation (Add a b) (Add b a)
plusCommutative Coz b = rewrite AddCozRightNeutral b in BisimulationRefl b
plusCommutative (Cos x) y = BisimulationTrans (Bis (plusCommutative x y)) ((AddCosRightCos y x))
