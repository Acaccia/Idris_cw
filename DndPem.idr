module DndPem

%access export
%default total

--- You need this to get the final submit work
public export
AxiomPEM : Type
AxiomPEM = {a, b : Type} -> (a -> b) -> ((a -> Void) -> b) -> b

public export
AxiomDNE : Type
AxiomDNE = {a : Type} -> ((a -> Void) -> Void) -> a

from : AxiomDNE -> AxiomPEM
from dne = ?check

to : AxiomPEM -> AxiomDNE
to pem = ?prove
