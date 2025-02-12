#  File converted from Magma code -- requires editing and checking
#  Magma -> GAP converter, version 0.5, 11/5/18 by AH

#  Global Variables used: Append, ClassicalStandardGenerators,
#  ClassicalStandardPresentation, Evaluate, EvenPlus,
#  EvenPlus_PresentationForN, EvenPlus_PresentationForN1, Factorial, GF, GL,
#  Id, Identity, Integers, IsEven, IsOdd, IsPrime, IsPrimePower, LHS,
#  MatrixAlgebra, Ngens, OddPlus, OddPlusGenerators, OddPlus_PresentationForN,
#  OddPlus_PresentationForN1, OmegaPlus4, PlusConvertToStandard,
#  PlusGeneratorOfCentre, PlusPresentationToStandard,
#  PlusStandardToPresentation, PrimitiveElement, RHS, FreeGroup, Universe, phi,
#  tau

#  Defines: EvenPlus, EvenPlus_OrderN, EvenPlus_PresentationForN,
#  EvenPlus_PresentationForN1, OddPlus, OddPlusGenerators, OddPlus_OrderN,
#  OddPlus_OrderN1, OddPlus_PresentationForN, OddPlus_PresentationForN1,
#  OmegaPlus4, PlusConvertToStandard, PlusGeneratorOfCentre, PlusGenerators,
#  PlusPresentation, PlusPresentationToStandard, PlusStandardToPresentation

DeclareGlobalFunction("PlusConvertToStandard");

DeclareGlobalFunction("PlusGeneratorOfCentre");

DeclareGlobalFunction("PlusStandardToPresentation");

DeclareGlobalFunction("PlusPresentationToStandard");

#  Forward declaration of PlusConvertToStandard
#  Forward declaration of PlusGeneratorOfCentre
#  Forward declaration of PlusStandardToPresentation
#  Forward declaration of PlusPresentationToStandard
OmegaPlus4:=function(q)
local F,Projective,S,T,Y,d,d1,gens,gog,rels,s,s1,t,t1,v,x,y;
  Projective:=ValueOption("Projective");
  if Projective=fail then
    Projective:=false;
  fi;
  F:=FreeGroup(8);
  d:=4;
  s:=F.1;
  s1:=F.4;
  t:=F.2;
  t1:=F.5;
  d:=F.3;
  d1:=F.6;
  v:=F.8;
  #   one of the standard generators is the identity
  rels:=[F.7];
  #   sl2 presentation on s, t, d
  S:=ClassicalStandardPresentation("SL",2,q);
  # need the variable "gog" (Generators Of Group) for the function MappedWord below
  gog:=GeneratorsOfGroup(FreeGroupOfFpGroup(S));
  Y:=FreeGroupOfFpGroup(S);
  S:=RelatorsOfFpGroup(S);
  gens:=[s,s,t,d,s^0,s^0,s^0,s^0];
  # was "T:=Evaluate(S,gens);"
  T:=List(S, w -> MappedWord(w, gog, gens));
  rels:=Concatenation(rels,T);
  #   sl2 presentation on s1, t1, d1
  gens:=[s1,s1,t1,d1,s1^0,s1^0,s1^0,s1^0];
  # was "T:=Evaluate(S,gens);"
  T:=List(S, w -> MappedWord(w, gog, gens));
  rels:=Concatenation(rels,T);
  for x in [s,t,d] do
    for y in [s1,t1,d1] do
      Add(rels,Comm(x,y));
    od;
  od;
  Add(rels,v/s1);
  Add(rels,s^2/s1^2);
  if Projective and IsOddInt(q) then
    Add(rels,F.3^(QuoInt((q-1),2)));
  fi;
  return F/rels;
end;

OddPlusGenerators:=function(d,q)
local lvarDelta,varE,F,U,V,varZ,gens,sigma,w;
  F:=GF(q);
  varZ:=IdentityMat(d,F);
  varZ[1][1]:=0;
  varZ[1][2]:=1;
  varZ[2][1]:=1;
  varZ[2][2]:=0;
  varZ[3][4]:=1;
  varZ[4][3]:=1;
  varZ[3][3]:=0;
  varZ[4][4]:=0;
  w:=PrimitiveElement(F);
  lvarDelta:=IdentityMat(d,F);
  lvarDelta[1][1]:=w^-1;
  lvarDelta[2][2]:=w;
  lvarDelta[3][3]:=w^1;
  lvarDelta[4][4]:=w^-1;
  varE:=ClassicalStandardGenerators("Omega+",d,q);
  U:=varE[4];
  sigma:=varE[5];
  V:=varE[8];
  gens:=[lvarDelta,sigma,varZ,U,V];
  return gens;
end;

PlusGenerators:=function(d,q)
local varE,F,MA,U,V,varZ,delta,gens,sigma,w;
  if d=4 then
    return ClassicalStandardGenerators("Omega+",d,q);
  fi;
  if IsOddInt(q) then
    return OddPlusGenerators(d,q);
  fi;
  F:=GF(q);
  w:=PrimitiveElement(F);
  delta:=IdentityMat(d, F);
  delta[1][1]:=w^-1;
  delta[2][2]:=w;
  varE:=ClassicalStandardGenerators("Omega+",d,q);
  sigma:=varE[5];
  U:=varE[4];
  V:=varE[8];
  varZ:=IdentityMat(d,F);
  varZ[1][1]:=0;
  varZ[1][2]:=1;
  varZ[2][1]:=1;
  varZ[2][2]:=0;
  varZ:=varZ*w^0;
  varZ:=varZ*varZ^U;
  gens:=[delta,sigma,varZ,U,V];
  return gens;
end;

#   infrastructure for OmegaPlus (2n, q) where q is even
EvenPlus_PresentationForN1:=function(n,q)
local F,R,R1,Rels,S,U,V,varZ,e,f,p,phi;
e := Factors(q);
    if Size(DuplicateFreeList(e)) > 1 then
        f := false;
    else
        f := true;
        p := e[1];
        e := Size(e);
    fi;
  F:=FreeGroup(3);
  U:=F.1;
  V:=F.2;
  varZ:=F.3;
  R1:=PresentationForSn(n);
  S:=FreeGroupOfFpGroup(R1);
  R1:=RelatorsOfFpGroup(R1);
  phi:=GroupHomomorphismByImages(S,F,
    GeneratorsOfGroup(S),
    [U,V]);
  R1:=List(R1,r->Image(phi,r));
  R:=[];
  if n > 3 then
    Add(R,Comm(varZ,U^(V^2)));
    Add(R,Comm(varZ,varZ^(V^2)));
  fi;
  if n > 4 then
    Add(R,Comm(varZ,V*U*U^V));
  fi;
  Add(R,Comm(varZ,varZ^V));
  Add(R,varZ*varZ^V/varZ^(U^V));
  Add(R,varZ^2);
  Add(R,Comm(varZ,U));
  Rels:=Concatenation(R,R1);
  return F/Rels;
end;

#   infrastructure for OmegaPlus (2n, q) where q is even
EvenPlus_PresentationForN:=function(n,q)
local F,R,R1,Rels,S,U,V,varZ,delta,e,f,p,phi;
e := Factors(q);
if Size(DuplicateFreeList(e)) > 1 then
    f := false;
else
    f := true;
    p := e[1];
    e := Size(e);
fi;
  F:=FreeGroup(4);
  U:=F.1;
  V:=F.2;
  varZ:=F.3;
  delta:=F.4;
  R1:=EvenPlus_PresentationForN1(n,q);
  S:=FreeGroupOfFpGroup(R1);
  R1:=RelatorsOfFpGroup(R1);
  phi:=GroupHomomorphismByImages(S,F,
    GeneratorsOfGroup(S),
    [U,V,varZ]);
  R1:=List(R1,r->Image(phi,r));
  R:=[];
  Add(R,Comm(delta,U^V));
  if n > 3 then
    Add(R,Comm(delta,V*U));
  fi;
  Add(R,Comm(delta,delta^U));
  Add(R,delta^(q-1));
  Add(R,delta^varZ/delta^-1);
  Add(R,Comm(delta,varZ^V));
  Rels:=Concatenation(R,R1);
  return F/Rels;
end;

EvenPlus_OrderN:=function(n,q)
return QuoInt((2*(q-1))^n*Factorial(n),2);
end;

#   presentation for OmegaPlus (2n, q) where q is even
EvenPlus:=function(d,q)
local lvarDelta,F,R1,R2,R3,R4,Rels,S,U,V,W,varZ,delta,e,f,n,p,phi,sigma,w;
  Assert(1,IsEvenInt(d));
  Assert(1,IsEvenInt(q));
  n:=QuoInt(d,2);
  Assert(1,n > 2);
  F:=GF(q);
  w:=PrimitiveElement(F);
  e := Factors(q);
  if Size(DuplicateFreeList(e)) > 1 then
      f := false;
  else
      f := true;
      p := e[1];
      e := Size(e);
  fi;
  F:=FreeGroup(5);
  delta:=F.1;
  sigma:=F.2;
  varZ:=F.3;
  U:=F.4;
  V:=F.5;
  if e=1 then
    R1:=EvenPlus_PresentationForN1(n,q);
    S:=FreeGroupOfFpGroup(R1);
    R1:=RelatorsOfFpGroup(R1);
    phi:=GroupHomomorphismByImages(S,F,
      GeneratorsOfGroup(S),
      [U,V,varZ]);
  else
    R1:=EvenPlus_PresentationForN1(n,q);
    S:=FreeGroupOfFpGroup(R1);
    R1:=RelatorsOfFpGroup(R1);
    phi:=GroupHomomorphismByImages(S,F,
      GeneratorsOfGroup(S),
      [U,V,varZ,delta]);
  fi;
  R1:=List(R1,r->Image(phi,r));
  Rels:=[];
    R2:=EvenPlus_PresentationForN1(n,q);
    S:=FreeGroupOfFpGroup(R2);
    R2:=RelatorsOfFpGroup(R2);
  if e=1 then
    phi:=GroupHomomorphismByImages(S,F,
      GeneratorsOfGroup(S),
      [sigma,U]);
    Add(Rels,delta);
  else
    lvarDelta:=delta*(delta^-1)^U;
    phi:=GroupHomomorphismByImages(S,F,
      GeneratorsOfGroup(S),
      [lvarDelta,sigma,U]);
  fi;
  R2:=List(R2,r->Image(phi,r));
  #   centraliser of sigma
  R3:=[];
  if e > 1 then
    Add(R3,Comm(sigma,delta*delta^U));
    Add(R3,Comm(sigma,delta^(V^2)));
  fi;
  Add(R3,Comm(sigma,varZ*U));
  if n > 3 then
    Add(R3,Comm(sigma,U^(V^2)));
  fi;
  if n > 4 then
    Add(R3,Comm(sigma,V*U*U^V));
  fi;
  if n > 3 then
    Add(R3,Comm(sigma,varZ^(V^2)));
  fi;
  #   Steinberg relations
  R4:=[];
  Add(R4,Comm(sigma,sigma^V)/sigma^(V*U));
  Add(R4,Comm(sigma,sigma^(V*U)));
  W:=U^(V*U);
  Add(R4,Comm(sigma,sigma^W));
  if n > 3 then
    Add(R4,Comm(sigma,sigma^(V^2)));
  fi;
  Add(R4,Comm(sigma,sigma^(varZ^V)));
  if n=4 then
    Add(R4,Comm(sigma,sigma^(varZ^V*V^2)));
  fi;
  Rels:=Concatenation(R1,R2, R3, R4);
  return F/Rels;
end;

#   infrastructure for OmegaPlus (2n, q) where q is odd
OddPlus_PresentationForN1:=function(n,q)
local F,R,R1,Rels,S,U,V,varZ,e,f,p,phi,w;
  F:=GF(q);
  w:=PrimitiveElement(F);
  e := Factors(q);
  if Size(DuplicateFreeList(e)) > 1 then
      f := false;
  else
      f := true;
      p := e[1];
      e := Size(e);
  fi;
  F:=FreeGroup(3);
  varZ:=F.1;
  U:=F.2;
  V:=F.3;
  R:=SignedPermutations(n);
  S:=FreeGroupOfFpGroup(R);
  R:=RelatorsOfFpGroup(R);
  phi:=GroupHomomorphismByImages(S,F,
    GeneratorsOfGroup(S),
    [U,V]);
  R:=List(R,r->Image(phi,r));
  R1:=[];
  if n > 3 then
    Add(R1,Comm(varZ,U^(V^2)));
    Add(R1,Comm(varZ,varZ^(V^2)));
  fi;
  if n > 4 then
    Add(R1,Comm(varZ,V*U*U^V));
  fi;
  Add(R1,varZ^2);
  Add(R1,Comm(varZ,(U^2)^V));
  if n > 2 then
    Add(R1,varZ*varZ^V/varZ^(V*U));
  fi;
  Add(R1,Comm(varZ,U));
  Add(R1,Comm(varZ,varZ^V));
  Rels:=Concatenation(R1,R);
  return F/Rels;
end;

OddPlus_OrderN1:=function(n)
return 2^(2*n-2)*Factorial(n);
end;

#   infrastructure for OmegaPlus (2n, q) where q is odd
OddPlus_PresentationForN:=function(n,q)
local lvarDelta,F,OMIT,R,R1,Rels,S,U,V,varZ,phi;
  Assert(1,n > 2);
  F:=FreeGroup(4);
  lvarDelta:=F.1;
  varZ:=F.2;
  V:=F.4;
  U:=F.3;
  R:=OddPlus_PresentationForN1(n,q);
  S:=FreeGroupOfFpGroup(R);
  R:=RelatorsOfFpGroup(R);
  phi:=GroupHomomorphismByImages(S,F,
    GeneratorsOfGroup(S),
    [varZ,U,V]);
  R:=List(R,r->Image(phi,r));
  R1:=[];
  if n > 3 then
    Add(R1,Comm(lvarDelta,U^(V^2)));
    Add(R1,Comm(lvarDelta,varZ^(V^2)));
    Add(R1,Comm(lvarDelta,lvarDelta^(V^2)));
  fi;
  if n > 4 then
    Add(R1,Comm(lvarDelta,V*U*U^V));
  fi;
  #   June 2018 change  -- replace by following
  #   Append (~R1, (Delta, Z * U) = 1);
  Add(R1,lvarDelta^U/lvarDelta^-1);
  Add(R1,Comm(lvarDelta,(U^2)^V));
  OMIT:=true;
  if not OMIT then
    Add(R1,(lvarDelta^(QuoInt((q-1),2)))/U^2);
  fi;
  Add(R1,lvarDelta*lvarDelta^(V)/lvarDelta^(V*U));
  Add(R1,Comm(lvarDelta,lvarDelta^V));
  Add(R1,lvarDelta^varZ/lvarDelta^-1);
  Rels:=Concatenation(R1,R);
  return F/Rels;
end;

OddPlus_OrderN:=function(n,q)
return (q-1)^n*2^(n-2)*Factorial(n);
end;

#   presentation for OmegaPlus (2n, q) where q is odd
OddPlus:=function(d,q)
local lvarDelta,F,I,R1,R2,R3,R4,Rels,S,U,V,W,varZ,b,e,f,n,p,phi,sigma,w;
  Assert(1,IsEvenInt(d));
  Assert(1,IsOddInt(q));
  n:=QuoInt(d,2);
  Assert(1,n > 2);
  F:=GF(q);
  w:=PrimitiveElement(F);
  e := Factors(q);
  if Size(DuplicateFreeList(e)) > 1 then
      f := false;
  else
      f := true;
      p := e[1];
      e := Size(e);
  fi;
  F:=FreeGroup(5);
  lvarDelta:=F.1;
  sigma:=F.2;
  varZ:=F.3;
  V:=F.5;
  U:=F.4;
  Rels:=[];
  #   additional relation needed for q = p to express Delta as word in sigma
  #  and U
  if IsPrimeInt(q) then
    b:=Int(1/w);
    w:=Int(w);
    Add(Rels,lvarDelta/((sigma^U)^(w-w^2)*sigma^(b)*(sigma^U)^((w-1))
     *sigma^-1));
  fi;
  if e=1 then
    R1:=OddPlus_PresentationForN1(n,q);
    S:=FreeGroupOfFpGroup(R1);
    R1:=RelatorsOfFpGroup(R1);
    phi:=GroupHomomorphismByImages(S,F,
      GeneratorsOfGroup(S),
      [varZ,U,V]);
  else
    R1:=OddPlus_PresentationForN1(n,q);
    S:=FreeGroupOfFpGroup(R1);
    R1:=RelatorsOfFpGroup(R1);
    phi:=GroupHomomorphismByImages(S,F,
      GeneratorsOfGroup(S),
      [lvarDelta,varZ,U,V]);
  fi;
  R1:=List(R1,r->Image(phi,r));
    R2:=OddPlus_PresentationForN1(n,q);
    S:=FreeGroupOfFpGroup(R2);
    R2:=RelatorsOfFpGroup(R2);
  if e=1 then
    phi:=GroupHomomorphismByImages(S,F,
      GeneratorsOfGroup(S),
      [sigma,U]);
  else
    phi:=GroupHomomorphismByImages(S,F,
      GeneratorsOfGroup(S),
      [lvarDelta,sigma,U]);
  fi;
  R2:=List(R2,r->Image(phi,r));
  #   centraliser of sigma
  R3:=[];
  if n > 3 then
    Add(R3,Comm(sigma,U^(V^2)));
  fi;
  if n > 4 then
    Add(R3,Comm(sigma,V*U^-1*(U^-1)^V));
  fi;
  if n > 3 then
    Add(R3,Comm(sigma,varZ^(V^2)));
  fi;
  if e > 1 then
    if n > 3 then
      Add(R3,Comm(sigma,lvarDelta^(V^2)));
    fi;
    Add(R3,Comm(sigma,lvarDelta^(varZ^V)));
    if n in Set([3,4]) then
      Add(R3,Comm(sigma,lvarDelta^(U^V)*lvarDelta^V));
    fi;
  fi;
  Add(R3,Comm(sigma,varZ*U));
  #   Steinberg relations
  R4:=[];
  Add(R4,Comm(sigma,sigma^V)/sigma^(V*U^-1));
  Add(R4,Comm(sigma,sigma^(V*U^-1)));
  W:=U^(V*U^-1);
  Add(R4,Comm(sigma,sigma^W));
  if n > 3 then
    Add(R4,Comm(sigma,sigma^(V^2)));
  fi;
  Add(R4,Comm(sigma,sigma^(varZ^V)));
  if n=4 then
    Add(R4,Comm(sigma,sigma^(varZ^V*V^2)));
  fi;
  Rels:=Concatenation(Rels, R3, R4,R1,R2)
   ;
  return F/Rels;
end;

PlusPresentation:=function(d,q)
local P,Presentation,Projective,R,Rels,S,n,z;
  Projective:=ValueOption("Projective");
  if Projective=fail then
    Projective:=false;
  fi;
  Presentation:=ValueOption("Presentation");
  if Presentation=fail then
    Presentation:=false;
  fi;
  if d=4 then
    return OmegaPlus4(q:Projective:=Projective);
  elif IsEvenInt(q) then
    R:=EvenPlus(d,q);
    P:=FreeGroupOfFpGroup(R);
    R:=RelatorsOfFpGroup(R);
  else
    R:=OddPlus(d,q);
    P:=FreeGroupOfFpGroup(R);
    R:=RelatorsOfFpGroup(R);
  fi;
  n:=QuoInt(d,2);
  if Projective and q^n mod 4=1 then
    z:=PlusGeneratorOfCentre(d,q,P);
    R:=Concatenation(R,[z]);
  fi;
  if Presentation then
    return P/R;
  fi;
  Rels:=PlusConvertToStandard(d,q,R);
  S:=FreeGroupOfFpGroup(Rels);
  Rels:=RelatorsOfFpGroup(Rels);
  Rels:=Filtered(Rels,w->w<>w^0);
  return S/Rels;
end;

#  don't know if this is really necessary
#  I need this function to get the list of letters of the words for MappedWord (see below)
WriteGenerators:=function(R)
local fam, F;
  fam:=FamilyObj(R[1]);
  F:=fam!.freeGroup;
  return GeneratorsOfGroup(F);
end;


#   relations are on presentation generators;
#  convert to relations on standard generators
InstallGlobalFunction(PlusConvertToStandard,
function(d,q,Rels)
local A,B,C,T,U,W,tau;
  A:=PlusStandardToPresentation(d,q);
  # was "Rels:=Evaluate(Rels,A);"
  Rels:=List(Rels, w-> MappedWord(w, WriteGenerators(Rels), A));
  B:=PlusPresentationToStandard(d,q);
  # TODO How to implement evaluate
  # was "C:=Evaluate(B,A);"
  C:=List(B, w-> MappedWord(w, WriteGenerators(B), A));
  # TODO How to implement universe
  U:=Universe(C);
  W:=Universe(Rels);
  tau:=GroupHomomorphismByImages(U,W,
    GeneratorsOfGroup(U),List([1..Size(GeneratorsOfGroup(W))],i->W.i));
  T:=List([1..Size(GeneratorsOfGroup(W))],i->W.i^-1*tau(C[i]));
  Rels:=Concatenation(Rels,T);
  return W/Rels;
end);

#   express presentation generators as words in standard generators
InstallGlobalFunction(PlusStandardToPresentation,
function(d,q)
local F,delta,delta1,s,s1,t,t1,u,v;
  Assert(1,IsEvenInt(d) and d > 4);
  F:=FreeGroup(8);
  s:=F.1;
  s1:=F.4;
  t:=F.2;
  delta:=F.3;
  t1:=F.5;
  delta1:=F.6;
  u:=F.7;
  v:=F.8;
  #   return presentation generators = [delta, sigma, Z, U, V]
  if IsOddInt(q) then
    return [delta1^-1,t1,s*s1,s1,v];
  else
    return [(delta*delta1)^(QuoInt((q-2),2)),t1,s*s1,s1,v];
  fi;
end);

#   express standard generators as words in presentation generators
InstallGlobalFunction(PlusPresentationToStandard,
function(d,q)
local U,V,W,varZ,delta,sigma,w1,w3,w6;
  Assert(1,IsEvenInt(d) and d > 4);
  W:=FreeGroup(5);
  delta:=W.1;
  sigma:=W.2;
  varZ:=W.3;
  U:=W.4;
  V:=W.5;
  # rewritten select statement
  if IsEvenInt(q) then
    w1:=varZ*U;
  else
    w1:=varZ*U^-1;
  fi;
  # rewritten select statement
  if IsEvenInt(q) then
    w3:=delta^-1*(delta^-1)^U;
  else
    w3:=delta^(varZ^(V^-1));
  fi;
  # rewritten select statement
  if IsEvenInt(q) then
    w6:=(delta*(delta^varZ)^U)^-1;
  else
    w6:=delta^-1;
  fi;
  #   return standard generators = [s, t, delta, s', t', delta', u, v]
  return [w1,(sigma^-1)^(varZ^V),w3,W.4,W.2,w6,W.0,W.5];
end);

#   generator of centre as word in presentation generators
InstallGlobalFunction(PlusGeneratorOfCentre,
function(d,q,F)
local lvarDelta,V,varZ,n,z;
  Assert(1,IsEvenInt(d) and d > 2);
  n:=QuoInt(d,2);
  if q^n mod 4=1 then
    lvarDelta:=F.1;
    varZ:=F.3;
    V:=F.5;
    if IsEvenInt(n) then
      z:=V^n;
    else
      z:=(V*varZ*lvarDelta)^(QuoInt(n*(q-1),4));
    fi;
  else
     # TODO Not sure it is correct
    # was "z:=F.0;"
    z:=Identity(F);
  fi;
  return z;
end);
