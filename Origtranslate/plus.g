#  File converted from Magma code -- requires editing and checking
#  Magma -> GAP converter, version 0.5, 11/5/18 by AH

#  Global Variables used: Append, ClassicalStandardGenerators,
#  ClassicalStandardPresentation, Evaluate, EvenPlus,
#  EvenPlus_PresentationForN, EvenPlus_PresentationForN1, Factorial, GF, GL,
#  Id, Identity, Integers, IsEven, IsOdd, IsPrime, IsPrimePower, LHS,
#  MatrixAlgebra, Ngens, OddPlus, OddPlusGenerators, OddPlus_PresentationForN,
#  OddPlus_PresentationForN1, OmegaPlus4, PlusConvertToStandard,
#  PlusGeneratorOfCentre, PlusPresentationToStandard,
#  PlusStandardToPresentation, PrimitiveElement, RHS, SLPGroup, Universe, phi,
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
local F,Projective,R,S,T,Y,d,d1,gens,rels,s,s1,t,t1,v,x,y;
  Projective:=ValueOption("Projective");
  if Projective=fail then
    Projective:=false;
  fi;
  F:=SLPGroup(8);
  d:=4;
  s:=F.1;
  s1:=F.4;
  t:=F.2;
  t1:=F.5;
  d:=F.3;
  d1:=F.6;
  v:=F.8;
  #   one of the standard generators is the identity
  rels:=[F.7=1];
  #   sl2 presentation on s, t, d
  # =v= MULTIASSIGN =v=
  S:=ClassicalStandardPresentation("SL",2,q);
  Y:=S.val1;
  S:=S.val2;
  # =^= MULTIASSIGN =^=
  gens:=[s,s,t,d,s^0,s^0,s^0,s^0];
  T:=Evaluate(S,gens);
  rels:=Concatenation(rels,List(T,t->t=One(F)));
  #   sl2 presentation on s1, t1, d1
  gens:=[s1,s1,t1,d1,s1^0,s1^0,s1^0,s1^0];
  T:=Evaluate(S,gens);
  rels:=Concatenation(rels,List(T,t->t=One(F)));
  for x in [s,t,d] do
    for y in [s1,t1,d1] do
      Append(TILDErels,Tuple([x,y])=1);
    od;
  od;
  Append(TILDErels,v=s1);
  Append(TILDErels,s^2=s1^2);
  if Projective and IsOddInt(q) then
    Append(TILDErels,F.3^(QuoInt((q-1),2)));
  fi;
  R:=List(rels,r->LHS(r)*RHS(r)^-1);
  return rec(val1:=F,
    val2:=List(R,r->r));
end;

OddPlusGenerators:=function(d,q)
local Delta,varE,F,MA,U,V,varZ,gens,sigma,w;
  F:=GF(q);
  MA:=MatrixAlgebra(F,d);
  varZ:=Identity(MA);
  varZ[1][1]:=0;
  varZ[1][2]:=1;
  varZ[2][1]:=1;
  varZ[2][2]:=0;
  varZ[3][4]:=1;
  varZ[4][3]:=1;
  varZ[3][3]:=0;
  varZ[4][4]:=0;
  w:=PrimitiveElement(F);
  lvarDelta:=Identity(MA);
  lvarDelta[1][1]:=w^-1;
  lvarDelta[2][2]:=w;
  lvarDelta[3][3]:=w^1;
  lvarDelta[4][4]:=w^-1;
  lvarDelta:=lvarDelta*FORCEOne(GL(d,F));
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
  MA:=MatrixAlgebra(F,d);
  w:=PrimitiveElement(F);
  delta:=Identity(MA);
  delta[1][1]:=w^-1;
  delta[2][2]:=w;
  varE:=ClassicalStandardGenerators("Omega+",d,q);
  sigma:=varE[5];
  U:=varE[4];
  V:=varE[8];
  varZ:=Identity(MA);
  varZ[1][1]:=0;
  varZ[1][2]:=1;
  varZ[2][1]:=1;
  varZ[2][2]:=0;
  varZ:=varZ*FORCEOne(GL(d,q));
  varZ:=varZ*varZ^U;
  gens:=[delta,sigma,varZ,U,V];
  return gens;
end;

#   infrastructure for OmegaPlus (2n, q) where q is even
EvenPlus_PresentationForN1:=function(n,q)
local F,R,R1,Rels,S,U,V,varZ,e,f,p,phi;
  # =v= MULTIASSIGN =v=
  e:=IsPrimePower(q);
  f:=e.val1;
  p:=e.val2;
  e:=e.val3;
  # =^= MULTIASSIGN =^=
  F:=SLPGroup(3);
  U:=F.1;
  V:=F.2;
  varZ:=F.3;
  # =v= MULTIASSIGN =v=
  R1:=PresentationForSn(n);
  S:=R1.val1;
  R1:=R1.val2;
  # =^= MULTIASSIGN =^=
  phi:=GroupHomomorphismByImages(S,F,
    GeneratorsOfGroup(S),
    [U,V]);
  R1:=List(R1,r->phi(r));
  R:=[];
  if n > 3 then
    Append(TILDER,Tuple([varZ,U^(V^2)])=1);
    Append(TILDER,Tuple([varZ,varZ^(V^2)])=1);
  fi;
  if n > 4 then
    Append(TILDER,Tuple([varZ,V*U*U^V])=1);
  fi;
  Append(TILDER,Tuple([varZ,varZ^V])=1);
  Append(TILDER,varZ*varZ^V=varZ^(U^V));
  Append(TILDER,varZ^2=1);
  Append(TILDER,Tuple([varZ,U])=1);
  Rels:=Concatenation(List(R,r->LHS(r)*RHS(r)^-1),R1);
  return rec(val1:=F,
    val2:=Rels);
end;

#   infrastructure for OmegaPlus (2n, q) where q is even
EvenPlus_PresentationForN:=function(n,q)
local F,R,R1,Rels,S,U,V,varZ,delta,e,f,p,phi;
  # =v= MULTIASSIGN =v=
  e:=IsPrimePower(q);
  f:=e.val1;
  p:=e.val2;
  e:=e.val3;
  # =^= MULTIASSIGN =^=
  F:=SLPGroup(4);
  U:=F.1;
  V:=F.2;
  varZ:=F.3;
  delta:=F.4;
  # =v= MULTIASSIGN =v=
  R1:=EvenPlus_PresentationForN1(n,q);
  S:=R1.val1;
  R1:=R1.val2;
  # =^= MULTIASSIGN =^=
  phi:=GroupHomomorphismByImages(S,F,
    GeneratorsOfGroup(S),
    [U,V,varZ]);
  R1:=List(R1,r->phi(r));
  R:=[];
  Append(TILDER,Tuple([delta,U^V])=1);
  if n > 3 then
    Append(TILDER,Tuple([delta,V*U])=1);
  fi;
  Append(TILDER,Tuple([delta,delta^U])=1);
  Append(TILDER,delta^(q-1)=1);
  Append(TILDER,delta^varZ=delta^-1);
  Append(TILDER,Tuple([delta,varZ^V])=1);
  Rels:=Concatenation(List(R,r->LHS(r)*RHS(r)^-1),R1);
  return rec(val1:=F,
    val2:=Rels);
end;

EvenPlus_OrderN:=function(n,q)
return QuoInt((2*(q-1))^n*Factorial(n),2);
end;

#   presentation for OmegaPlus (2n, q) where q is even
EvenPlus:=function(d,q)
local Delta,F,R1,R2,R3,R4,Rels,S,U,V,W,varZ,delta,e,f,n,p,phi,sigma,w;
  Assert(1,IsEvenInt(d));
  Assert(1,IsEvenInt(q));
  n:=QuoInt(d,2);
  Assert(1,n > 2);
  F:=GF(q);
  w:=PrimitiveElement(F);
  # =v= MULTIASSIGN =v=
  e:=IsPrimePower(q);
  f:=e.val1;
  p:=e.val2;
  e:=e.val3;
  # =^= MULTIASSIGN =^=
  F:=SLPGroup(5);
  delta:=F.1;
  sigma:=F.2;
  varZ:=F.3;
  U:=F.4;
  V:=F.5;
  if e=1 then
    # =v= MULTIASSIGN =v=
    R1:=EvenPlus_PresentationForN1(n,q);
    S:=R1.val1;
    R1:=R1.val2;
    # =^= MULTIASSIGN =^=
    phi:=GroupHomomorphismByImages(S,F,
      GeneratorsOfGroup(S),
      [U,V,varZ]);
  else
    # =v= MULTIASSIGN =v=
    R1:=EvenPlus_PresentationForN(n,q);
    S:=R1.val1;
    R1:=R1.val2;
    # =^= MULTIASSIGN =^=
    phi:=GroupHomomorphismByImages(S,F,
      GeneratorsOfGroup(S),
      [U,V,varZ,delta]);
  fi;
  R1:=List(R1,r->phi(r));
  Rels:=[];
  # =v= MULTIASSIGN =v=
  R2:=PresentationForSL2(p,e);
  S:=R2.val1;
  R2:=R2.val2;
  # =^= MULTIASSIGN =^=
  if e=1 then
    phi:=GroupHomomorphismByImages(S,F,
      GeneratorsOfGroup(S),
      [sigma,U]);
    Append(TILDERels,delta=1);
  else
    lvarDelta:=delta*(delta^-1)^U;
    phi:=GroupHomomorphismByImages(S,F,
      GeneratorsOfGroup(S),
      [lvarDelta,sigma,U]);
  fi;
  R2:=List(R2,r->phi(r));
  #   centraliser of sigma
  R3:=[];
  if e > 1 then
    Append(TILDER3,Tuple([sigma,delta*delta^U])=1);
    Append(TILDER3,Tuple([sigma,delta^(V^2)])=1);
  fi;
  Append(TILDER3,Tuple([sigma,varZ*U])=1);
  if n > 3 then
    Append(TILDER3,Tuple([sigma,U^(V^2)])=1);
  fi;
  if n > 4 then
    Append(TILDER3,Tuple([sigma,V*U*U^V])=1);
  fi;
  if n > 3 then
    Append(TILDER3,Tuple([sigma,varZ^(V^2)])=1);
  fi;
  #   Steinberg relations
  R4:=[];
  Append(TILDER4,Tuple([sigma,sigma^V])=sigma^(V*U));
  Append(TILDER4,Tuple([sigma,sigma^(V*U)])=1);
  W:=U^(V*U);
  Append(TILDER4,Tuple([sigma,sigma^W])=1);
  if n > 3 then
    Append(TILDER4,Tuple([sigma,sigma^(V^2)])=1);
  fi;
  Append(TILDER4,Tuple([sigma,sigma^(varZ^V)])=1);
  if n=4 then
    Append(TILDER4,Tuple([sigma,sigma^(varZ^V*V^2)])=1);
  fi;
  Rels:=Concatenation(List(Concatenation(Rels,R3,R4),r->LHS(r)*RHS(r)^-1),R1,R2)
   ;
  return rec(val1:=F,
    val2:=Rels);
end;

#   infrastructure for OmegaPlus (2n, q) where q is odd
OddPlus_PresentationForN1:=function(n,q)
local F,R,R1,Rels,S,U,V,varZ,e,f,p,phi,w;
  F:=GF(q);
  w:=PrimitiveElement(F);
  # =v= MULTIASSIGN =v=
  e:=IsPrimePower(q);
  f:=e.val1;
  p:=e.val2;
  e:=e.val3;
  # =^= MULTIASSIGN =^=
  F:=SLPGroup(3);
  varZ:=F.1;
  U:=F.2;
  V:=F.3;
  # =v= MULTIASSIGN =v=
  R:=SignedPermutations(n);
  S:=R.val1;
  R:=R.val2;
  # =^= MULTIASSIGN =^=
  phi:=GroupHomomorphismByImages(S,F,
    GeneratorsOfGroup(S),
    [U,V]);
  R:=List(R,r->phi(r));
  R1:=[];
  if n > 3 then
    Append(TILDER1,Tuple([varZ,U^(V^2)])=1);
    Append(TILDER1,Tuple([varZ,varZ^(V^2)])=1);
  fi;
  if n > 4 then
    Append(TILDER1,Tuple([varZ,V*U*U^V])=1);
  fi;
  Append(TILDER1,varZ^2=1);
  Append(TILDER1,Tuple([varZ,(U^2)^V])=1);
  if n > 2 then
    Append(TILDER1,varZ*varZ^V=varZ^(V*U));
  fi;
  Append(TILDER1,Tuple([varZ,U])=1);
  Append(TILDER1,Tuple([varZ,varZ^V])=1);
  Rels:=Concatenation(List(R1,r->LHS(r)*RHS(r)^-1),R);
  return rec(val1:=F,
    val2:=Rels);
end;

OddPlus_OrderN1:=function(n)
return 2^(2*n-2)*Factorial(n);
end;

#   infrastructure for OmegaPlus (2n, q) where q is odd
OddPlus_PresentationForN:=function(n,q)
local Delta,F,OMIT,R,R1,Rels,S,U,V,varZ,phi;
  Assert(1,n > 2);
  F:=SLPGroup(4);
  lvarDelta:=F.1;
  varZ:=F.2;
  V:=F.4;
  U:=F.3;
  # =v= MULTIASSIGN =v=
  R:=OddPlus_PresentationForN1(n,q);
  S:=R.val1;
  R:=R.val2;
  # =^= MULTIASSIGN =^=
  phi:=GroupHomomorphismByImages(S,F,
    GeneratorsOfGroup(S),
    [varZ,U,V]);
  R:=List(R,r->phi(r));
  R1:=[];
  if n > 3 then
    Append(TILDER1,Tuple([lvarDelta,U^(V^2)])=1);
    Append(TILDER1,Tuple([lvarDelta,varZ^(V^2)])=1);
    Append(TILDER1,Tuple([lvarDelta,lvarDelta^(V^2)])=1);
  fi;
  if n > 4 then
    Append(TILDER1,Tuple([lvarDelta,V*U*U^V])=1);
  fi;
  #   June 2018 change  -- replace by following
  #   Append (~R1, (Delta, Z * U) = 1);
  Append(TILDER1,lvarDelta^U=lvarDelta^-1);
  Append(TILDER1,Tuple([lvarDelta,(U^2)^V])=1);
  OMIT:=true;
  if not OMIT then
    Append(TILDER1,(lvarDelta^(QuoInt((q-1),2)))=U^2);
  fi;
  Append(TILDER1,lvarDelta*lvarDelta^(V)=lvarDelta^(V*U));
  Append(TILDER1,Tuple([lvarDelta,lvarDelta^V])=1);
  Append(TILDER1,lvarDelta^varZ=lvarDelta^-1);
  Rels:=Concatenation(List(R1,r->LHS(r)*RHS(r)^-1),R);
  return rec(val1:=F,
    val2:=Rels);
end;

OddPlus_OrderN:=function(n,q)
return (q-1)^n*2^(n-2)*Factorial(n);
end;

#   presentation for OmegaPlus (2n, q) where q is odd
OddPlus:=function(d,q)
local Delta,F,I,R1,R2,R3,R4,Rels,S,U,V,W,varZ,b,e,f,n,p,phi,sigma,w;
  Assert(1,IsEvenInt(d));
  Assert(1,IsOddInt(q));
  n:=QuoInt(d,2);
  Assert(1,n > 2);
  F:=GF(q);
  w:=PrimitiveElement(F);
  # =v= MULTIASSIGN =v=
  e:=IsPrimePower(q);
  f:=e.val1;
  p:=e.val2;
  e:=e.val3;
  # =^= MULTIASSIGN =^=
  F:=SLPGroup(5);
  lvarDelta:=F.1;
  sigma:=F.2;
  varZ:=F.3;
  V:=F.5;
  U:=F.4;
  Rels:=[];
  #   additional relation needed for q = p to express Delta as word in sigma
  #  and U
  if IsPrimeInt(q) then
    I:=Integers();
    b:=(1/w)*FORCEOne(I);
    w:=w*FORCEOne(I);
    Append(TILDERels,lvarDelta=(sigma^U)^(w-w^2)*sigma^(b)*(sigma^U)^((w-1))
     *sigma^-1);
  fi;
  if e=1 then
    # =v= MULTIASSIGN =v=
    R1:=OddPlus_PresentationForN1(n,q);
    S:=R1.val1;
    R1:=R1.val2;
    # =^= MULTIASSIGN =^=
    phi:=GroupHomomorphismByImages(S,F,
      GeneratorsOfGroup(S),
      [varZ,U,V]);
  else
    # =v= MULTIASSIGN =v=
    R1:=OddPlus_PresentationForN(n,q);
    S:=R1.val1;
    R1:=R1.val2;
    # =^= MULTIASSIGN =^=
    phi:=GroupHomomorphismByImages(S,F,
      GeneratorsOfGroup(S),
      [lvarDelta,varZ,U,V]);
  fi;
  R1:=List(R1,r->phi(r));
  # =v= MULTIASSIGN =v=
  R2:=PresentationForSL2(p,e);
  S:=R2.val1;
  R2:=R2.val2;
  # =^= MULTIASSIGN =^=
  if e=1 then
    phi:=GroupHomomorphismByImages(S,F,
      GeneratorsOfGroup(S),
      [sigma,U]);
  else
    phi:=GroupHomomorphismByImages(S,F,
      GeneratorsOfGroup(S),
      [lvarDelta,sigma,U]);
  fi;
  R2:=List(R2,r->phi(r));
  #   centraliser of sigma
  R3:=[];
  if n > 3 then
    Append(TILDER3,Tuple([sigma,U^(V^2)])=1);
  fi;
  if n > 4 then
    Append(TILDER3,Tuple([sigma,V*U^-1*(U^-1)^V])=1);
  fi;
  if n > 3 then
    Append(TILDER3,Tuple([sigma,varZ^(V^2)])=1);
  fi;
  if e > 1 then
    if n > 3 then
      Append(TILDER3,Tuple([sigma,lvarDelta^(V^2)])=1);
    fi;
    Append(TILDER3,Tuple([sigma,lvarDelta^(varZ^V)])=1);
    if n in Set([3,4]) then
      Append(TILDER3,Tuple([sigma,lvarDelta^(U^V)*lvarDelta^V])=1);
    fi;
  fi;
  Append(TILDER3,Tuple([sigma,varZ*U])=1);
  #   Steinberg relations
  R4:=[];
  Append(TILDER4,Tuple([sigma,sigma^V])=sigma^(V*U^-1));
  Append(TILDER4,Tuple([sigma,sigma^(V*U^-1)])=1);
  W:=U^(V*U^-1);
  Append(TILDER4,Tuple([sigma,sigma^W])=1);
  if n > 3 then
    Append(TILDER4,Tuple([sigma,sigma^(V^2)])=1);
  fi;
  Append(TILDER4,Tuple([sigma,sigma^(varZ^V)])=1);
  if n=4 then
    Append(TILDER4,Tuple([sigma,sigma^(varZ^V*V^2)])=1);
  fi;
  Rels:=Concatenation(List(Concatenation(Rels,R3,R4),r->LHS(r)*RHS(r)^-1),R1,R2)
   ;
  return rec(val1:=F,
    val2:=Rels);
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
    # =v= MULTIASSIGN =v=
    R:=EvenPlus(d,q);
    P:=R.val1;
    R:=R.val2;
    # =^= MULTIASSIGN =^=
  else
    # =v= MULTIASSIGN =v=
    R:=OddPlus(d,q);
    P:=R.val1;
    R:=R.val2;
    # =^= MULTIASSIGN =^=
  fi;
  n:=QuoInt(d,2);
  if Projective and q^n mod 4=1 then
    z:=PlusGeneratorOfCentre(d,q,P);
    R:=Concatenation(R,[z]);
  fi;
  if Presentation then
    return rec(val1:=P,
      val2:=R);
  fi;
  # =v= MULTIASSIGN =v=
  Rels:=PlusConvertToStandard(d,q,R);
  S:=Rels.val1;
  Rels:=Rels.val2;
  # =^= MULTIASSIGN =^=
  Rels:=Filtered(Rels,w->w<>w^0);
  return rec(val1:=S,
    val2:=Rels);
end;

#   relations are on presentation generators;
#  convert to relations on standard generators 
InstallGlobalFunction(PlusConvertToStandard,
function(d,q,Rels)
local A,B,C,Rels,T,U,W,tau;
  A:=PlusStandardToPresentation(d,q);
  Rels:=Evaluate(Rels,A);
  B:=PlusPresentationToStandard(d,q);
  C:=Evaluate(B,A);
  U:=Universe(C);
  W:=Universe(Rels);
  tau:=GroupHomomorphismByImages(U,W,
    GeneratorsOfGroup(U),List([1..Ngens(W)],i->W.i));
  T:=List([1..Ngens(W)],i->W.i^-1*tau(C[i]));
  Rels:=Concatenation(Rels,T);
  return rec(val1:=W,
    val2:=Rels);
end);

#   express presentation generators as words in standard generators 
InstallGlobalFunction(PlusStandardToPresentation,
function(d,q)
local F,delta,delta1,s,s1,t,t1,u,v;
  Assert(1,IsEvenInt(d) and d > 4);
  F:=SLPGroup(8);
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
  W:=SLPGroup(5);
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
local Delta,V,varZ,n,z;
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
    z:=F.0;
  fi;
  return z;
end);


