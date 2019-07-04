#  File converted from Magma code -- requires editing and checking
#  Magma -> GAP converter, version 0.5, 11/5/18 by AH

#  Global Variables used: Append, ClassicalStandardGenerators, Factorial, GF,
#  Integers, IsEven, IsOdd, IsPrimePower, LHS, Log, PrimitiveElement, RHS,
#  SLPGroup, SU_PresentationForN, Thm71, Thm72, eta, phi, tau

#  Defines: EvenSUGenerators, EvenSUPresentation, OrderSU_N, OrderThm71,
#  OrderThm72, SU_PresentationForN, Thm71, Thm72

#   this agrees with paper definition of psi
EvenSUGenerators:=function(d,q)
local Delta,S,T,U,V,varZ,delta,sigma,tau;
  Assert(1,IsEvenInt(d));
  S:=ClassicalStandardGenerators("SU",d,q);
  varZ:=S[1];
  varZ:=varZ^-1;
  V:=S[2];
  tau:=S[3];
  tau:=tau^-1;
  delta:=S[4];
  delta:=delta^-1;
  U:=S[5];
  sigma:=S[6];
  sigma:=sigma^(V^2);
  lvarDelta:=S[7]^(V^2);
  lvarDelta:=lvarDelta^-1;
  T:=[varZ,V,tau,delta,U,sigma,lvarDelta];
  return T;
end;

Thm71:=function(n,q)
local Delta,F,OMIT,R,Rels,S,U,V,tau;
  Rels:=[];
  if n=2 then
    F:=SLPGroup(2);
    lvarDelta:=F.1;
    U:=F.2;
    R:=[];
    Append(TILDERels,U^2=1);
  else
    F:=SLPGroup(3);
    lvarDelta:=F.1;
    U:=F.2;
    V:=F.3;
    # =v= MULTIASSIGN =v=
    R:=PresentationForSn(n);
    S:=R.val1;
    R:=R.val2;
    # =^= MULTIASSIGN =^=
    tau:=GroupHomomorphismByImages(S,F,
      GeneratorsOfGroup(S),
      [U,V]);
    R:=List(R,r->tau(r));
    if n > 3 then
      Append(TILDERels,Tuple([lvarDelta,U^(V^2)])=1);
      Append(TILDERels,Tuple([lvarDelta,lvarDelta^(V^2)])=1);
    fi;
    if n > 4 then
      Append(TILDERels,Tuple([lvarDelta,V*U*U^V])=1);
    fi;
    Append(TILDERels,lvarDelta*lvarDelta^V=lvarDelta^(V*U));
    Append(TILDERels,Tuple([lvarDelta,lvarDelta^V])=1);
  fi;
  OMIT:=true;
  if not OMIT then
    Append(TILDERels,lvarDelta^U=lvarDelta^-1);
    Append(TILDERels,lvarDelta^(q^2-1)=1);
  fi;
  Rels:=Concatenation(List(Rels,r->LHS(r)*RHS(r)^-1),R);
  return rec(val1:=F,
    val2:=Rels);
end;

OrderThm71:=function(n,q)
return (q^2-1)^(n-1)*Factorial(n);
end;

Thm72:=function(n,q)
local Delta,F,OMIT,R,Rels,S,U,V,delta,tau;
  F:=SLPGroup(4);
  lvarDelta:=F.1;
  U:=F.2;
  V:=F.3;
  delta:=F.4;
  Rels:=[];
  # =v= MULTIASSIGN =v=
  R:=Thm71(n,q);
  S:=R.val1;
  R:=R.val2;
  # =^= MULTIASSIGN =^=
  if n=2 then
    Append(TILDERels,U=V);
    tau:=GroupHomomorphismByImages(S,F,
      GeneratorsOfGroup(S),
      [lvarDelta,U]);
  else
    tau:=GroupHomomorphismByImages(S,F,
      GeneratorsOfGroup(S),
      [lvarDelta,U,V]);
  fi;
  R:=List(R,r->tau(r));
  OMIT:=true;
  if not OMIT then
    Append(TILDERels,delta^(q-1)=1);
  fi;
  if n > 2 then
    Append(TILDERels,Tuple([delta,U^V])=1);
    Append(TILDERels,Tuple([delta,lvarDelta^V])=1);
  fi;
  Append(TILDERels,Tuple([delta,lvarDelta])=1);
  if n > 3 then
    Append(TILDERels,Tuple([delta,V*U])=1);
  fi;
  Append(TILDERels,lvarDelta^(q+1)=delta*(delta^-1)^U);
  Rels:=Concatenation(List(Rels,r->LHS(r)*RHS(r)^-1),R);
  return rec(val1:=F,
    val2:=Rels);
end;

OrderThm72:=function(n,q)
return (q-1)*(q^2-1)^(n-1)*Factorial(n);
end;

SU_PresentationForN:=function(n,q)
local Delta,F,OMIT,R,Rels,S,U,V,varZ,delta,tau;
  F:=SLPGroup(5);
  lvarDelta:=F.1;
  U:=F.2;
  V:=F.3;
  delta:=F.4;
  varZ:=F.5;
  # =v= MULTIASSIGN =v=
  R:=Thm72(n,q);
  S:=R.val1;
  R:=R.val2;
  # =^= MULTIASSIGN =^=
  tau:=GroupHomomorphismByImages(S,F,
    GeneratorsOfGroup(S),
    [lvarDelta,U,V,delta]);
  R:=List(R,r->tau(r));
  Rels:=[];
  OMIT:=true;
  if not OMIT then
    if IsOddInt(q) then
      Append(TILDERels,varZ^2=delta^(QuoInt((q-1),2)));
    else
      Append(TILDERels,varZ^2=1);
    fi;
    Append(TILDERels,delta^varZ=delta^-1);
  fi;
  if n > 2 then
    Append(TILDERels,Tuple([varZ,U^V])=1);
    Append(TILDERels,Tuple([varZ,lvarDelta^V])=1);
  fi;
  if n > 3 then
    Append(TILDERels,Tuple([varZ,V*U])=1);
  fi;
  Append(TILDERels,Tuple([varZ,varZ^U])=1);
  Append(TILDERels,delta=Tuple([lvarDelta^-1,varZ]));
  if n=2 then
    Append(TILDERels,Tuple([delta,varZ^U])=1);
  fi;
  Rels:=Concatenation(List(Rels,r->LHS(r)*RHS(r)^-1),R);
  return rec(val1:=F,
    val2:=Rels);
end;

OrderSU_N:=function(n,q)
return 2^n*(q-1)*(q^2-1)^(n-1)*Factorial(n);
end;

EvenSUPresentation:=function(d,q)
local 
   Delta,varE,F,I,OMIT,R,R1,R2,R3,R4,Rels,S,U,V,W,varZ,a,delta,e,eta,f,m,n,p,
   phi,sigma,tau,w,w0,x,y;
  Assert(1,IsPrimePower(q));
  Assert(1,IsEvenInt(d) and d > 2);
  n:=QuoInt(d,2);
  # =v= MULTIASSIGN =v=
  e:=IsPrimePower(q);
  f:=e.val1;
  p:=e.val2;
  e:=e.val3;
  # =^= MULTIASSIGN =^=
  F:=SLPGroup(7);
  varZ:=F.1;
  V:=F.2;
  tau:=F.3;
  delta:=F.4;
  U:=F.5;
  sigma:=F.6;
  lvarDelta:=F.7;
  R:=[];
  # =v= MULTIASSIGN =v=
  R4:=SU_PresentationForN(n,q);
  S:=R4.val1;
  R4:=R4.val2;
  # =^= MULTIASSIGN =^=
  eta:=GroupHomomorphismByImages(S,F,
    GeneratorsOfGroup(S),
    [lvarDelta,U,V,delta,varZ]);
  R4:=List(R4,r->eta(r));
  #   centraliser of sigma
  if n > 3 then
    Append(TILDER,Tuple([U^(V^2),sigma])=1);
  fi;
  if n > 4 then
    Append(TILDER,Tuple([V*U*U^V,sigma])=1);
  fi;
  if n > 3 and IsOddInt(q) then
    Append(TILDER,Tuple([lvarDelta^(V^2),sigma])=1);
  fi;
  if n=3 and IsOddInt(q) then
    Append(TILDER,Tuple([delta^(V^2),sigma])=1);
  fi;
  if n > 2 then
    Append(TILDER,Tuple([varZ^(V^2),sigma])=1);
    Append(TILDER,Tuple([lvarDelta*(lvarDelta^2)^V,sigma])=1);
  fi;
  if n=2 then
    if IsEvenInt(q) then
      Append(TILDER,Tuple([delta*delta^U,sigma])=1);
    else
      Append(TILDER,Tuple([lvarDelta^(QuoInt((q+1),2))*delta^-1,sigma])=1);
    fi;
  fi;
  Append(TILDER,Tuple([varZ*U*varZ^-1,sigma])=1);
  #   centraliser of tau
  if n > 2 then
    Append(TILDER,Tuple([U^V,tau])=1);
  fi;
  if n=2 and IsOddInt(q) then
    Append(TILDER,Tuple([delta^U,tau])=1);
  fi;
  if n > 2 then
    Append(TILDER,Tuple([lvarDelta^V,tau])=1);
  fi;
  #   V*U is needed to generate centraliser of tau but relation not needed
  OMIT:=true;
  if not OMIT then
    if n > 3 then
      Append(TILDER,Tuple([V*U,tau])=1);
    fi;
  fi;
  Append(TILDER,Tuple([varZ^U,tau])=1);
  Append(TILDER,Tuple([lvarDelta^2*delta^-1,tau])=1);
  # =v= MULTIASSIGN =v=
  R1:=PresentationForSL2(p,e);
  S:=R1.val1;
  R1:=R1.val2;
  # =^= MULTIASSIGN =^=
  if e=1 then
    phi:=GroupHomomorphismByImages(S,F,
      GeneratorsOfGroup(S),
      [tau,varZ]);
    #   need to express delta as word in <tau, Z> = SL(2, p)
    w:=PrimitiveElement(GF(p));
    I:=Integers();
    x:=(w^-1)*FORCEOne(I)-1;
    y:=(w^-2-w^-1)*FORCEOne(I);
    Append(TILDER,delta=tau^-1*(tau^x)^varZ*tau^(w*FORCEOne(I))*(tau^-y)^varZ);
  else
    phi:=GroupHomomorphismByImages(S,F,
      GeneratorsOfGroup(S),
      [delta,tau,varZ]);
  fi;
  R1:=List(R1,r->phi(r));
  # rewritten select statement
  if IsEvenInt(q) then
    W:=U;
  else
    W:=U*varZ^2;
  fi;
  # =v= MULTIASSIGN =v=
  R2:=PresentationForSL2(p,2*e);
  S:=R2.val1;
  R2:=R2.val2;
  # =^= MULTIASSIGN =^=
  phi:=GroupHomomorphismByImages(S,F,
    GeneratorsOfGroup(S),
    [lvarDelta,sigma,W]);
  R2:=List(R2,r->phi(r));
  #   Steinberg relations
  R3:=[];
  Append(TILDER3,Tuple([sigma,tau])=1);
  if IsEvenInt(q) then
    Append(TILDER3,Tuple([sigma,sigma^varZ])=1);
  else
    Append(TILDER3,Tuple([sigma,sigma^varZ])=(tau^2)^(varZ*U));
  fi;
  if (q<>3) then
    varE:=GF(q^2);
    # Implicit generator Assg from previous line.
    w:=varE.1;
    w0:=w^(q+1);
    a:=w^(2*q)+w^2;
    m:=Log(w0,a);
    Append(TILDER3,Tuple([sigma^lvarDelta,sigma^varZ])=tau^(varZ*U*lvarDelta^m))
     ;
  else
    Append(TILDER3,Tuple([sigma^lvarDelta,sigma^varZ])=1);
  fi;
  Append(TILDER3,Tuple([sigma,tau^varZ])=sigma^varZ*(tau^-1)^(varZ*U));
  #   additional relation needed for SU(6, 2) -- probably only #2 required
  if (n=3 and q=2) then
    Append(TILDER3,Tuple([sigma,sigma^(U^V*lvarDelta)])=1);
    Append(TILDER3,Tuple([sigma,sigma^(V*lvarDelta)])=sigma^(V*U*lvarDelta^-1))
     ;
  fi;
  if n > 2 then
    Append(TILDER3,Tuple([sigma,sigma^(U^V)])=1);
    Append(TILDER3,Tuple([sigma,sigma^V])=sigma^(V*U));
  fi;
  if n < 4 then
    Append(TILDER3,Tuple([tau,tau^U])=1);
  fi;
  if n=3 then
    Append(TILDER3,Tuple([tau,sigma^V])=1);
  fi;
  if n > 3 then
    Append(TILDER3,Tuple([sigma,sigma^(V^2)])=1);
  fi;
  if n=2 and q=3 then
    Append(TILDER3,tau=Tuple([(sigma^-1)^(U*varZ),sigma])^lvarDelta);
  fi;
  Rels:=Concatenation(List(Concatenation(R,R3),r->LHS(r)*RHS(r)^-1),R1,R2,R4);
  return rec(val1:=F,
    val2:=Rels);
end;


