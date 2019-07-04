#  File converted from Magma code -- requires editing and checking
#  Magma -> GAP converter, version 0.5, 11/5/18 by AH

#  Global Variables used: Append, ClassicalStandardGenerators, DiagonalMatrix,
#  Factorial, GF, GL, Identity, InsertBlock, IsEven, IsOdd, IsPrimePower, LHS,
#  Log, MatrixAlgebra, Odd_SU_PresentationForN, PrimitiveElement, RHS,
#  SLPGroup, Trace, Zero, phi, tau

#  Defines: OddSUGenerators, OddSUPresentation, Odd_SU_PresentationForN,
#  Order_Odd_SU_N

OddSUGenerators:=function(d,q)
local F,Gamma,MA,S,U,V,alpha,gamma,i,phi,psi,sigma,t,tau,v,w,x;
  Assert(1,IsOddInt(d));
  MA:=MatrixAlgebra(GF(q^2),d);
  F:=GF(q^2);
  w:=PrimitiveElement(F);
  #   define tau
  tau:=Identity(MA);
  # rewritten select statement
  if IsEvenInt(q) then
    psi:=1;
  else
    psi:=w^(QuoInt((q+1),2));
  fi;
  tau[1][2]:=-psi;
  #   define Gamma
  lvarGamma:=Concatenation([w^-1,w^q],List([3..d-1],i->1),[w^(1-q)]);
  lvarGamma:=DiagonalMat(lvarGamma);
  #   define t
  t:=Zero(MA);
  t[1][2]:=1;
  t[2][1]:=1;
  t[d][d]:=-1;
  for i in [3..d-1] do
    t[i][i]:=1;
  od;
  #   define v
  alpha:=1;
  if IsEvenInt(q) then
    phi:=Trace(w,GF(q))^(-1)*w;
    Assert(1,phi=w/(w+w^q));
  else
    phi:=-1/2;
  fi;
  gamma:=phi*alpha^(1+q);
  v:=Zero(MA);
  v[1][1]:=1;
  v[1][2]:=gamma;
  v[1][d]:=alpha;
  for i in [2..d] do
    v[i][i]:=1;
  od;
  v[d][2]:=-alpha^q;
  #   U and V
  S:=ClassicalStandardGenerators("SU",d,q);
  U:=S[5];
  V:=S[2];
  S:=ClassicalStandardGenerators("SU",d-1,q);
  x:=S[6]^(S[2]^2);
  sigma:=Zero(MA);
  InsertBlock(TILDEsigma,x,1,1);
  sigma[d][d]:=1;
  return [lvarGamma,t,U,V,sigma,tau,v];
end;

Odd_SU_PresentationForN:=function(n,q)
local F,Gamma,OMIT,R,Rels,S,U,V,t,tau;
  F:=SLPGroup(4);
  lvarGamma:=F.1;
  t:=F.2;
  U:=F.3;
  V:=F.4;
  Rels:=[];
  # =v= MULTIASSIGN =v=
  R:=PresentationForSn(n);
  S:=R.val1;
  R:=R.val2;
  # =^= MULTIASSIGN =^=
  tau:=GroupHomomorphismByImages(S,F,
    GeneratorsOfGroup(S),
    [U,V]);
  R:=List(R,r->tau(r));
  OMIT:=true;
  if not OMIT then
    Append(TILDERels,lvarGamma^(q^2-1)=1);
    Append(TILDERels,t^2=1);
    Append(TILDERels,lvarGamma^t=lvarGamma^-q);
  fi;
  if n > 2 then
    Append(TILDERels,Tuple([lvarGamma,U^V])=1);
    Append(TILDERels,Tuple([t,U^V])=1);
  fi;
  if n > 3 then
    Append(TILDERels,Tuple([lvarGamma,V*U])=1);
    Append(TILDERels,Tuple([t,V*U])=1);
  fi;
  Append(TILDERels,Tuple([lvarGamma,lvarGamma^U])=1);
  Append(TILDERels,Tuple([t,t^U])=1);
  Append(TILDERels,Tuple([lvarGamma,t^U])=1);
  Rels:=Concatenation(List(Rels,r->LHS(r)*RHS(r)^-1),R);
  return rec(val1:=F,
    val2:=Rels);
end;

Order_Odd_SU_N:=function(n,q)
local a;
  a:=(q^2-1)*2;
  return a^n*Factorial(n);
end;

OddSUPresentation:=function(d,q)
local 
   Delta,varE,F,Gamma,K,OMIT,Projective,Q,R,R3,R4,R_N,R_SL2,R_SU3,Rels,U,V,W,
   varZ,a,e,f,m,n,p,phi,r,rhs,sigma,t,tau,v,w,w0;
  Projective:=ValueOption("Projective");
  if Projective=fail then
    Projective:=false;
  fi;
  Assert(1,IsOddInt(d) and d >= 3);
  n:=QuoInt(d,2);
  if d=3 then
    if q=2 then
      return SU32Presentation(:Projective:=Projective);
    else
      return SU3Presentation(q);
    fi;
  fi;
  # =v= MULTIASSIGN =v=
  e:=IsPrimePower(q);
  f:=e.val1;
  p:=e.val2;
  e:=e.val3;
  # =^= MULTIASSIGN =^=
  K:=GF(q^2);
  w:=PrimitiveElement(K);
  F:=SLPGroup(7);
  lvarGamma:=F.1;
  t:=F.2;
  U:=F.3;
  V:=F.4;
  sigma:=F.5;
  tau:=F.6;
  v:=F.7;
  lvarDelta:=lvarGamma*(lvarGamma^-1)^U;
  R:=[];
  #   centraliser of v
  if n > 2 then
    Append(TILDER,Tuple([U^V,v])=1);
  fi;
  if n > 3 then
    Append(TILDER,Tuple([V*U,v])=1);
  fi;
  if IsEvenInt(q) then
    Append(TILDER,Tuple([t^U,v])=1);
  else
    m:=QuoInt((q^2-1),2);
    Append(TILDER,Tuple([t^U*lvarDelta^m,v])=1);
  fi;
  if n=2 and q mod 3=1 then
    Append(TILDER,Tuple([lvarGamma^(q-1)*(lvarGamma^U)^3*Tuple([t,lvarGamma^-1])
     ^U,v])=1);
  else
    Append(TILDER,Tuple([lvarGamma^(q-1)*(lvarGamma^U)^3,v])=1);
  fi;
  if n > 2 then
    Append(TILDER,Tuple([lvarGamma^U*(lvarGamma^-1)^(V^2),v])=1);
  fi;
  if IsEvenInt(q) then
    varZ:=t;
  else
    varZ:=t*lvarGamma^(QuoInt((q+1),2));
  fi;
  #   centraliser of sigma
  OMIT:=true;
  if not OMIT then
    if n > 3 then
      Append(TILDER,Tuple([U^(V^2),sigma])=1);
    fi;
    if n > 4 then
      Append(TILDER,Tuple([V*U*U^V,sigma])=1);
    fi;
    if n > 2 then
      Append(TILDER,Tuple([lvarGamma^(V^2),sigma])=1);
      Append(TILDER,Tuple([t^(V^2),sigma])=1);
    fi;
  fi;
  if IsEvenInt(q) then
    Append(TILDER,Tuple([U^t,sigma])=1);
  else
    Append(TILDER,Tuple([U^t*varZ^2,sigma])=1);
  fi;
  Append(TILDER,Tuple([lvarGamma*lvarGamma^U,sigma])=1);
  # =v= MULTIASSIGN =v=
  lvarR_N:=Odd_SU_PresentationForN(n,q);
  Q:=lvarR_N.val1;
  lvarR_N:=lvarR_N.val2;
  # =^= MULTIASSIGN =^=
  phi:=GroupHomomorphismByImages(Q,F,
    GeneratorsOfGroup(Q),
    [lvarGamma,t,U,V]);
  lvarR_N:=List(lvarR_N,r->phi(r));
  #   tau = tau^-1 in char 2
  # =v= MULTIASSIGN =v=
  R_SU3:=SU3Presentation(q);
  Q:=R_SU3.val1;
  R_SU3:=R_SU3.val2;
  # =^= MULTIASSIGN =^=
  if q=2 then
    phi:=GroupHomomorphismByImages(Q,F,
      GeneratorsOfGroup(Q),
      [v,v^(lvarGamma^U),lvarGamma^-1,t]);
  else
    phi:=GroupHomomorphismByImages(Q,F,
      GeneratorsOfGroup(Q),
      [v,tau^-1,lvarGamma^-1,t]);
  fi;
  R_SU3:=List(R_SU3,r->phi(r));
  # =v= MULTIASSIGN =v=
  R_SL2:=PresentationForSL2(p,2*e);
  Q:=R_SL2.val1;
  R_SL2:=R_SL2.val2;
  # =^= MULTIASSIGN =^=
  # rewritten select statement
  if IsEvenInt(q) then
    W:=U;
  else
    W:=U*varZ^2;
  fi;
  phi:=GroupHomomorphismByImages(Q,F,
    GeneratorsOfGroup(Q),
    [lvarDelta,sigma,W]);
  R_SL2:=List(R_SL2,r->phi(r));
  #   Steinberg relations
  R4:=[];
  Append(TILDER4,Tuple([v,v^U])=(sigma^-1)^(t^U));
  if q=4 then
    Append(TILDER4,Tuple([v,v^(lvarGamma*U)])=sigma^(lvarGamma^7*t^U));
    Append(TILDER4,Tuple([v^lvarGamma,sigma])=1);
  fi;
  Append(TILDER4,Tuple([v,sigma])=1);
  if IsOddInt(q) then
    a:=(w^(QuoInt(-(q+1),2)))/2;
    r:=Log(a);
    rhs:=sigma^(lvarGamma^r*varZ^U)*(v^-1)^U;
  else
    a:=w^q/(w+w^q);
    r:=Log(a);
    rhs:=sigma^(lvarGamma^r*varZ^U)*(v^U);
  fi;
  Append(TILDER4,Tuple([v,sigma^U])=rhs);
  if q=2 then
    Append(TILDER4,Tuple([v,sigma^(lvarGamma*U)])=sigma^(lvarGamma*varZ^U)
     *v^(U^(lvarGamma^-1)));
  fi;
  if n > 2 then
    Append(TILDER4,Tuple([v,sigma^V])=1);
  fi;
  Append(TILDER4,Tuple([v,tau^U])=1);
  #   Steinberg relations for SU(2n, q)
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
  Rels:=Concatenation(List(Concatenation(R,R3,R4),r->LHS(r)*RHS(r)^-1)
   ,R_SU3,R_SL2,lvarR_N);
  return rec(val1:=F,
    val2:=Rels);
end;


