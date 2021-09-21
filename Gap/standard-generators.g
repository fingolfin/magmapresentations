#AH 7/19: commented out as unused
# #   function from Allan Steel
# find_quad_ext_prim:=function(K,L)
# #  /out:
# #  L must be a degree-2 extension of K, where #K = q.
# #  Return a primitive element alpha of L such that
# #  alpha^(q + 1) = PrimitiveElement(K).
# 
# local alpha,flag,q,w;
#   q:=Size(K);
#   Assert(1,Size(L)=q^2);
#   w:=PrimitiveElement(K);
#   repeat
#     # =v= MULTIASSIGN =v=
#     alpha:=NormEquation(L,w);
#     flag:=alpha.val1;
#     alpha:=alpha.val2;
#     # =^= MULTIASSIGN =^=
#     Assert(1,flag);
#     Assert(1,alpha^(q+1)=w);
#     
#   until IsPrimitive(alpha);
#   return alpha;
# end;

#   canonical basis for SL(d, q) 
BindGlobal("SLChosenElements@",function(G)
local F,M,P,a,b,d,delta,i,t,w;
  d:=DimensionOfMatrixGroup(G);
  F:=DefaultFieldOfMatrixGroup(G);
  w:=PrimitiveElement(F);
  a:=IdentityMat(d,F);
  a[1][1]:=0*One(F);
  a[1][2]:=1*One(F);
  a[2][1]:=-1*One(F);
  a[2][2]:=0*One(F);
  b:=Zero(M);
  for i in [2..d] do
    b[i][i-1]:=-1*One(F);
  od;
  b[1][d]:=1*One(F);
  #   if d eq 3 then b := b^-1; end if;
  t:=IdentityMat(d,F);
  t[1][2]:=1*One(F);
  delta:=IdentityMat(d,F);
  delta[1][1]:=w;
  delta[2][2]:=w^-1;
  a:=ImmutableMatrix(F,a);
  b:=ImmutableMatrix(F,b);
  t:=ImmutableMatrix(F,t);
  delta:=ImmutableMatrix(F,delta);
  return [a,b,t,delta];
end);

#   additional element to generate all of Sp 
BindGlobal("SpAdditionalElement@",function(F)
local I,M;
  I:=IdentityMat(4,F);
  I[2][3]:=1*One(F);
  I[4][1]:=1*One(F);
  I:=ImmutableMatrix(F,I);
  return I;
end);

#   canonical basis for Sp(d, q) 
BindGlobal("SpChosenElements@",function(G)
local F,M,P,a,b,d,delta,i,n,p,t,v,w;
  d:=DimensionOfMatrixGroup(G);
  F:=DefaultFieldOfMatrixGroup(G);
  w:=PrimitiveElement(F);
  a:=IdentityMat(d,F);
  a[1][1]:=0*One(F);
  a[1][2]:=1*One(F);
  a[2][1]:=-1*One(F);
  a[2][2]:=0*One(F);
  t:=IdentityMat(d,F);
  t[1][2]:=1*One(F);
  delta:=IdentityMat(d,F);
  delta[1][1]:=w;
  delta[2][2]:=w^-1;
  if d >= 4 then
    p:=NullMat(d,d,F);
    p[1][3]:=1*One(F);
    p[2][4]:=1*One(F);
    p[3][1]:=1*One(F);
    p[4][2]:=1*One(F);
    for i in [5..d] do
      p[i][i]:=1*One(F);
    od;
  else
    p:=IdentityMat(d,F);
  fi;
  if d >= 4 then
    b:=NulMat(d,d,F);
    n:=QuoInt(d,2);
    for i in [1,1+2..d-3] do
      b[i][i+2]:=1*One(F);
    od;
    b[d-1][1]:=1*One(F);
    for i in [2,2+2..d-2] do
      b[i][i+2]:=1*One(F);
    od;
    b[d][2]:=1*One(F);
  else
    b:=IdentityMat(d,F);
  fi;
  a:=ImmutableMatrix(F,a);
  b:=ImmutableMatrix(F,b);
  p:=ImmutableMatrix(F,p);
  t:=ImmutableMatrix(F,t);
  delta:=ImmutableMatrix(F,delta);
  if d > 4 then
    #v:=(DirectSumMat(Identity(MatrixAlgebra(F,d-4)),SpAdditionalElement(F))) *FORCEOne(P);
    v:=IdentityMat(d,F);
    v{[d-3..d]}{[d-3..d]}:=SpAdditionalElement@(F);
  elif d=4 then
    v:=SpAdditionalElement@(F);
  else
    v:=IdentityMat(d,F);
  fi;
  v:=ImmutableMatrix(F,v);

  return [a,b,t,delta,p,v];
end);

#   additional elements to generate SU 
BindGlobal("SUAdditionalElements@",function(F)
local EvenCase,I,J,M,d,gamma,phi,q;
  EvenCase:=ValueOption("EvenCase");
  if EvenCase=fail then
    EvenCase:=true;
  fi;
  if EvenCase then
    d:=4;
  else
    d:=3;
  fi;
  gamma:=PrimitiveElement(F);
  q:=RootInt(Size(F),2);
  I:=IdentityMat(d,F);
  if EvenCase then
    I[1][3]:=1*One(F);
    I[4][2]:=-1*One(F);
    J:=DiagonalMat([gamma,gamma^-q,gamma^-1,gamma^q]);
  else
    if IsEvenInt(q) then
      phi:=(Trace(GF(q),gamma))^-1*gamma;
    else
      phi:=-1/2*One(F);
    fi;
    I:=[[1,phi,1],[0,1,0],[0,-1,1]]*One(F);
    J:=DiagonalMat([gamma,gamma^(-q),gamma^(q-1)]);
  fi;

  I:=ImmutableMatrix(F,I);
  J:=ImmutableMatrix(F,J);
  return [I,J];
end);

#   canonical basis for SU(d, q) 
BindGlobal("SUChosenElements",function(G)
local varE,F,M,P,a,alpha,b,d,delta,f,i,n,p,q,t,w,w0,x,y;
  d:=DimensionOfMatrixGroup(G);
  varE:=DefaultFieldOfMatrixGroup(G);
  f:=QuoInt(DegreeOverPrimeField(varE),2);
  p:=Characteristic(varE);
  q:=p^f;
  F:=GF(q);
  w:=PrimitiveElement(varE);
  if IsEvenInt(Size(varE)) then
    w0:=w^(q+1);
    alpha:=1*One(varE);
  else
    alpha:=w^(QuoInt((q+1),2));
    w0:=alpha^2;
  fi;
  a:=NullMat(d,d,varE);
  a[1][2]:=alpha;
  a[2][1]:=alpha^-q;
  for i in [3..d] do
    a[i][i]:=1*One(varE);
  od;
  t:=IdentityMat(d,varE);
  t[1][2]:=alpha;
  delta:=Identity(M);
  if (d=3 and p=2 and f=1) then
    delta[1][2]:=w;
    delta[1][3]:=w;
    delta[3][2]:=w^2;
  else
    delta[1][1]:=w0;
    delta[2][2]:=w0^-1;
  fi;
  if d >= 4 then
    p:=NullMat(d,d,varE);
    p[1][3]:=1*One(varE);
    p[2][4]:=1*One(varE);
    p[3][1]:=1*One(varE);
    p[4][2]:=1*One(varE);
    for i in [5..d] do
      p[i][i]:=1*One(varE);
    od;
  else
    p:=IdentityMat(d,varE);
  fi;
  if d >= 4 then
    b:=NullMat(d,d,varE);
    n:=QuoInt(d,2);
    for i in [1,1+2..2*n-2] do
      b[i][i+2]:=1*One(varE);
    od;
    b[2*n-1][1]:=1*One(varE);
    for i in [2,2+2..2*n-2] do
      b[i][i+2]:=1*One(varE);
    od;
    b[2*n][2]:=1*One(varE);
    if IsOddInt(d) then
      b[d][d]:=1*One(varE);
    fi;
  else
    b:=IdentityMat(d,varE);
  fi;
  a:=ImmutableMatrix(varE,a);
  b:=ImmutableMatrix(varE,b);
  p:=ImmutableMatrix(varE,p);
  t:=ImmutableMatrix(varE,t);
  delta:=ImmutableMatrix(varE,delta);

  if d=2 then
    x:=IdentityMat(d,varE);
    y:=IdentityMat(d,varE);
  elif d in [3,4] then
    y:=SUAdditionalElements@(varE:EvenCase:=IsEvenInt(d));
    x:=y[1];
    y:=y[2];
  else
    y:=SUAdditionalElements@(varE:EvenCase:=IsEvenInt(d));
    x:=y[1];
    y:=y[2];
    #x:=(DirectSumMat(Identity(MatrixAlgebra(varE,f)),x))*FORCEOne(GL(d,varE));
    #y:=(DirectSumMat(Identity(MatrixAlgebra(varE,f)),y))*FORCEOne(GL(d,varE));
    f:=IdentityMat(d,varE);
    f{[d-Length(x)+1..d]}{[d-Length(x)+1..d]}:=x;x:=f;
    f:=IdentityMat(d,varE);
    f{[d-Length(x)+1..d]}{[d-Length(x)+1..d]}:=y;y:=f;
  fi;
  x:=ImmutableMatrix(varE,x);
  y:=ImmutableMatrix(varE,y);
  return [a,b,t,delta,p,x,y];
end);

#   if SpecialGroup is true, then standard generators
#  for SO^0, otherwise for Omega 
BindGlobal("SOChosenElements@",function(G)
local A,D,F,Gens,I,L,M,MA,P,SpecialGroup,U,_,a,b,delta,gens,h,i,m,n,q,u,w,x,y;
  SpecialGroup:=ValueOption("SpecialGroup");
  if SpecialGroup=fail then
    SpecialGroup:=false;
  fi;
  n:=Degree(G);
  Assert(1,IsOddInt(n) and n > 1);
  F:=BaseRing(G);
  q:=Size(F);
  w:=PrimitiveElement(F);
  MA:=MatrixAlgebra(F,n);
  A:=MatrixAlgebra(F,2);
  M:=MatrixAlgebra(F,3);
  a:=[1,1,2,0,1,0,0,1,1]*FORCEOne(M);
  U:=Identity(MA);
  InsertBlock(TILDEU,a,n-2,n-2);
  b:=[0,1,0,1,0,0,0,0,-1]*FORCEOne(M);
  L:=Identity(MA);
  InsertBlock(TILDEL,b,n-2,n-2);
  delta:=DiagonalMat(F,[w^2,w^-2,1])*FORCEOne(M);
  D:=Identity(MA);
  InsertBlock(TILDED,delta,n-2,n-2);
  Gens:=[L,U,D];
  if n=3 then
    h:=Identity(MA);
  else
    I:=[1,0,0,1]*FORCEOne(A);
    h:=Zero(MA);
    m:=n-1;
    for i in [1..QuoInt(m,2)-1] do
      x:=(i-1)*2+1;
      y:=x+2;
      InsertBlock(TILDEh,I,x,y);
    od;
    InsertBlock(TILDEh,(-1)^(QuoInt(n,2)-1)*I,m-1,1);
    h[n][n]:=1;
  fi;
  Append(TILDEGens,h);
  #   EOB -- add additional generator u Oct 2012
  if n > 3 then
    u:=Zero(MA);
    for i in [5..n] do
      u[i][i]:=1;
    od;
    u[1][3]:=1;
    u[2][4]:=1;
    u[3][1]:=-1;
    u[4][2]:=-1;
  else
    u:=Identity(MA);
  fi;
  Append(TILDEGens,u);
  if SpecialGroup then
    m:=Identity(MA);
    # =v= MULTIASSIGN =v=
    b:=Valuation(q-1,2);
    _:=b.val1;
    b:=b.val2;
    # =^= MULTIASSIGN =^=
    m[n-2][n-2]:=w^b;
    m[n-1][n-1]:=w^-b;
    Append(TILDEGens,m);
  fi;
  P:=GL(n,q);
  gens:=List(Gens,x->x*FORCEOne(P));
  return gens;
end);

#   if SpecialGroup is true, then standard generators
#  for SO+, otherwise for Omega+ 
BindGlobal("PlusChosenElements@",function(G)
local 
   A,F,Gens,I,M,MA,P,SpecialGroup,_,a,b,delta,delta1,delta4,gens,i,n,q,s,s1,t,
   t1,t4,u,v,w,x,y;
  SpecialGroup:=ValueOption("SpecialGroup");
  if SpecialGroup=fail then
    SpecialGroup:=false;
  fi;
  n:=Degree(G);
  F:=BaseRing(G);
  q:=Size(F);
  w:=PrimitiveElement(F);
  A:=MatrixAlgebra(F,2);
  if n=2 then
    Gens:=List([1..8],i->Identity(A));
    if Size(F) > 3 then
      x:=OmegaPlus(2,F).1;
      Gens[3]:=x;
    fi;
    if SpecialGroup then
      w:=PrimitiveElement(F);
      if IsOddInt(q) then
        Gens[Size(Gens)+1]:=[w,0,0,w^-1]*FORCEOne(GL(2,F));
      else
        Gens[Size(Gens)+1]:=[0,1,1,0]*FORCEOne(A);
      fi;
    fi;
  else
    MA:=MatrixAlgebra(F,n);
    M:=MatrixAlgebra(F,4);
    s:=Zero(MA);
    for i in [5..n] do
      s[i][i]:=1;
    od;
    s[1][4]:=-1;
    s[2][3]:=-1;
    s[3][2]:=1;
    s[4][1]:=1;
    t4:=[1,0,0,-1,0,1,0,0,0,1,1,0,0,0,0,1]*FORCEOne(M);
    t:=Identity(MA);
    InsertBlock(TILDEt,t4,1,1);
    delta4:=DiagonalMat(F,[w,w^-1,w,w^-1]);
    delta:=Identity(MA);
    InsertBlock(TILDEdelta,delta4,1,1);
    s1:=Zero(MA);
    for i in [5..n] do
      s1[i][i]:=1;
    od;
    s1[1][3]:=1;
    s1[2][4]:=1;
    s1[3][1]:=-1;
    s1[4][2]:=-1;
    t4:=[1,0,1,0,0,1,0,0,0,0,1,0,0,-1,0,1]*FORCEOne(M);
    t1:=Identity(MA);
    InsertBlock(TILDEt1,t4,1,1);
    delta4:=DiagonalMat(F,[w,w^-1,w^-1,w]);
    delta1:=Identity(MA);
    InsertBlock(TILDEdelta1,delta4,1,1);
    u:=Identity(MA);
    I:=Identity(A);
    v:=Zero(MA);
    for i in [1..QuoInt(n,2)-1] do
      x:=(i-1)*2+1;
      y:=x+2;
      InsertBlock(TILDEv,I,x,y);
    od;
    InsertBlock(TILDEv,(-1)^(QuoInt(n,2)+1)*I,n-1,1);
    Gens:=[s,t,delta,s1,t1,delta1,u,v];
    if SpecialGroup then
      a:=Identity(MA);
      if IsOddInt(q) then
        # =v= MULTIASSIGN =v=
        b:=Valuation(q-1,2);
        _:=b.val1;
        b:=b.val2;
        # =^= MULTIASSIGN =^=
        a[1][1]:=w^b;
        a[2][2]:=w^-b;
      else
        a[1][1]:=0;
        a[1][2]:=1;
        a[2][1]:=1;
        a[2][2]:=0;
      fi;
      Append(TILDEGens,a);
    fi;
  fi;
  P:=GL(n,F);
  gens:=List(Gens,x->x*FORCEOne(P));
  return gens;
end);

BindGlobal("MinusChar2Elements@",function(G)
local 
   C,CC,F,G,GG,Gens,I,II,K,M,O,SpecialGroup,a,alpha,d,d1,dd,delta,deltaq,gamma,
   h,i,m,p,pow,q,r,r1,rr,sl,t,t1,tt,x,y;
  SpecialGroup:=ValueOption("SpecialGroup");
  if SpecialGroup=fail then
    SpecialGroup:=false;
  fi;
  d:=DimensionOfMatrixGroup(G);
  F:=BaseRing(G);
  q:=Size(F);
  alpha:=PrimitiveElement(F);
  K:=GF(q^2);
  gamma:=PrimitiveElement(K);
  for i in [1..q-1] do
    if (gamma^i)^(q+1)=alpha then
      pow:=i;
      break i;
    fi;
  od;
  gamma:=gamma^pow;
  Assert(1,gamma^(q+1)=alpha);
  M:=MatrixAlgebra(GF(q^2),d);
  if d=2 then
    Gens:=List([1..5],i->Identity(G));
    O:=OmegaMinus(d,q);
    x:=O.Ngens(O);
    Gens[3]:=x;
    if SpecialGroup then
      Gens[Size(Gens)+1]:=SOMinus(2,q).1;
    fi;
  else
    C:=[1,0,0,0,0,gamma,1,0,0,gamma^q,1,0,0,0,0,1]*FORCEOne(GL(4,GF(q^2)));
    C:=TransposedMat(C);
    CC:=[1,0,0,0,0,0,0,1,0,0,1,0,0,1,0,0]*FORCEOne(GL(4,GF(q^2)));
    sl:=SL(2,GF(q^2));
    t:=[1,1,0,1]*FORCEOne(sl);
    r:=[1,0,1,1]*FORCEOne(sl);
    delta:=[gamma,0,0,gamma^-1]*FORCEOne(sl);
    deltaq:=[gamma^q,0,0,gamma^-q]*FORCEOne(sl);
    G:=GL(4,GF(q^2));
    t1:=(TensorProduct(t,t)*FORCEOne(G)^(C^-1))^(CC^-1);
    r1:=(TensorProduct(r,r)*FORCEOne(G)^(C^-1))^(CC^-1);
    d1:=(TensorProduct(delta,deltaq)*FORCEOne(G)^(C^-1))^(CC^-1);
    GG:=GL(d,GF(q));
    tt:=InsertBlock(One(GG),t1*FORCEOne(GL(4,GF(q))),d-3,d-3);
    rr:=InsertBlock(One(GG),r1*FORCEOne(GL(4,GF(q))),d-3,d-3);
    dd:=InsertBlock(One(GG),d1*FORCEOne(GL(4,GF(q))),d-3,d-3);
    Gens:=[tt,rr,dd];
    I:=One(GL(2,GF(q^2)));
    if d > 4 then
      p:=Zero(M);
      InsertBlock(TILDEp,I,1,3);
      InsertBlock(TILDEp,-I,3,1);
      for i in [5..d] do
        p[i][i]:=1;
      od;
    else
      p:=One(GG);
    fi;
    Append(TILDEGens,p*FORCEOne(GG));
    if d > 6 then
      h:=Zero(M);
      m:=d-2;
      for i in [1..QuoInt(m,2)-1] do
        x:=(i-1)*2+1;
        y:=x+2;
        InsertBlock(TILDEh,I,x,y);
      od;
      # rewritten select statement
      if IsEvenInt(QuoInt(d,2)) then
        II:=I;
      else
        II:=-I;
      fi;
      InsertBlock(TILDEh,II,m-1,1);
      InsertBlock(TILDEh,I,d-1,d-1);
      Append(TILDEGens,h);
    else
      Append(TILDEGens,p*FORCEOne(GG));
    fi;
    if SpecialGroup then
      a:=Identity(M);
      a[1][1]:=0;
      a[2][2]:=0;
      a[1][2]:=1;
      a[2][1]:=1;
      Append(TILDEGens,a);
    fi;
  fi;
  return List(Gens,g->g*FORCEOne(GL(d,q)));
end);

#   if SpecialGroup is true, then standard generators
#  for SO-, otherwise for Omega- 
BindGlobal("MinusChosenElements@",function(G)
local 
   A,D,varE,EE,F,Gens,I,L,M,MA,P,SpecialGroup,U,a,b,c,d,delta,gens,h,i,m,mu,n,p,
   q,w,x,y;
  SpecialGroup:=ValueOption("SpecialGroup");
  if SpecialGroup=fail then
    SpecialGroup:=false;
  fi;
  n:=Degree(G);
  F:=BaseRing(G);
  q:=Size(F);
  if IsEvenInt(q) then
    return MinusChar2Elements@(G:SpecialGroup:=SpecialGroup);
  fi;
  A:=MatrixAlgebra(F,2);
  if n=2 then
    Gens:=List([1..5],i->Identity(A));
    x:=OmegaMinus(n,q).1;
    Gens[2]:=x;
    if SpecialGroup then
      if q mod 4=1 then
        Gens[Size(Gens)+1]:=-Identity(GL(2,F));
      else
        y:=SOMinus(n,q).1;
        Gens[Size(Gens)+1]:=y*x^-1;
      fi;
    fi;
    return List(Gens,x->x*FORCEOne(GL(n,q)));
  fi;
  w:=PrimitiveElement(F);
  MA:=MatrixAlgebra(F,n);
  #   EE := ext<F | 2>;
  lvarEE:=GF(q^2);
  delta:=PrimitiveElement(lvarEE);
  mu:=delta^(QuoInt((q+1),2));
  #  
  #  if mu^2 ne w then
  #  x := find_quad_ext_prim(F, EE);
  #  E<delta> := sub<EE | x>;
  #  SetPrimitiveElement(E, delta);
  #  mu := delta^((q + 1) div 2);
  #  else
  #  E := EE;
  #  end if;
  
  varE:=lvarEE;
  #   EOB Nov 2012 -- we need this to be true but known problem
  Assert(1,mu^2=w);
  MA:=MatrixAlgebra(F,n);
  I:=[1,0,0,1]*FORCEOne(A);
  M:=MatrixAlgebra(F,4);
  a:=[1,1,0,1]*FORCEOne(A);
  b:=[2,0,0,0]*FORCEOne(A);
  c:=[0,1,0,0]*FORCEOne(A);
  d:=[1,0,0,1]*FORCEOne(A);
  U:=Identity(MA);
  U[n-3][n-3]:=0;
  U[n-3][n-2]:=1;
  U[n-2][n-3]:=1;
  U[n-2][n-2]:=0;
  U[n-1][n-1]:=-1;
  a:=[1,0,1,1]*FORCEOne(A);
  b:=[0,0,2,0]*FORCEOne(A);
  c:=[1,0,0,0]*FORCEOne(A);
  d:=[1,0,0,1]*FORCEOne(A);
  L:=Zero(MA);
  for i in [1..n-4] do
    L[i][i]:=1;
  od;
  InsertBlock(TILDEL,a,n-3,n-3);
  InsertBlock(TILDEL,b,n-3,n-1);
  InsertBlock(TILDEL,c,n-1,n-3);
  InsertBlock(TILDEL,d,n-1,n-1);
  L:=TransposedMat(L);
  a:=[delta^(q+1),0,0,delta^(-q-1)]*FORCEOne(A);
  d:=[1/2*(delta^(q-1)+delta^(-q+1)),1/2*mu*(delta^(q-1)-delta^(-q+1))
   ,1/2*mu^(-1)*(delta^(q-1)-delta^(-q+1)),1/2*(delta^(q-1)+delta^(-q+1))]
   *FORCEOne(A);
  D:=Zero(MA);
  for i in [1..n-4] do
    D[i][i]:=1;
  od;
  InsertBlock(TILDED,a,n-3,n-3);
  InsertBlock(TILDED,d,n-1,n-1);
  D:=TransposedMat(D);
  Gens:=[U,L,D];
  if n <= 4 then
    p:=Identity(MA);
  elif n > 4 then
    p:=Zero(MA);
    InsertBlock(TILDEp,I,1,3);
    InsertBlock(TILDEp,-I,3,1);
    for i in [5..n] do
      p[i][i]:=1;
    od;
  fi;
  Append(TILDEGens,p);
  #   if n gt 6 then
  h:=Zero(MA);
  m:=n-2;
  for i in [1..QuoInt(m,2)-1] do
    x:=(i-1)*2+1;
    y:=x+2;
    InsertBlock(TILDEh,I,x,y);
  od;
  InsertBlock(TILDEh,(-1)^(QuoInt(n,2))*I,m-1,1);
  InsertBlock(TILDEh,I,n-1,n-1);
  Append(TILDEGens,h);
  #   end if;
  if SpecialGroup then
    m:=Identity(MA);
    if q mod 4=3 then
      m[1][1]:=-1;
      m[2][2]:=-1;
    else
      m[n-1][n-1]:=-1;
      m[n][n]:=-1;
    fi;
    Append(TILDEGens,m);
  fi;
  P:=GL(n,q);
  gens:=List(Gens,x->x*FORCEOne(P));
  return rec(val1:=gens,
    val2:=varE);
end);

ClassicalStandardGenerators:=function(type,d,F)
#  -> ,]  return the Leedham - Green and O ' Brien standard generators for the
#  quasisimple classical group of specified type in dimension d and defining
#  field F ; the string type := one of SL , Sp , SU , Omega , Omega + , Omega -
local PresentationGenerators,SpecialGroup;
  SpecialGroup:=ValueOption("SpecialGroup");
  if SpecialGroup=fail then
    SpecialGroup:=false;
  fi;
  PresentationGenerators:=ValueOption("PresentationGenerators");
  if PresentationGenerators=fail then
    PresentationGenerators:=false;
  fi;
  if not type in ["SL","Sp","SU","Omega","Omega+","Omega-"] then
    Error("Type is not valid");
  fi;
  if not d > 1 then
    Error("Dimension is not valid");
  fi;
  if type="Omega" then
      if not IsOddInt(d) and IsOddInt(Size(F)) then
      Error("Dimension and field size must be odd");
    fi;
  fi;
  if type in Set(["Omega+","Omega-"]) then
      if not (IsEvenInt(d) and d >= 4) then
      Error("Dimension must be even and at least 4");
    fi;
  fi;
  if PresentationGenerators=true then
    return Internal_PresentationGenerators@(type,d,Size(F));
  fi;
  if type="SL" then
    return rec(val1:=SLChosenElements@(SL(d,F)),
      val2:=_);
  elif type="Sp" then
    return rec(val1:=SpChosenElements@(SP(d,F)),
      val2:=_);
  elif type="SU" then
    return rec(val1:=SUChosenElements@(SU(d,ExtStructure(F,2))),
      val2:=_);
  elif type="Omega" then
    return rec(val1:=SOChosenElements(Omega(d,F):SpecialGroup:=SpecialGroup),
      val2:=_);
  elif type="Omega+" then
    return rec(val1:=PlusChosenElements@(OmegaPlus(d,F)
     :SpecialGroup:=SpecialGroup),
      val2:=_);
    #   avoid OmegaMinus -- it sets order, too hard for large d, q
  elif type="Omega-" then
    return MinusChosenElements@(ChevalleyGroup("2D",QuoInt(d,2),F)
     :SpecialGroup:=SpecialGroup);
  fi;
end;

ClassicalStandardGenerators:=function(type,d,q)
#  -> ,]  return the Leedham - Green and O ' Brien standard generators for the
#  quasisimple classical group of specified type in dimension d and defining
#  field F ; the string type := one of SL , Sp , SU , Omega , Omega + , Omega -
local PresentationGenerators,SpecialGroup;
  SpecialGroup:=ValueOption("SpecialGroup");
  if SpecialGroup=fail then
    SpecialGroup:=false;
  fi;
  PresentationGenerators:=ValueOption("PresentationGenerators");
  if PresentationGenerators=fail then
    PresentationGenerators:=false;
  fi;
  if not type in ["SL","Sp","SU","Omega","Omega+","Omega-"] then
    Error("Type is not valid");
  fi;
  if not d > 1 then
    Error("Dimension is not valid");
  fi;
  if not IsPrimePowerInt(q) then
    Error("Field size is not valid");
  fi;
  return ClassicalStandardGenerators(type,d,GF(q)
   :SpecialGroup:=SpecialGroup,PresentationGenerators:=PresentationGenerators);
end;


