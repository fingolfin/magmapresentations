#  File converted from Magma code -- requires editing and checking
#  Magma -> GAP converter, version 0.5, 11/5/18 by AH

#  Global Variables used: Factorial, IsEven, LHS, RHS, SLPGroup, SignedEven,
#  SignedOdd

#  Defines: OrderSigned, SignedEven, SignedOdd, SignedPermutations

SignedOdd:=function(d)
local Rels,S,u,v;
  S:=SLPGroup(2);
  u:=S.1;
  v:=S.2;
  Rels:=Concatenation([u^4,(u^2)^(v*u)*u^2*(u^2)^v,v^d,(u*v)^(d-1),(u*v^-1*u*v)
   ^3],List([2..QuoInt(d,2)],j->Tuple([u,v^-j*u*v^j])));
  return rec(val1:=S,
    val2:=Rels);
end;

SignedEven:=function(d)
local R,Rels,S,u,v;
  S:=SLPGroup(2);
  u:=S.1;
  v:=S.2;
  if d=2 then
    Rels:=[u^4,u*v^-1];
    return rec(val1:=S,
      val2:=Rels);
  fi;
  Rels:=Concatenation([u^4,(u^2)^(v*u)*u^2*(u^2)^v,(u*v^-1*u*v)^3]
   ,List([2..QuoInt(d,2)],j->Tuple([u,v^-j*u*v^j])));
  R:=[v^d=(u*v)^(d-1),Tuple([v^d,u])=1,v^(2*d)=1];
  Rels:=Concatenation(Rels,List(R,r->LHS(r)*RHS(r)^-1));
  return rec(val1:=S,
    val2:=Rels);
end;

#   presentation for group of signed permutation matrices of rank d and det 1
SignedPermutations:=function(d)
Assert(1,d > 1);
  if IsEvenInt(d) then
    return SignedEven(d);
  else
    return SignedOdd(d);
  fi;
end;

OrderSigned:=function(d)
return 2^(d-1)*Factorial(d);
end;


