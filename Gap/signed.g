#  File converted from Magma code -- requires editing and checking
#  Magma -> GAP converter, version 0.5, 11/5/18 by AH

# Edited and checked 11/7/19 by MW

#  Global Variables used: Factorial, IsEven, LHS, RHS, FreeGroup, SignedEven,
#  SignedOdd

#  Defines: OrderSigned, SignedEven, SignedOdd, SignedPermutations

SignedOdd:=function(d)
local Rels,S,u,v;
  S:=FreeGroup(2);
  u:=S.1;
  v:=S.2;
  Rels:=Concatenation([u^4,(u^2)^(v*u)*u^2*(u^2)^v,v^d,(u*v)^(d-1),(u*v^-1*u*v)
   ^3],List([2..QuoInt(d,2)],j->Comm(u,v^-j*u*v^j)));
  return S/Rels;
end;

SignedEven:=function(d)
local R,Rels,S,u,v;
  S:=FreeGroup(2);
  u:=S.1;
  v:=S.2;
  if d=2 then
    Rels:=[u^4,u*v^-1];
    return S/Rels;
  fi;
  Rels:=Concatenation([u^4,(u^2)^(v*u)*u^2*(u^2)^v,(u*v^-1*u*v)^3]
   ,List([2..QuoInt(d,2)],j->Comm(u,v^-j*u*v^j)));
  R:=[v^d/(u*v)^(d-1),Comm(v^d,u),v^(2*d)];
  Rels:=Concatenation(Rels,R);
  return S/Rels;
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
