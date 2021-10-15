
SUElements:=function()
local Q,R,S,d,q;
  for d in [3..dim_limit] do
    for q in [2..field_limit] do
      if Size(DuplicateFreeList(Factors(p))) > 1 then
        Print(d," ",q,"\n");
        R:=ClassicalStandardPresentation("SU",d,q:PresentationGenerators:=false)
         ;
        Q:=FreeGroupOfFpGroup(R);
         R := RelatorsOfFpGroup(R);
        S:=ClassicalStandardGenerators("SU",d,q);
        # was "Assert(1,Size(Set(Evaluate(R,S)))=1);"
        Assert(1,Size(Set(List(R, w-> MappedWord(w, GeneratorsOfGroup(Q), S))))=1);
      fi;
    od;
  od;
  return true;
end;

PlusElements:=function()
local varE,Q,R,d,q;
  for d in [4,4+2..dim_limit] do
    for q in [2..field_limit] do
      if Size(DuplicateFreeList(Factors(p))) > 1 then
        Print(d," ",q,"\n");
        R:=ClassicalStandardPresentation("Omega+",d,
         q:PresentationGenerators:=false);
        Q:=FreeGroupOfFpGroup(R);
        R:=RelatorsOfFpGroup(R);
        varE:=ClassicalStandardGenerators("Omega+",d,q);
        # was "Assert(1,Size(Set(Evaluate(R,varE)))=1);"
        Assert(1,Size(Set(List(R, w-> MappedWord(w, GeneratorsOfGroup(Q), varE))))=1);
      fi;
    od;
  od;
  return true;
end;

MinusElements:=function()
local varE,Q,R,d,q;
  for d in [4,4+2..dim_limit] do
    for q in [2..field_limit] do
      if Size(DuplicateFreeList(Factors(p))) > 1 then
        Print(d," ",q,"\n");
        R:=ClassicalStandardPresentation("Omega-",d,
         q:PresentationGenerators:=false);
        Q:=FreeGroupOfFpGroup(R);
        R:=RelatorsOfFpGroup(R);
        varE:=ClassicalStandardGenerators("Omega-",d,q);
        # was "Assert(1,Size(Set(Evaluate(R,varE)))=1);"
        Assert(1,Size(Set(List(R, w-> MappedWord(w, GeneratorsOfGroup(Q), varE))))=1);
      fi;
    od;
  od;
  return true;
end;

OmegaElements:=function()
local varE,Q,R,d,q;
  for d in [3,3+2..dim_limit] do
    for q in [3..field_limit] do
      if Size(DuplicateFreeList(Factors(p))) > 1 and IsOddInt(q) then
        Print(d," ",q,"\n");
        R:=ClassicalStandardPresentation("Omega",d,
         q:PresentationGenerators:=false);
        R:=RelatorsOfFpGroup(R);
        varE:=ClassicalStandardGenerators("Omega",d,q);
        Assert(1,Size(Set(Evaluate(R,varE)))=1);
      fi;
    od;
  od;
  return true;
end;
