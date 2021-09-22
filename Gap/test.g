#   usually subgroups chosen for coset enumeration are maximal of smallest index
## TODO Don't know what this does
SetGlobalTCParameters(:CosetLimit:=10^7,Hard:=true,Print:=10^6);
LoadPackage("ace");
TCENUM:=ACETCENUM;

dim_limit:=20;
#   max dimension
field_limit:=100;
#   max size of field
#   Presentation = false: presentation rewritten on standard generators
#   Presentation = true: presentation listed in paper
#   Projective = true: presentation for group modulo its centre
#   do matrices satisfy presentation?
#   coset enumerations
TestSL:=function(a_list,b_list)
local DD,F,I,K,Presentation,Projective,QQ,U,V,d,delta,e,f,p,q,tau;
  Projective:=ValueOption("Projective");
  if Projective=fail then
    Projective:=false;
  fi;
  Presentation:=ValueOption("Presentation");
  if Presentation=fail then
    Presentation:=true;
  fi;
  for d in a_list do
    for q in b_list do
      DD:=d;
      QQ:=q;
      Print("\n D = ",d,"q = ",q,"\n");
      if d=2 then
        F:=ClassicalStandardPresentation("SL",d,q:Projective:=Projective,
         PresentationGenerators:=false);
      else
        F:=ClassicalStandardPresentation("SL",d,q:Projective:=Projective,
         PresentationGenerators:=Presentation);
      fi;
      e := Factors(q);
      if Size(DuplicateFreeList(e)) > 1 then
          f := false;
      else
          f := true;
          p := e[1];
          e := Size(e);
      fi;
      U:=F.1;
      V:=F.2;
      tau:=F.3;
      delta:=F.4;
      if d=2 then
          ## TODO SubStructure
        K:=SubStructure(F,tau,#TODO CLOSURE
          delta);
      else
          ## TODO SubStructure
        #   max? subgroup containing SL(d - 1, q)
        K:=SubStructure(F,U,#TODO CLOSURE
          tau,V*U^(V^-1),delta,delta^(V^-1),tau^(V^-1));
      fi;
      ## TODO Lots of this to change here
      I:=CosetImage(F,SubStructure(F,K));
      if Degree(I) < 10^7 then
        RandomSchreier(I);
        CompositionFactors(I);
        if d=2 then
          Assert(1,Degree(I)=q+1);
        else
          Assert(1,(q^d-1) mod Degree(I)=0);
          #   else assert Degree (I) eq (q^d - 1);
        fi;
      fi;
      ## TODO Up to here
    od;
  od;
  return true;
end;
