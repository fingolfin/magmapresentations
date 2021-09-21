#  File converted from Magma code -- requires editing and checking
#  Magma -> GAP converter, version 0.5, 11/5/18 by AH

# File checked and edited by MW 05/07/19

#  Global Variables used: ClassicalStandardPresentation, GF,
#  Internal_PresentationGenerators, Internal_StandardPresentationForOmega,
#  Internal_StandardPresentationForSL, Internal_StandardPresentationForSU,
#  Internal_StandardPresentationForSp, IsEven, IsOdd

#  Defines: ClassicalStandardPresentation, Internal_PresentationGenerators

Internal_PresentationGenerators:=function(type,d,F)
#  -> ,]  return the Leedham - Green and O ' Brien presentation generators for
#  the quasisimple classical group of specified type in dimension d and
#  defining field F ; the string type := one of SL , Sp , SU , Omega , Omega +
#  , Omega -
local q;
  if not type in ["SL","Sp","SU","Omega","Omega+","Omega-"] then
    Error("Type is not valid");
  fi;
  if not d > 1 then
    Error("Dimension is not valid");
  fi;
  if type="SU" then
      if not d >= 3 then
      Error("Dimension must be at least 3");
    fi;
    if d=3 then
          if not Size(F) > 2 then
        Error("Field size must be at least 3");
      fi;
    fi;
  fi;
  if type="Omega" then
      if not IsOddInt(d) and d >= 5 and IsOddInt(Size(F)) then
      Error("Dimension and field size must be odd, d >= 5, and q >= 3");
    fi;
  fi;
  if type in Set(["Omega+","Omega-"]) then
      if not (IsEvenInt(d) and d >= 6) then
      Error("Dimension must be even and at least 6");
    fi;
  fi;
  if type="Sp" then
      if not IsEvenInt(d) and d >= 4 then
      Error("Dimension must be even and at least 4");
    fi;
  fi;
  q:=Size(F);
  if type="SL" then
    return SLGenerators(d,q);
  elif type="Sp" then
    return SpGenerators(d,q);
  elif type="SU" then
    return SUGenerators(d,q);
  elif type="Omega" then
    return OmegaGenerators(d,q);
  elif type="Omega+" then
    return PlusGenerators(d,q);
  elif type="Omega-" then
    return MinusGenerators(d,q);
  fi;
end;

## TODO Fix duplicate fuction definition here

Internal_PresentationGenerators:=function(type,d,q)
#  -> ,]  return the Leedham - Green and O ' Brien presentation generators for
#  the quasisimple classical group of specified type in dimension d over field
#  of size q ; the string type := one of SL , Sp , SU , Omega , Omega + , Omega
#  -
if not type in ["SL","Sp","SU","Omega","Omega+","Omega-"] then
    Error("Type is not valid");
  fi;
  if not d > 1 then
    Error("Dimension is not valid");
  fi;
  if Size(DuplicateFreeList(Factors(q))) > 1 then
    Error("Field size is not valid");
  fi;
  return Internal_PresentationGenerators(type,d,GF(q));
end;

ClassicalStandardPresentation:=function(type,d,q)
#  -> ,GrpSLP ,[ ,]  return the Leedham - Green and O ' Brien presentation on
#  standard generators for the quasisimple classical group of specified type in
#  dimension d over field of size q ; the string type := one of SL , Sp , SU ,
#  Omega + , Omega - , Omega . If Projective := true , then return the
#  presentation for the corresponding projective group . If
#  PresentationGenerators := true , then return the presentation on the
#  presentation generators , otherwise on standard generators . An SLP group on
#  the generators and the relations as SLPs in this group are returned .
local PresentationGenerators,Projective;
  Projective:=ValueOption("Projective");
  if Projective=fail then
    Projective:=false;
  fi;
  PresentationGenerators:=ValueOption("PresentationGenerators");
  if PresentationGenerators=fail then
    PresentationGenerators:=false;
  fi;
  if not type in ["SL","Sp","SU","Omega+","Omega-","Omega"] then
    Error("Type is not valid");
  fi;
  if not d > 1 then
    Error("Dimension is not valid");
  fi;
  if Size(DuplicateFreeList(Factors(q))) > 1 then
    Error("Field size is not valid");
  fi;
  return ClassicalStandardPresentation(type,d,GF(q)
   :Projective:=Projective,PresentationGenerators:=PresentationGenerators);
end;

# TODO Fix duplicate function definition

ClassicalStandardPresentation:=function(type,d,F)
#  -> ,GrpSLP ,[ ,]  return the Leedham - Green and O ' Brien presentation on
#  standard generators for the quasisimple classical group of specified type in
#  dimension d over field of size q ; the string type := one of SL , Sp , SU ,
#  Omega + , Omega - , Omega . If Projective := true , then return the
#  presentation for the corresponding projective group . If
#  PresentationGenerators := true , then return the presentation on the
#  presentation generators , otherwise on standard generators . An SLP group on
#  the generators and the relations as SLPs in this group are returned .
local PresentationGenerators,Projective;
  Projective:=ValueOption("Projective");
  if Projective=fail then
    Projective:=false;
  fi;
  PresentationGenerators:=ValueOption("PresentationGenerators");
  if PresentationGenerators=fail then
    PresentationGenerators:=false;
  fi;
  if not type in ["SL","Sp","SU","Omega+","Omega-","Omega"] then
    Error("Type is not valid");
  fi;
  if not d > 1 then
    Error("Dimension is not valid");
  fi;
  if type="Omega" then
      if not IsOddInt(d) and d >= 3 and IsOddInt(Size(F)) then
      Error("Dimension and field size must be odd");
    fi;
  fi;
  if type in Set(["Sp","Omega+","Omega-"]) then
      if not (IsEvenInt(d) and d >= 4) then
      Error("Dimension must be even and at least 4");
    fi;
  fi;
  if type="SL" then
    return
     Internal_StandardPresentationForSL(d,F:Projective:=Projective,
     Presentation:=PresentationGenerators);
  elif type="Sp" then
    return
     Internal_StandardPresentationForSp(d,F:Projective:=Projective,
     Presentation:=PresentationGenerators);
  elif type="SU" then
    return
     Internal_StandardPresentationForSU(d,F:Projective:=Projective,
     Presentation:=PresentationGenerators);
  elif type="Omega+" then
    return
     Internal_StandardPresentationForOmega(d,F:Projective:=Projective,
     Type:="Omega+",Presentation:=PresentationGenerators);
  elif type="Omega-" then
    return
     Internal_StandardPresentationForOmega(d,F:Projective:=Projective,
     Type:="Omega-",Presentation:=PresentationGenerators);
  elif type="Omega" then
    return
     Internal_StandardPresentationForOmega(d,F:Type:="Omega",
     Presentation:=PresentationGenerators);
  fi;
end;
