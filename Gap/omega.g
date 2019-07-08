#  File converted from Magma code -- requires editing and checking
#  Magma -> GAP converter, version 0.5, 11/5/18 by AH

#  Global Variables used: Internal_StandardPresentationForOmega, IsEven, IsOdd,
#  IsPrimePower

#  Defines: Internal_StandardPresentationForOmega

#  ///////////////////////////////////////////////////////////////////////
#     Short presentation for Omega^\epsilon(d, q)                       //
#                                                                       //
#     Input two parameters to compute this presentation of Omega(d, q)     //
#       d = dimension                                                   //
#       q = field order                                                 //

#     November 2017
#  ///////////////////////////////////////////////////////////////////////
Internal_StandardPresentationForOmega:=function(d,F)
#  -> ,GrpSLP ,[ ,]  return standard presentation for Omega ( d , F )
local Presentation,Projective,Type;
  Projective:=ValueOption("Projective");
  if Projective=fail then
    Projective:=false;
  fi;
  Presentation:=ValueOption("Presentation");
  if Presentation=fail then
    Presentation:=false;
  fi;
  Type:=ValueOption("Type");
  if Type=fail then
    Type:="Omega+";
  fi;
  if not d > 2 then
    Error("Degree must be at least 3");
  fi;
  return Internal_StandardPresentationForOmega(d,Size(F)
   :Projective:=Projective,Presentation:=Presentation,Type:=Type);
end;

# TODO: fix multiple definition of same function

Internal_StandardPresentationForOmega:=function(d,q)
#  -> ,GrpSLP ,[ ,]  return standard presentation for Omega ( d , q )
local Presentation,Projective,Type;
  Projective:=ValueOption("Projective");
  if Projective=fail then
    Projective:=false;
  fi;
  Presentation:=ValueOption("Presentation");
  if Presentation=fail then
    Presentation:=false;
  fi;
  Type:=ValueOption("Type");
  if Type=fail then
    Type:="Omega+";
  fi;
  if Size(DuplicateFreeList(Factors(q))) > 1 then
    Error("Field size is not valid");
  fi;
  if Type="Omega" then
      if not IsOddInt(d) and d >= 3 then
      Error("Degree must be odd and at least 3");
    fi;
      if not IsOddInt(q) then
      Error("Field size must be odd");
    fi;
    return OmegaPresentation(d,q:Presentation:=Presentation);
  elif Type="Omega+" then
      if not IsEvenInt(d) and d >= 4 then
      Error("Degree must be even and at least 4");
    fi;
    return
     PlusPresentation(d,q:Projective:=Projective,Presentation:=Presentation);
  elif Type="Omega-" then
      if not IsEvenInt(d) and d >= 4 then
      Error("Degree must be even and at least 4");
    fi;
    return
     MinusPresentation(d,q:Projective:=Projective,Presentation:=Presentation);
  else
    Error("Invalid input");
  fi;
end;
