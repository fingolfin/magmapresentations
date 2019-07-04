import "sl.m": SLGenerators;
import "sp.m": SpGenerators;
import "su.m": SUGenerators;
import "circle.m": OmegaGenerators;
import "plus.m": PlusGenerators;
import "minus.m": MinusGenerators;

intrinsic Internal_PresentationGenerators (type :: MonStgElt, d :: RngIntElt, F :: FldFin) 
-> []
{return the Leedham-Green and O'Brien presentation generators for the quasisimple 
 classical group of specified type in dimension d and defining field F; 
 the string type is one of SL, Sp, SU, Omega, Omega+, Omega-
} 
   require type in ["SL", "Sp", "SU", "Omega", "Omega+", "Omega-"]: "Type is not valid";
   require d gt 1: "Dimension is not valid";

   if type eq "SU" then 
      require d ge 3: "Dimension must be at least 3"; 
      if d eq 3 then require #F gt 2: "Field size must be at least 3"; end if;
   end if;
   if type eq "Omega" then require IsOdd (d) and d ge 5 and IsOdd (#F): 
      "Dimension and field size must be odd, d >= 5, and q >= 3"; 
   end if;
   if type in {"Omega+", "Omega-"}  then require (IsEven (d) and d ge 6): 
      "Dimension must be even and at least 6"; 
   end if;
   if type eq "Sp" then 
      require IsEven (d) and d ge 4: "Dimension must be even and at least 4";
   end if;
    
   q := #F;
   case type:
       when "SL": return SLGenerators (d, q); 
       when "Sp": return SpGenerators (d, q);
       when "SU": return SUGenerators (d, q);
       when "Omega": return OmegaGenerators (d, q);
       when "Omega+": return PlusGenerators (d, q);
       when "Omega-": return MinusGenerators (d, q);
   end case;
end intrinsic;

intrinsic Internal_PresentationGenerators (type :: MonStgElt, d :: RngIntElt, q :: RngIntElt) 
-> []
{return the Leedham-Green and O'Brien presentation generators for the quasisimple 
 classical group of specified type in dimension d over field of size q; 
 the string type is one of SL, Sp, SU, Omega, Omega+, Omega-
} 
   require type in ["SL", "Sp", "SU", "Omega", "Omega+", "Omega-"]: "Type is not valid";
   require d gt 1: "Dimension is not valid";
   require IsPrimePower (q): "Field size is not valid";

   return Internal_PresentationGenerators(type, d, GF(q)); 
end intrinsic;

intrinsic ClassicalStandardPresentation (type :: MonStgElt, d :: RngIntElt, 
   q :: RngIntElt: Projective := false, PresentationGenerators:= false)
-> GrpSLP, []
{return the Leedham-Green and O'Brien presentation on standard generators for the 
 quasisimple classical group of specified type in dimension d over field of size q; 
 the string type is one of SL, Sp, SU, Omega+, Omega-, Omega.
 If Projective is true, then return the presentation for the
 corresponding projective group. 
 If PresentationGenerators is true, then return the presentation 
 on the presentation generators, otherwise on standard generators.
 An SLP group on the generators and the relations as SLPs in this 
 group are returned.
} 
   require type in ["SL", "Sp", "SU", "Omega+", "Omega-", "Omega"]: "Type is not valid";
   require d gt 1: "Dimension is not valid";
   require IsPrimePower (q): "Field size is not valid";
   return ClassicalStandardPresentation(type, d, GF(q) : 
          Projective := Projective, PresentationGenerators := PresentationGenerators);
end intrinsic;

intrinsic ClassicalStandardPresentation (type :: MonStgElt, d :: RngIntElt, 
   F :: FldFin: Projective := false, PresentationGenerators := false)
-> GrpSLP, []
{return the Leedham-Green and O'Brien presentation on standard generators for the 
 quasisimple classical group of specified type in dimension d over field of size q; 
 the string type is one of SL, Sp, SU, Omega+, Omega-, Omega.
 If Projective is true, then return the presentation for the
 corresponding projective group. 
 If PresentationGenerators is true, then return the presentation 
 on the presentation generators, otherwise on standard generators.
 An SLP group on the generators and the relations as SLPs in this 
 group are returned.
} 
   require type in ["SL", "Sp", "SU", "Omega+", "Omega-", "Omega"]: "Type is not valid";
   require d gt 1: "Dimension is not valid";

   if type eq "Omega" then require IsOdd (d) and d ge 3 and IsOdd (#F): "Dimension and field size must be odd"; end if;
   if type in {"Sp", "Omega+", "Omega-"}  then require (IsEven (d) and d ge 4): 
      "Dimension must be even and at least 4"; end if;

   case type:
       when "SL": return Internal_StandardPresentationForSL (d, F: Projective := Projective, Presentation := PresentationGenerators);
       when "Sp": return Internal_StandardPresentationForSp (d, F: Projective := Projective, Presentation := PresentationGenerators);
       when "SU": return Internal_StandardPresentationForSU (d, F: Projective := Projective, Presentation := PresentationGenerators);
       when "Omega+": return Internal_StandardPresentationForOmega (d, F: Projective := Projective, Type := "Omega+", Presentation := PresentationGenerators);
       when "Omega-": return Internal_StandardPresentationForOmega (d, F: Projective := Projective, Type := "Omega-", Presentation := PresentationGenerators);
       when "Omega": return Internal_StandardPresentationForOmega (d, F: Type := "Omega", Presentation := PresentationGenerators);
   end case;
end intrinsic;
