forward SLConvertToStandard, SLPresentationToStandard, 
        SLStandardToPresentation, SLGeneratorOfCentre;

import "sn.m": PresentationForSn;
import "sl2q.m": PresentationForSL2, SL2Generators;
import "signed.m": SignedPermutations;

SLGenerators := function (d, q)
   if d eq 2 then 
      f, p, e := IsPrimePower (q); return SL2Generators (p, e); 
   end if;
   S := ClassicalStandardGenerators ("SL", d, q);
   MA := MatrixAlgebra (GF(q), d);
   V := Zero (MA);
   for i in [1..d - 1] do V[i, i + 1] := 1; end for;
   V[d,1] := (-1)^(d - 1);
   S[2] := V;
   S[4] := S[4]^-1;
   return S;
end function;

// presentation for extension of direct product of 
// d - 1 copies of Z_{q - 1} by a copy of Sym (d) 

PresentationForN := function (d, q)
   F := SLPGroup (3);
   U := F.1; V := F.2; delta := F.3;

   if IsEven (q) then 
      S, R := PresentationForSn (d);
   else 
      S, R := SignedPermutations (d);
   end if;
   tau := hom<S-> F | U, V>;
   R := [tau (r): r in R];

   Rels := [];

   if d gt 3 then 
      Append (~Rels, (delta, U^(V^2)) = 1);
   end if;
   if d gt 4 then 
      Append (~Rels, (delta, V * U * U^V) = 1);
   end if;

   Append (~Rels, delta * delta^V = delta^(V * U));
   Append (~Rels, (delta, delta^V) = 1);
   if d gt 3 then Append (~Rels, (delta, delta^(V^2)) = 1); end if;

   OMIT := true;
   if not OMIT then 
      Append (~Rels, delta^U = delta^-1);
      if IsEven (q) then 
         Append (~Rels, delta^(q - 1) = 1);
      else 
         Append (~Rels, delta^((q - 1) div 2) = U^2);
      end if;
   end if;

   Rels := [LHS (r) * RHS (r)^-1: r in Rels] cat R;
   return F, Rels;
end function;

SL_Order_NSubgroup := function (d, q)
   return (q - 1)^(d - 1) * Factorial (d);
end function;

// return presentation for SL(d, q) 

SLPresentation := function (d, q)
   assert d gt 2;
   f, p, e := IsPrimePower (q);

   F := SLPGroup (4);
   U := F.1; V := F.2; tau := F.3; delta := F.4;

   Rels := [];
   // we don't need delta if e = 1 but it makes presentation consistent for all q 
   if e eq 1 then
      w := PrimitiveElement (GF(p));
      I := Integers ();
      a := I!(w - w^2);
      b := I!(w - 1);
      wm1 := I!(w^-1);
      Append (~Rels, delta = (tau^a)^U * tau^(wm1) * (tau^b)^U * tau^-1);
   end if;

   if IsPrime (q) then 
      if q eq 2 then
         S, R1 := PresentationForSn (d);
      else 
         S, R1 := SignedPermutations (d);
      end if;
      phi := hom<S-> F | U, V>;
   else 
      S, R1 := PresentationForN (d, q);
      phi := hom<S-> F | U, V, delta>;
   end if;
   R1 := [phi (r): r in R1];
   
   S, R2 := PresentationForSL2 (p, e);
   if e eq 1 then 
      phi := hom<S-> F | tau, U>;
   else 
      phi := hom<S-> F | delta, tau, U>;
   end if;
   R2 := [phi (r): r in R2];
    
   // centraliser of tau 
   if d gt 3 then 
      Append (~Rels, (tau, U^(V^2)) = 1);
   end if;
   if d gt 4 then 
      if e gt 1 then 
         Append (~Rels, (tau, V * U * U^V) = 1);
      else
         Append (~Rels, (tau, V * U^-1 * (U^-1)^V) = 1);
      end if;
   end if;
   if e gt 1 then 
      Append (~Rels, (tau, delta * (delta^2)^V) = 1);
      if d gt 3 then 
         Append (~Rels, (tau, delta^(V^2)) = 1);
      end if;
   end if;

   // Steinberg relations 
   Append (~Rels, (tau, tau^V) = tau^(U^V));
   Append (~Rels, (tau, tau^(U^V)) = 1);
   Append (~Rels, (tau, tau^(U * V)) = 1);
   if d gt 3 then 
      Append (~Rels, (tau, tau^(V^2)) = 1);
   end if;

   // one additional relation needed for this special case 
   if d eq 3 and q eq 4 then 
      Append (~Rels, (tau, tau^(delta * V)) = tau^(delta * U^V));
      // Append (~Rels, (tau, tau^(delta * U^V)) = 1);
      // Append (~Rels, (tau, tau^(delta * U * V)) = 1);
   end if;

   Rels := [LHS (r) * RHS (r)^-1: r in Rels] cat R1 cat R2;
   return F, Rels;
end function;

/////////////////////////////////////////////////////////////////////////
//   Short presentation for SL(d, q)                                   //
//                                                                     //
//   Input two parameters to compute this presentation of SL(d, q)     //
//     d = dimension                                                   //
//     q = field order                                                 //
// 
//   November 2017 
/////////////////////////////////////////////////////////////////////////

intrinsic Internal_StandardPresentationForSL (d :: RngIntElt, q :: RngIntElt: 
       Presentation := false, Projective := false) -> GrpSLP, []
{return standard presentation for SL(d, q); if projective, then
 return standard presentation for PSL(d, q)}
  
   require d gt 1: "Degree must be at least 2";
   require IsPrimePower (q): "Field size is not valid";
   return Internal_StandardPresentationForSL(d, GF(q): Presentation := Presentation, Projective := Projective);
end intrinsic;
 
intrinsic Internal_StandardPresentationForSL (d :: RngIntElt, K :: FldFin: 
       Presentation := false, Projective := false) -> GrpSLP, []
{return standard presentation for SL(d, K); if projective, then
 return standard presentation for PSL(d, K)}
  
   require d gt 1: "Degree must be at least 2";

   q := #K;
   p := Characteristic (K); 
   e := Degree (K);    

   if d eq 2 then 
      P, R := PresentationForSL2 (p, e: Projective := Projective);
   else 
      P, R := SLPresentation (d, q);
      if Projective and Gcd (d, q - 1) gt 1 then
         z := SLGeneratorOfCentre (d, q, P);
         R cat:= [z];
      end if;
   end if;

   if Presentation then return P, R; end if;

   S, Rels := SLConvertToStandard (d, q, R);
   Rels := [w : w in Rels | w ne w^0];
  
   return S, Rels;
end intrinsic;

/* relations are on presentation generators; 
   convert to relations on 4 standard generators */

SLConvertToStandard := function (d, q, Rels) 
   A := SLStandardToPresentation (d, q);
   Rels := Evaluate (Rels, A);
   B := SLPresentationToStandard (d, q);
   C := Evaluate (B, A);
   U := Universe (C);
   W := Universe (Rels);
   tau := hom <U -> W | [W.i:i in [1..Ngens (W)]]>;
   T := [W.i^-1 * tau (C[i]): i in [1..Ngens (W)]];
   Rels cat:= T;
   return W, Rels;
end function;

/* express presentation generators as words in standard generators */
   
SLStandardToPresentation := function (d, q)
   S := SLPGroup (4);
   if d eq 2 then
      if IsPrime (q) then
         P := [S.3, S.2, S.0, S.0];
      else
         P := [S.4^-1, S.3, S.2, S.0];
      end if;
      return P;
   end if;
   
   U := S.1; V := S.2; tau := S.3; delta := S.4;

   if IsOdd (d) and IsOdd (q) then 
      V_p := V^-1 * (U^-1 * V)^(d - 1); 
   else 
      V_p := V^(d - 1);
   end if;
       
   return [U, V_p, tau, delta^-1];
end function;

/* express standard generators as words in presentation generators */

SLPresentationToStandard := function (d, q)
   if d eq 2 then
      if IsPrime (q) then
         P := SLPGroup (2);
         w := PrimitiveElement (GF(q));
         I := Integers ();
         x := I!(w^-1) - 1;
         y := I!(w^-2 - w^-1);
         U := P.2; tau := P.1; 
         delta := (tau^-1 * (tau^x)^U * tau^(I!w) * (tau^-y)^U)^-1;
         S := [P.2, P.2, P.1, delta];
      else
         P := SLPGroup (3);
         S := [P.3, P.3, P.2, P.1^-1];
      end if;
      return S;
   end if;

   P := SLPGroup (4);
   U := P.1; V := P.2; tau := P.3; delta := P.4;

   if IsOdd (d) and IsOdd (q) then 
      V_s := (V * U^-1)^(d - 1) * V^-1;
   else 
      V_s := V^(d - 1);
   end if; 
   
   return [U, V_s, tau, delta^-1];
end function;

// construct generator of centre as SLP in presentation generators 

SLGeneratorOfCentre := function (d, q, W)
   assert d gt 2;
   m := (d - 1) * (q - 1) div Gcd (d, q - 1);
   U := W.1; V := W.2; delta := W.4; 
   z := (delta * U * V^-1)^m; 
   return z;
end function;
