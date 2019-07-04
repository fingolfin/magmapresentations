forward SpStandardToPresentation, SpPresentationToStandard, SpConvertToStandard;

import "sn.m": PresentationForSn;
import "sl2q.m": PresentationForSL2;

SpGenerators := function (d, q)
   S := ClassicalStandardGenerators ("Sp", d, q);
   Z := S[1];
   V := S[2];
   tau := S[3];
   delta := S[4];
   U := S[5];
   sigma := S[6]; sigma := ((sigma^(V^2))^(Z^-1));
   return [Z, V, tau, delta^-1, U, sigma];
end function;

Sp_PresentationForN1 := function (n, q)

   F := SLPGroup (3);

   U := F.1; V := F.2; Z := F.3; 

   S, R1 := PresentationForSn (n);
   phi := hom<S-> F | U, V>;

   Rels := [phi (r): r in R1];
   OMIT := true;
   if not OMIT then 
      m := IsOdd (q) select 4 else 2;
      Append (~Rels, Z^m);
   end if;
   if n gt 2 then Append (~Rels, (Z, U^V)); end if;
   if n gt 3 then Append (~Rels, (Z, V * U)); end if;
   Append (~Rels, (Z, Z^U));

   return F, Rels;
end function;

Order_Sp_N1 := function (n, q)
   if IsEven (q) then return 2^n * Factorial (n);
   else return 4^n * Factorial (n); end if;
end function;

// presentation for D_{2(q-1)} wr Sym (n) for q even or Q_{2(q-1)} wr Sym (n) for q odd 

Sp_PresentationForN := function (n, q)

   f, p, e := IsPrimePower (q);
   F := SLPGroup (4);
   
   U := F.1; V := F.2; Z := F.3; delta := F.4;

   S, R1 := Sp_PresentationForN1 (n, q);
   phi := hom<S-> F | U, V, Z>;
   R1 := [phi (r): r in R1];

   Rels := [];

   OMIT := true;
   if not OMIT then 
      if IsEven (q) then 
         Append (~Rels, delta^(q - 1) = 1);
      else 
         Append (~Rels, Z^2 = delta^((q - 1) div 2)); 
      end if;
      Append (~Rels, delta^Z = delta^-1);
   end if;

   if n gt 2 then 
      Append (~Rels, (delta, U^V) = 1); 
   end if;
   
   if n gt 3 then 
      Append (~Rels, (delta, V * U) = 1); 
   end if;
   Append (~Rels, (Z, delta^U) = 1);  
   Append (~Rels, (delta, delta^U) = 1);  
   Rels := [LHS (r) * RHS (r)^-1: r in Rels] cat R1; 

   return F, Rels;
end function;

Order_Sp_N := function (n, q)
   return (2 * (q - 1))^n * Factorial (n);
end function;
   
SpPresentation := function (d, q)
   assert IsPrimePower (q);
   assert d gt 2;
   assert IsEven (d);
   n := d div 2;

   f, p, e := IsPrimePower (q);

   F := SLPGroup (6);
   Z := F.1; V := F.2; tau := F.3; delta := F.4; U := F.5; sigma := F.6; 

   // we don't need delta if e = 1 but it makes presentation consistent for all q 
   Rels := [];
   if e eq 1 then
      w := PrimitiveElement (GF(p));
      I := Integers ();
      a := I!(w - w^2);
      b := I!(w - 1);
      wm1 := I!(w^-1);
      Append (~Rels, delta = (tau^a)^Z * tau^(wm1) * (tau^b)^Z * tau^-1);
   end if;

   // presentation for D_{2(q-1)} wr Sym (n) for q even or Q_{2(q-1)} wr Sym (n) for q odd 
   if e eq 1 then 
      S, R1 := Sp_PresentationForN1 (n, q);
      phi := hom<S->F | U, V, Z>;
   else 
      S, R1 := Sp_PresentationForN (n, q);
      phi := hom<S->F | U, V, Z, delta>;
   end if;
   R1 := [phi (r): r in R1];

   // centraliser of tau 
   Append (~Rels, (tau, Z^U) = 1);
   if n gt 2 then 
      Append (~Rels, (tau, U^V) = 1);
   end if;
   if n gt 3 and IsEven (q) then 
      Append (~Rels, (tau, V * U) = 1);
   end if;
   if IsOdd (q) then 
      Append (~Rels, (tau, Z^2) = 1);
   end if;
   if e gt 1 then Append (~Rels, (tau, delta^U) = 1); end if;

   // centraliser of sigma 
   Append (~Rels, (sigma, Z * U * Z^-1) = 1);
   if n gt 2 then 
      Append (~Rels, (sigma, Z^(V^2)) = 1);
      if e gt 1 then Append (~Rels, (sigma, delta^(V^2)) = 1); end if;
   end if;
   if n gt 3 then
      Append (~Rels, (sigma, U^(V^2)) = 1);
   end if;
   if n gt 4 then
      Append (~Rels, (sigma, V * U * U^V) = 1);
   end if;
   if IsOdd (q) and e eq 1 then Append (~Rels, (sigma, (Z^2, U)) = 1); end if;
   if e gt 1 then Append (~Rels, (sigma, delta * delta^V) = 1); end if;

   // presentation for SL(2, q) on <delta, tau, Z>
   S, R2 := PresentationForSL2 (p, e);
   if e eq 1 then 
      phi := hom<S-> F | tau, Z>;
   else 
      phi := hom<S-> F | delta, tau, Z>;
   end if;
   R2 := [phi (r): r in R2];

   // presentation for SL(2, q) on <Delta, sigma, W>
   W := IsEven (q) select U else U * Z^2;
   S, R3 := PresentationForSL2 (p, e);
   if e eq 1 then 
      phi := hom<S-> F | sigma, W>;
   else 
      Delta := (U, delta);
      phi := hom<S-> F | Delta, sigma, W>;
   end if;
   R3 := [phi (r): r in R3];

   // Steinberg relations 
   if n gt 2 then 
      Append (~Rels, (sigma, sigma^V) = sigma^(V * U)); 
      Append (~Rels, (sigma, sigma^(V * U)) = 1);
      Append (~Rels, (sigma, sigma^(U * V)) = 1);
   end if;
   if n gt 3 then 
      Append (~Rels, (sigma, sigma^(V^2)) = 1);
   end if;

   if IsOdd (q) then 
      Append (~Rels, (sigma, sigma^Z) = (tau^2)^(Z * U));
   else 
      Append (~Rels, (sigma, sigma^Z) = 1);
   end if;

   Append (~Rels, (sigma, tau) = 1);
   Append (~Rels, (sigma, tau^U) = sigma^(Z^U) * tau^-1);
   if n gt 2 then Append (~Rels, (sigma, tau^(V^2)) = 1); end if;

   Append (~Rels, (tau, tau^U) = 1);

   Rels := [LHS (r) * RHS (r)^-1: r in Rels] cat R1 cat R2 cat R3;
   return F, Rels;
end function;

/////////////////////////////////////////////////////////////////////////
//   standard presentation for Sp(d, q)                                //
//                                                                     //
//   Input two parameters to compute this presentation of Sp(d, q)     //
//     d = dimension                                                   //
//     q = field order                                                 //
//                                                                     //
//   July 2018                                                         //
/////////////////////////////////////////////////////////////////////////

intrinsic Internal_StandardPresentationForSp (d:: RngIntElt, q :: RngIntElt :
      Presentation := false, Projective := false) -> GrpSLP, [] 
{return standard presentation for Sp (d, q); if Projective is true, 
 then return presentation for PSp (n, q) }
  
   require d gt 2 and IsEven (d): "Degree must be at least 4 and even";
   require IsPrimePower (q): "Field size is not valid";
   return Internal_StandardPresentationForSp(d, GF(q) : Presentation := Presentation, Projective := Projective);
end intrinsic;

intrinsic Internal_StandardPresentationForSp (d:: RngIntElt, K :: FldFin :
      Presentation := false, Projective := false) -> GrpSLP, [] 
{return standard presentation for Sp(n, K); if Projective is true, 
 then return presentation for PSp(n, K)}
  
   require d gt 2 and IsEven (d): "Degree must be at least 4 and even";

   q := #K;
   
   P, R := SpPresentation (d, q);

   // add relation for PSp (d, q) 
   if IsOdd (q) and Projective then 
      Z := P.1; V := P.2;
      Append (~R, (Z * V)^d);
   end if;

   if Presentation then return P, R; end if;

   S, Rels := SpConvertToStandard (d div 2, q, R);
   Rels := [w : w in Rels | w ne w^0];
   return S, Rels;
end intrinsic;

/* relations are on presentation generators;
   convert to relations on standard generators */

SpConvertToStandard := function (d, q, Rels)
   A := SpStandardToPresentation (d, q);
   Rels := Evaluate (Rels, A);
   B := SpPresentationToStandard (d, q);
   C := Evaluate (B, A);
   U := Universe (C);
   W := Universe (Rels);
   tau := hom <U -> W | [W.i:i in [1..Ngens (W)]]>;
   T := [W.i^-1 * tau (C[i]): i in [1..Ngens (W)]];
   Rels cat:= T;
   return W, Rels;
end function;

/* express presentation generators as words in standard generators */ 

function SpStandardToPresentation(d, q)
    W := SLPGroup(6);
    // sequence [Z, V, tau, delta, U, sigma] 
    return [W.1, W.2, W.3, W.4^-1, W.5, (W.6^(W.2^2))^(W.1^-1)];
end function;

/* express standard generators as words in presentation generators */ 

function SpPresentationToStandard(d, q)
    W := SLPGroup(6);
    // [s, V, t, delta, U, x] 
    return [W.1, W.2, W.3, W.4^-1, W.5, (W.6^W.1)^(W.2^-2)];
end function;
