import "sn.m": PresentationForSn;
import "sl2q.m": PresentationForSL2;
import "signed.m": SignedPermutations;

forward PlusConvertToStandard, PlusGeneratorOfCentre, PlusStandardToPresentation, 
PlusPresentationToStandard;

OmegaPlus4 := function (q: Projective := false) 
   F := SLPGroup (8);
   d := 4;

   s := F.1; s1 := F.4;
   t := F.2; t1 := F.5;
   d := F.3; d1 := F.6;
   v := F.8;

   // one of the standard generators is the identity
   rels := [F.7 = 1];

   // sl2 presentation on s, t, d
   Y, S := ClassicalStandardPresentation ("SL", 2, q);
   gens := [s, s, t, d, s^0, s^0, s^0, s^0];
   T := Evaluate (S, gens);
   rels cat:= [t = Id (F): t in T];
   // sl2 presentation on s1, t1, d1
   gens := [s1, s1, t1, d1, s1^0, s1^0, s1^0, s1^0];
   T := Evaluate (S, gens);
   rels cat:= [t = Id (F): t in T];
   for x in [s, t, d] do 
      for y in [s1, t1, d1] do
         Append (~rels, (x, y) = 1);
      end for;
   end for;
   Append (~rels, v = s1);
   Append (~rels, s^2 = s1^2);
   if Projective and IsOdd (q) then
      Append (~rels, F.3^((q - 1) div 2));
   end if;
   R := [LHS (r) * RHS (r)^-1: r in rels];
   return F, [r: r in R];
end function;

OddPlusGenerators := function (d, q)
   F := GF (q);
   MA := MatrixAlgebra (F, d);
   Z := Identity (MA);
   Z[1,1] := 0; Z[1,2] := 1;
   Z[2,1] := 1; Z[2,2] := 0;
   Z[3,4] := 1; Z[4,3] := 1;
   Z[3,3] := 0; Z[4,4] := 0;

   w := PrimitiveElement (F);
   Delta := Identity (MA);
   Delta[1,1] := w^-1; 
   Delta[2,2] := w; 
   Delta[3,3] := w^+1;
   Delta[4,4] := w^-1;
   Delta := GL(d, F)!Delta;

   E := ClassicalStandardGenerators ("Omega+", d, q);
   U := E[4]; 
   sigma := E[5];
   V := E[8]; 
   
   gens := [GL(d, q) | Delta, sigma, Z, U, V];
   return gens;
end function;

PlusGenerators := function (d, q)
   if d eq 4 then 
      return ClassicalStandardGenerators ("Omega+", d, q);
   end if;

   if IsOdd (q) then return OddPlusGenerators (d, q); end if;

   F := GF (q);
   MA := MatrixAlgebra (F, d);

   w := PrimitiveElement (F);
   delta := Identity (MA);
   delta[1,1] := w^-1; 
   delta[2,2] := w; 

   E := ClassicalStandardGenerators ("Omega+", d, q);

   sigma := E[5];
   U := E[4];
   V := E[8]; 

   Z := Identity (MA);
   Z[1,1] := 0; Z[1,2] := 1;
   Z[2,1] := 1; Z[2,2] := 0;
   Z := GL(d, q) ! Z;
   Z := Z * Z^U;
   
   gens := [GL(d, q) | delta, sigma, Z, U, V];
   return gens;
end function;

// infrastructure for OmegaPlus (2n, q) where q is even 
EvenPlus_PresentationForN1 := function (n, q)

   f, p, e := IsPrimePower (q);
   F := SLPGroup (3); 
   
   U := F.1; V := F.2; Z := F.3; 

   S, R1 := PresentationForSn (n);
   phi := hom<S-> F | U, V>;
   R1 := [phi (r): r in R1];

   R := [];
   if n gt 3 then
      Append (~R, (Z, U^(V^2)) = 1);
      Append (~R, (Z, Z^(V^2)) = 1);
   end if;

   if n gt 4 then 
      Append (~R, (Z, V * U * U^V) = 1);
   end if;

   Append (~R, (Z, Z^V) = 1);
   Append (~R, Z * Z^V = Z^(U^V));

   Append (~R, Z^2 = 1);
   Append (~R, (Z, U) = 1);

   Rels := [LHS (r) * RHS (r)^-1: r in R] cat R1;
   return F, Rels;
end function;

// infrastructure for OmegaPlus (2n, q) where q is even 
EvenPlus_PresentationForN := function (n, q)

   f, p, e := IsPrimePower (q);
   F := SLPGroup (4); 
   
   U := F.1; V := F.2; Z := F.3; delta := F.4;

   S, R1 := EvenPlus_PresentationForN1 (n, q);
   phi := hom<S-> F | U, V, Z>;
   R1 := [phi (r): r in R1];
   
   R := [];
   Append (~R, (delta, U^V) = 1);
   if n gt 3 then Append (~R, (delta, V * U) = 1); end if;
   Append (~R, (delta, delta^U) = 1);
   Append (~R, delta^(q - 1) = 1);
   Append (~R, delta^Z = delta^-1);
   Append (~R, (delta, Z^V) = 1);

   Rels := [LHS (r) * RHS (r)^-1: r in R] cat R1;
   return F, Rels;
end function;

EvenPlus_OrderN := function (n, q)
   return (2 * (q - 1))^n * Factorial (n) div 2;
end function;

// presentation for OmegaPlus (2n, q) where q is even 

EvenPlus := function (d, q)
   assert IsEven (d);
   assert IsEven (q);
   n := d div 2;
   assert n gt 2;
   
   F := GF (q);
   w := PrimitiveElement (F);
   
   f, p, e := IsPrimePower (q);

   F := SLPGroup (5);
   delta := F.1; sigma := F.2; Z := F.3; U := F.4; V := F.5; 

   if e eq 1 then 
      S, R1 := EvenPlus_PresentationForN1 (n, q);
      phi := hom<S->F | U, V, Z>;
   else 
      S, R1 := EvenPlus_PresentationForN (n, q);
      phi := hom<S->F | U, V, Z, delta>;
   end if;
   R1 := [phi (r): r in R1];
   Rels := [];

   S, R2 := PresentationForSL2 (p, e);
   if e eq 1 then 
      phi := hom<S-> F | sigma, U>;
      Append (~Rels, delta = 1); 
   else 
      Delta := delta * (delta^-1)^U;
      phi := hom<S-> F | Delta, sigma, U>;
   end if;
   R2 := [phi (r): r in R2];

   // centraliser of sigma 
   R3 := [];
   if e gt 1 then 
      Append (~R3, (sigma, delta * delta^U) = 1);
      Append (~R3, (sigma, delta^(V^2)) = 1); 
   end if;
   Append (~R3, (sigma, Z * U) = 1);
   if n gt 3 then Append (~R3, (sigma, U^(V^2)) = 1); end if;
   if n gt 4 then Append (~R3, (sigma, V * U * U^V) = 1); end if;
   if n gt 3 then Append (~R3, (sigma, Z^(V^2)) = 1); end if;

   // Steinberg relations 
   R4 := [];
   Append (~R4, (sigma, sigma^V) = sigma^(V * U)); 
   Append (~R4, (sigma, sigma^(V * U)) = 1);

   W := U^(V * U);
   Append (~R4, (sigma, sigma^W) = 1);

   if n gt 3 then 
      Append (~R4, (sigma, sigma^(V^2)) = 1);
   end if;
   Append (~R4, (sigma, sigma^(Z^V)) = 1);
   if n eq 4 then Append (~R4, (sigma, sigma^(Z^V * V^2)) = 1); end if;

   Rels := [LHS (r) * RHS (r)^-1: r in Rels cat R3 cat R4] cat R1 cat R2; 
   return F, Rels;
end function;

// infrastructure for OmegaPlus (2n, q) where q is odd 
OddPlus_PresentationForN1 := function (n, q)
   F := GF (q);
   w := PrimitiveElement (F);
   
   f, p, e := IsPrimePower (q);

   F := SLPGroup (3);
   Z := F.1; U := F.2; V := F.3;
   
   S, R := SignedPermutations (n);
   phi := hom<S-> F | U, V>;
   R := [phi (r): r in R];

   R1 := [];
   if n gt 3 then 
     Append (~R1, (Z, U^(V^2)) = 1); 
     Append (~R1, (Z, Z^(V^2)) = 1); 
   end if;
   if n gt 4 then Append (~R1, (Z, V * U * U^V) = 1); end if;
   Append (~R1, Z^2 = 1);
   Append (~R1, (Z, (U^2)^V) = 1);
   if n gt 2 then Append (~R1, Z * Z^V = Z^(V * U)); end if;
   Append (~R1, (Z, U) = 1);
   Append (~R1, (Z, Z^V) = 1);
   Rels := [LHS (r) * RHS (r)^-1: r in R1] cat R;
   return F, Rels;
end function;

OddPlus_OrderN1 := function (n)
   return 2^(2 * n - 2) * Factorial (n);
end function;

// infrastructure for OmegaPlus (2n, q) where q is odd 
OddPlus_PresentationForN := function (n, q)

   assert n gt 2;

   F := SLPGroup (4);
   Delta := F.1; Z := F.2; V := F.4; U := F.3; 

   S, R := OddPlus_PresentationForN1 (n, q);
   phi := hom<S->F | Z, U, V>;
   R := [phi (r): r in R];

   R1 := [];
   if n gt 3 then 
      Append (~R1, (Delta, U^(V^2)) = 1); 
      Append (~R1, (Delta, Z^(V^2)) = 1); 
      Append (~R1, (Delta, Delta^(V^2)) = 1); 
   end if;
   if n gt 4 then Append (~R1, (Delta, V * U * U^V) = 1); end if;

   // June 2018 change  -- replace by following 
   // Append (~R1, (Delta, Z * U) = 1);
   Append (~R1, Delta^U = Delta^-1);
   Append (~R1, (Delta, (U^2)^V) = 1);
   OMIT := true;
   if not OMIT then 
      Append (~R1, (Delta^((q - 1) div 2)) =  U^2);
   end if;

   Append (~R1, Delta * Delta^(V) = Delta^(V * U)); 

   Append (~R1, (Delta, Delta^V) = 1);
   Append (~R1, Delta^Z = Delta^-1);

   Rels := [LHS (r) * RHS (r)^-1: r in R1] cat R;
   return F, Rels;
end function;

OddPlus_OrderN := function (n, q)
   return (q - 1)^n * 2^(n - 2) * Factorial (n);
end function;

// presentation for OmegaPlus (2n, q) where q is odd 
OddPlus := function (d, q)

   assert IsEven (d);
   assert IsOdd (q);
   n := d div 2;
   assert n gt 2;
   
   F := GF (q);
   w := PrimitiveElement (F);
   
   f, p, e := IsPrimePower (q);

   F := SLPGroup (5);
   Delta := F.1; sigma := F.2; Z := F.3; V := F.5; U := F.4; 

   Rels := [];

   // additional relation needed for q = p to express Delta as word in sigma and U 
   if IsPrime (q) then 
      I := Integers ();
      b := I!(1/w);
      w := I!w;
      Append (~Rels, Delta = (sigma^U)^(w - w^2) * sigma^(b) * (sigma^U)^((w-1)) * sigma^-1);
   end if;

   if e eq 1 then 
      S, R1:= OddPlus_PresentationForN1 (n, q);
      phi := hom<S->F | Z, U, V>;
   else 
      S, R1 := OddPlus_PresentationForN (n, q);
      phi := hom<S->F | Delta, Z, U, V>;
   end if;
   R1 := [phi (r): r in R1];

   S, R2 := PresentationForSL2 (p, e);
   if e eq 1 then 
      phi := hom<S-> F | sigma, U>;
   else 
      phi := hom<S-> F | Delta, sigma, U>;
   end if;
   R2 := [phi (r): r in R2];

   // centraliser of sigma 
   R3 := [];
   if n gt 3 then Append (~R3, (sigma, U^(V^2)) = 1); end if;
   if n gt 4 then Append (~R3, (sigma, V * U^-1 * (U^-1)^V) = 1); end if;
   if n gt 3 then Append (~R3, (sigma, Z^(V^2)) = 1); end if;
   if e gt 1 then 
      if n gt 3 then Append (~R3, (sigma, Delta^(V^2)) = 1); end if;
      Append (~R3, (sigma, Delta^(Z^V)) = 1);
      if n in {3, 4} then Append (~R3, (sigma, Delta^(U^V) * Delta^V) = 1); end if; 
   end if;
   Append (~R3, (sigma, Z * U) = 1);

   // Steinberg relations 
   R4 := [];
   Append (~R4, (sigma, sigma^V) = sigma^(V * U^-1)); 
   Append (~R4, (sigma, sigma^(V * U^-1)) = 1);
   W := U^(V * U^-1);
   Append (~R4, (sigma, sigma^W) = 1);
   if n gt 3 then 
      Append (~R4, (sigma, sigma^(V^2)) = 1);
   end if;
   Append (~R4, (sigma, sigma^(Z^V)) = 1);
   if n eq 4 then Append (~R4, (sigma, sigma^(Z^V * V^2)) = 1); end if;

   Rels := [LHS (r) * RHS (r)^-1: r in Rels cat R3 cat R4] cat R1 cat R2; 
   return F, Rels;
end function;

PlusPresentation := function (d, q: Projective := false, Presentation := false)
   if d eq 4 then
      return OmegaPlus4 (q: Projective := Projective);
   elif IsEven (q) then 
      P, R := EvenPlus (d, q);
   else
      P, R := OddPlus (d, q);
   end if;

   n := d div 2;   
   if Projective and q^n mod 4 eq 1 then
      z := PlusGeneratorOfCentre (d, q, P);
      R cat:= [z];
   end if;
   if Presentation then return P, R; end if;

   S, Rels := PlusConvertToStandard (d, q, R);
   Rels := [w : w in Rels | w ne w^0];
   return S, Rels;
end function;

/* relations are on presentation generators;
   convert to relations on standard generators */

PlusConvertToStandard := function (d, q, Rels)
   A := PlusStandardToPresentation (d, q);
   Rels := Evaluate (Rels, A);
   B := PlusPresentationToStandard (d, q);
   C := Evaluate (B, A);
   U := Universe (C);
   W := Universe (Rels);
   tau := hom <U -> W | [W.i:i in [1..Ngens (W)]]>;
   T := [W.i^-1 * tau (C[i]): i in [1..Ngens (W)]];
   Rels cat:= T;
   return W, Rels;
end function;

/* express presentation generators as words in standard generators */ 

PlusStandardToPresentation := function (d, q)
   assert IsEven (d) and d gt 4;
   F := SLPGroup(8);
   s := F.1; s1 := F.4;
   t := F.2; delta := F.3; 
   t1 := F.5; delta1 := F.6;
   u := F.7; v := F.8;
   // return presentation generators = [delta, sigma, Z, U, V]
   if IsOdd (q) then 
      return [delta1^-1, t1, s * s1, s1, v];
   else 
      return [(delta * delta1)^((q - 2) div 2), t1, s * s1, s1, v];
   end if;
end function;

/* express standard generators as words in presentation generators */ 

PlusPresentationToStandard := function (d, q)
   assert IsEven (d) and d gt 4;
   W := SLPGroup(5);
   delta := W.1; sigma := W.2; Z := W.3; U := W.4; V := W.5;
   w1 := IsEven (q) select Z * U else Z * U^-1;
   w3 := IsEven (q) select delta^-1 * (delta^-1)^U else delta^(Z^(V^-1));
   w6 := IsEven (q) select (delta * (delta^Z)^U)^-1 else delta^-1;
   // return standard generators = [s, t, delta, s', t', delta', u, v] 
   return [w1, (sigma^-1)^(Z^V), w3, W.4, W.2, w6, W.0, W.5];
end function;

// generator of centre as word in presentation generators

PlusGeneratorOfCentre := function (d, q, F)
   assert IsEven (d) and d gt 2;
   n := d div 2;
   if q^n mod 4 eq 1 then 
      Delta := F.1; Z := F.3; V := F.5; 
      if IsEven (n) then
         z := V^n;
      else 
         z := (V * Z * Delta)^(n * (q - 1) div 4);
      end if;
   else 
      z := F.0;
   end if;
   return z;
end function;
